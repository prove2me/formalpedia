-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4371
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:24:25.211987+00:00
-- url     : https://prove2.me/submissions/a0dc5b1b-2000-4d6e-86c3-ed18d0636c13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 785971223 ≤ n < 786151079 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 785972473 1250 785971223 785971229
    0xb03100509131203050c07050105010b071704150c0809040c08090601270903090302151c0c1b060b040f02190c03050301060320030702030306090907060c0209040602040f0609 76
    0xd915000e000a040080b0b40c2000c6160503000a00e04000d4814140114001c01c1c004048440e200014810700011900910496002e000c00d0007156039100003506210604442207031b480c1c105070704204028022610b44d080514200d800d2400c200c02c1941440c40d01c90351340e0003000c62054010b450080d4000c5070561042e00785002d00401e600f03942030b503601c40700404c0140c6221051003403c510714500366520300c00c150380048100d90091a100c1d4010380c80342c0c0012200034005007a8a0514008141100c071880d41c07003288080d003031101d0410401000e8011024001900f040c12281c408018071400c03100b0300c6035135000941c85d82c600410820050904e03d0704000203402c5045050007418004096107103082c000c210f150182034047d25910300b503078644007003200505240d07900300d01011400c0781c5081d0103a511402441c0280320b03079005940c592520b10103120303400c08010400403017548480c008000c00307500300020030445901524051950f0351141000d138081d01c244e1b40110141000594002141c580c01034030714080e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 785973723 1250 785972473 785972479
    0x120705181b0d021801050306031e12040b192a060609020a0f080105042a09050d080a0e0910140f030a03020d14070206160302100903210e1b06040b031005 67
    0x5a507490b1001146d16010889019415a000143c04a09480c80c040c80c01c4400f1640c800700d134816021402c0140c82c03504154080b018842004c41e5040c1001b80d02e902641c03001c0e1a42c5402e440c40406070703201035000344024944990900c018585282400540e41246d0301900450ba415541c55108050007010400e0300042e110000310000c00110302071500f4003800d13200c01c07107014000c052001c002e1070f001e2401401030540e03400d0142503440000d4035100c2e42400d954140c050b060071a165001d450f000781140541400c4188503080d0754080042c203060700d8800d0816900c0c160380380130f40e5182420115450328804644075515106040050040640c0015120810022a41c2e10b080300120610b8116150240c01c41c000e611641c00c1c0001508503040600300308170300c0c1c0a403040300c4807202400000ca04035040c8000c113500003007084520310341030a050162a0190094500101301d600c0d42c0a07062912a84c03803203074942d40c050456110b8000d40c2d8820f000e85000d0040d000443c2d0392410302c004400d6450929125480c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 785974973 1250 785973723 785973757
    0x6190f05030f120d0c120903170c1e0307020c1305090d0503010303020307021003110d050f15010207090507090b03010602071a040303050a0c0c090e030306120705181b0d02 75
    0x241d00080882d0b0803005540240183c0c0c00c044032865854050400e280b202010041c04c40b038602ca000800d4014181014001d4442400c4684c1c072030304c100851300004000c4d1010003c20003510317901f010324904094020b1510706020b612511550412410440d04921596100c00302080c100e448880a034011400b480248049840c3c4510031a4250b032180001d10001c0e016070018003070300740075017008140e0916074150761400095030007100b010324600d508000310803251150f44200f00b0100745d141e60889900b01030303045410359203c100c410000356228030f6030040e1075660f5100d001181c0c0d00d0b4007890a59016142007203920b512503841e2400290741d00a0380c80ad454402860714454007140200318115000ea070b80540d00c0030f15000c0c0182c0141c61031202040c1c1190a425445070000e0440c0c400c2c403c0c075042c060f0007805159070313040c4401001003040800341c420501d038006140820680c0c2d06c400751800b10002160800320b240e6245000c1c5a40e00d107e4078030049141d500080d944030401d00d42d60061000d80c44201d03100d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 785976223 1250 785974973 785974993
    0x7180b100905061e27010e01051303020609240304050c0603060904031b1202010e010f060f12030c061a09130302060604020706091a22050c01030506190f0503 69
    0x8414022078072580380c0003c1c00304000550f07a140d10708165500d6806a105030310703005480a01c1c40139810103840c10310115281a1000c8219a8040130050040301c00b460507604050056054405445007444002d10511740081d6845540e159400f01c0d00190300030400914400c240031004110302d900459041703075140a075002d000f04c149418000c0c0da00460014081c480c0c030b0b82d6241e500707488481c0681c51212910840d82d1000000403915200562a8900c5e6030011480454181086080d42c00f01d000c2d400c0800e041c01c00c01d00681d80f42c0e0b0034110071141000c10200e041784403400d0580301d48404007405410b541c142650ba000b60340d000348040b4a221825513905100e540c5a48659100900858000700141c201c44003240d036611701034003d84031180c0903100c0001c0020720b6980d09242000c21a000303402041000303040103e000b4114119034503611007034040070000015039684a450b000580c0000f03040c0759448001c2201c5803115030f5182500f4400d40200c8070b03d1500c1700320784086140288112131092141e64040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 785977473 1250 785976223 785976227
    0xb0301030209070f1715220605040209130c1404150801090b0d0605150d1b051210020f0c010203070918020a140307140a0906140a1d0307180b10 63
    0x1c40d01000315580c034a05e000700b400d0034403240442e01501c80d40c9005450075240065070380e011148003030413002082c521080b01c400d94800f025640c1540c04a032281d481444250916180d00131420b449142005001a80705080300c0182e4450101c200754001c605008039005c40d02d07080408038000b8480d1306485082880e0784c0c5030744442c181e0711080d02841e000003c8000e0800022207076005581c120b414140c20200790780800300414003c901c0d110064400f40741d8004502a001600030000c1c0281c0300a81c1d90b5900000317296500c95560114240303601c501e6600144600329031102405540c8036a0004000b95500d050020004007010710038042d2000301d40801564140e0603085100f182c5050340c6649611740350b02407402541c006c680008102105100207282c800e14060016401402c841105444001f103050400000820410707820300b4110b0006010040070301d083d42c0220002c0d2a521700c0304050501224002c012a04107825580004100340030314009003001c2000c0e40105003540b200b0755642c50600f4405e141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 785978723 1250 785977473 785977487
    0xc051204120b06011e0c0b0603070b070b090a2907210b03010e06160215040b0105060a0306080d0309060e010501060c020d0c0302031207021008010f061809060b030103020907 76
    0x50051180003070700c180c0002940c0b0046180d00010505089851010f640040d803080803100303030b203130303002a4805c10710342c04000c2c0400d85580c1003501903001303288890805200600c603108182e00501042c5c4030000156008008001c4020003075845800c11b00c0444a1904501c3c10000d9510501d80d9441d0744800280d00070710900745a4400441d01c40c0ca0b2510a0080c1d030510018551294004e400d95203034503490419100801081d80150034108241a00015100000341014850040309400260000500c0003040444407102c0c107640040f12101d0740e8030000142a002403e40c3e0344803002e40c0c0a03204a0040c240d802d54086004035014450910450400310313a050300301d4209000d0703180811485034a040160804501c94481c8520805000c0b8030107031079130000307490400040412464840005400b0045042c2104c2c400c0b2044050305004c0d80a504100342030800141a0298408001d0040b18071880004486800801040c0301101045203640740c200903481035200340401e900495500010458261117640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 785979973 1250 785978723 785978729
    0x303051e0606160602041d0717041115090901030c060e0105120f04030c241103041112010617030c010b060f07020603060a32030a0b04020405100f060c051204 69
    0x802403602005003003010007401100f009940844d030a110108074007000554144c0e00d049960f00710704180c50120070003040c02410441880341010f0a0040c0300c00100034401d44070443d002254010b00104400c81c10b51124040c0404496004450a0002050064001c0682c0c20b559942d5112070b804402c68005458500c101d001c680100d26a44002540040b40b03001410b8201e4440e02e001c0c40b186e081900c403040c10320016100c0790340108520264021081287c41008016119440407505510300b94071844044d03441e50000a004421917090707204030036000e5201c8400390071940400b900321070b114826243c1e69003101c10401295841c104151520740341c040203030f801403500d031040d0310324200459007844860380024051035000407031340c40003184200d25071401c00100c0400b64150302600c6411081000c0300c02719100001e000381c1001030058042803181441d50b503c01e07010b4a001c0b86030f1300c031000c0f41101d03c507c03540150441101c00d9030104240d948504540401c60142e000c94040240415410905d446144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 785981223 1250 785979973 785979979
    0xb010501111f0c0221030f07031103180f03160b0c0f0d0b010e0a0e07230409180f14100b1c0c03021c1401140f0a0603020d0303051e06 59
    0x11002c2404501c094008040c908024030540c2c038030040310728a0700c0480700219040b0358594004020409008a11a01681d00c038806103018460030144500b400d4861002a00550180c0f00361030180190100030490b0f21201e401e4141103d41d500c080f10300e41c40910300d6029045814900c0b60000c6a040c1034040b050343d00001c0c01c000d5040c40c05160480681c020840c0100b00d81c10f01500c40b200c1080307542c5185200700107082c02e21445c2c00c00c0c034002c0c100038030f034480c0c500101d45103400742c10002d00c1070100803040e601a00d034084800074410b08542c108102d0803c0400e80141102c80102d102801c0181207840e0040d101c486100302d0301c0c40d1040e60551810348500d072a41c1070300728202d50b100004c1d50307082190100b6840c0c0200ba1399441e06440ea004121440070072980c5c42900380055010808010044c00300350307560102032000702301e0a5103404504040c0c0c039000c4c01131807404128401054645030a94065002550f004200816000c610b01c1e0140140404850301d0144a02807956030b0550300c00c2883c5140308400003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 785982473 1250 785981223 785981263
    0x14040e0c0108100b0d06240f0f0309050102031e18060601080403180602030408070608060f04150909120906080405060414070e0c09040b030a11040b040207020301090b01050111 77
    0x1200c01103680c0ea100805403059140e4028000828038420401401444400301020032124140801c1c01d05610b190314620240c1d00c401410045150750007410750008846624004403e0404e9820880c003034001c401016102d54800414042103540d44030b040d00749200591420701482e6980d91000080c090020b000c201240c110704005401c56200c0c140c15940300e0f11908054181501c42e04070707002c926015420010141c2c0c80010140103001d000c0004000502140ca00322026141c1500440c000c2c05401048600440d06d40744198a40c41c2c00640c5400a803003002c0040211713200c030f4104500300188040c6181c01150540c3e201080b0244030b003011520503500000100b8040c1ca0700c0e078071402d401507046418580d601840c58045030070076060508070302078229090900e456401c1e1b2010082103882544000c0e1107035121000050015131007007043c0d150703100c0803100010b0200706200810082e1050b030f040203615510708002002005521104c10b0306884003a60391607010000d6a035029514100b454880c00c8140032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 785983723 1250 785982473 785982493
    0xe0f1b03152406070813030519050309090702030705061018050610121803090e01080c3d1106150f0402031b0c071a030c0403080a0905120714040e 64
    0x42c0d400940460100070b46402e25003000303038449a8203034202c640d603002016100e48081003804010801c2d1a000700055495040c00283d50340c40556070310407110828060030741d0100007801a4024401e40c4c02590300442958060f1800071a40c90184409002d50300810b003007a00350390b24500183c4200340c03082ca00500100420183d015040da00c504402403005581512a54441041c0d1100000401c1d032901c40d13143c1040e03460030316550341c210100517000040d0035032003030040c00309a5580c0c03201c09081074034000070121200d000c1c0000e4405115205448030301042c050807406001130307110980803180340d02a01a1031721500c5403841c200f004000784102990100040307010301003520b800c0d801180c00181001d07184000c801100c1c445050303500074503900000b0343c1013001d0030001031401c5030380040c24819050000d0f00e1071034403002c0c081c1140503500010b4481c81021608000240c0203d00480c003411000303204030391034058104602c1d55040d0501542c00f10f03021000b4482d11a041c140902d80b0a1038820000d020070b40c0e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 785984973 1250 785983723 785983771
    0x5121c090f080702121c110f1e01140c0c0f010c0e010e061c240326090316060306051912020d1707020f0d0c0303030e0f1b0315 56
    0x561007640c3c44144402c61701044141080005009499951500090f5400c8a8007802c0e03007a11410390342c0c01c1c2d0401100882407480100b4005c10809142440040300d000f000c01e014010a0548690744406c24110144103461074188050590403503001e0440c0c000f41a80841e5030300745c034002c8400300c0204601c01c184480e00d6024800d03001c9440c0d8007500241c20a80d409284403c6001d5107000c4090843c0d84141038240d85840c00d494000c42101840550081c1e80b950341c07001000d10145244241c0300b500aa8402c824040300004c4900d05040281100c0c0b039542000c1030303042c01f112640b24450109141c000d00203243c0c28501e181d10700c5040a245001c04940c508280c0c03a12001c4244801c9078072030784070742540002855205a202810107800e00e030300c0e1250140d106010301e03100303200002441807101c09070490003d610120b0320010f4070341c9440e010452008202c104c9141080145c220340880c080c1c40e0b5010380901044865401c6a1000c504030381580700070104000c0b13500001d494080ca03128003151042c101103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 785986223 1250 785984973 785984977
    0x6040506030a02040f0603170a14090f040510260c040b120a1b050a1214010e030a02030711040603150e120c0105070906050918060d05121c090f08 64
    0x24002605032200c42c0d0b16580040e08031390944802120040d03a912040c024022200c28141802c090b9440552504044c5540a41102421900109000000904001030391500c0071000800f0602900a001909110700701010441850281240c0c4402440d1605000281810040c8a0442d03583c00351460104010602015000c0e4409941c0c201c0c02c00a07030340d038111204102c4490514041d0f40624800180c040307000d14074200c15403200303214000f207003001d000807010321207144a420b0303000040d00100d0050031030407130141030395510800740340c000481c903c8610303900030000f031402c1407184560050b0f104078a030400003225081d000280101c48841001140f00e1501d42c01101e1100c1c052040300c0403550704010145456200b03240e2034a80741d45510900000a400007055809000241462402d2605e140b0105007504050800300c508621110082200350701e074031404581854101054500b10207850700b40c00c1d00d40e404400c40b880f40c40001c4081d14511101845101d10042e40310380e8030200c40030581c0f03072001d82d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 785987473 1250 785986223 785986231
    0x30e010b0d1401090b0108100b010f090b03100f0909060e160e090715050d0f0605061c0f0c050703170103121409030f01052a0a111f140c0c06060405 65
    0x140d941c0d10741420105e01c0480082e0700810488000b408e591000141c02d000340c5001c480400c0c10b21030360001450007590056600300c144d07400b48101a0b02da96550301451038405055000e80b4111034000300210303048c100f1390401d42305c00d4000c1e903082c00301c407a0002c80d841c4e980d0240c0f00c10415281c0e4600c81400b111024000558205420200326144142c40392000100300e16041003603008264009690307144044140142a0188075404040244c1890003021801c984105482c01d500d40c2410300d40800910500d6006000344800c001040003404090b0401604503440391300190007044481902c24182c1d21485403040c10b8903800216000c90744440581174a0203004204913030744003402071000e5403103510200300b9800107079840d8002054900305801c00210381010008079003039000d03003080c100305104805000c550302c007401450aa50303007407004410b5608010f00b102c1d08408083c0140760640311101d6681160b2104403904034121284d07198402804c203248104030320b800c41170304403030b000038030503c0c0943c085580 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 785988723 1250 785987473 785987513
    0x30a08090316060f1101020a140a170f18030307050a120b0607150c020a020612060d0c09020306041103221b080708060114030303040b06040f1a01030e010b0d 69
    0x4039015210b10b0707030b1842d00c998020a000401c0d0500041c0400e600140d400480e00454000314a40280304c080104070b000b010304000d00d985000a40c10200e10312500000030358801c0b80c042e5208508244071203091502d010b545002440389004001c688890003c0200c178043e01d115102d552400f01c4940d0280d0f0f100403580c500150042d50344484040b242c0321034005140c1c0b031b441404e4444203204c10395400421101e0b0366a031003007154040584e140040c1c59100c215090740074440312100480e61500d0003d80d440c03100090041070f24807400b0b00042d8141c065005180034004c01c803001c0c0722a02600c0300c812100d0004650b01c0c1409000311200d440e2040300e51440380031f2140a60006501240d0301051003420141942c0131034090382c4445000c0043c03520500025001d05010840e1604654000c40041d50702d000240c00a4400016000030403038580d2a54002c44142041d84410700510603100341103500542850410340c046400c000308407104a01c10301c5050f0650200504684c0c4902d6151070f42d4400071b8643d0b4034500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 785989973 1250 785988723 785988733
    0x30c0f06081302150a0e01091e260d091a0708160510180209060d02010c080322060605101812110307030f051204030b070e1909020409061202030a080903 67
    0x16080804e00818008055455101581441d000010a680350b1a400391620000c20041050303450000c0e424001124014405041c018145402040e201441c1481000c002d00c0b4a48031480304036000386c40c40c021200c1412100703010942c6112003117090310a090f00184580002c00c8601e441d07101c000d2844289600501c1200c08855000c0c102c18110740145607120816455111000c04504c5d0048085c0c2d80000207580d402e5940c0015070010302184008000104400008000030701400b0102c24400c00803802e200d1843c081310850b00b0007000411090151900130001c4030b2034030340054000e1820003074000040050115003440d180401085064403901180e651507010009416680d040000d440a1400b80f00c1d00c60340160107103000c0e450401000c640d507150300001d000410114144c000741070340c000320a092460071981a40300081000d1900c42800d001d6525100c0045004000c80d4060802d0302d0841c0800c20640d81c03039401c0500e02003e2444002d43c151b1117150002c0003d000c800183c40ac41a025007101c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 785991223 1250 785989973 785989999
    0x30e060627040b011703120a0507180902130842010f0e060306130209060a03060207060e01050c16300f02241602120c0106030c0f06081302 61
    0x321441c00107031420b6620100f10030051048070f4040000c085855a003d00031460108110f06203100500b000f407200c5900c07907032030000480b2035010740440c43d19201180c18042000d921090350800940000002c28800e1a00c0c180c007103580c120009100865420380608843e40c1c41e0359941a00b000600800c1c0301e00d0600455040d03d18007000440d029020384a032103490799130316003080082d030041c03e802086503101c0c2d80150240a4501183c445030409260150b400541d5951420301040e50b403e0b483c0c2c00200154070004211082c0a0158010405e0780f00c0800280f140351149080c01d41203006408000b080030a00c5100c0c5000242c4860310303c5050a0441d04601e402044810101c440b010340703011120105d4039418030103014a40c1032040e060101401d075071007031566001000c03c000302d08008069100d010b00486a0b082a58000c001000e08144040c241e0350b6205607810515010b444184170496064202c19004100030f00301c40e080200fa990307070360303100080ca41e1400f805114012080009030b0300544046048 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 785992473 1250 785991223 785991289
    0x20c090a150801021b2d0a1703060307060f2f070608090d03020f0a1b0206040609050306010909030e0d171303031d030304050d0201020309120a030f030e0606 69
    0x4009041c02c0b400103132101000d0700c4094800c45600720002c45504480c2092005402500009060a011842d21202c1d00c500501240c078041503610042d002c40d60280d00c8000b51801480150320078001a01521501c554501c41030396800c4e14011030f03c021562a01c1002450f02107021401840c0c181c88114020140400e1b94041c188015a04120001465001007002c1954100001d04003100301e8602180b0b40302061310703803003024066011054208944036800c0e1054034451030080711510b80041030035a441c2d54a09010f000d0301d0b914440e81e0b000b4002e00d000020505110300c5811000ca406880f125a5074100c2410003950810482045031200310f40a40315214090f14030280008020b00341d2a03490301415400c01510340800401e641030070100c680c5840d000d588010060300c00320344058824509601251005178114001c075244150003800710b0301c0c08003c08400141c00d042d101e00a40303038000901e041d440e048080c3c1c1c260010726413540d4410408500c0d2400c01c001c4e1141002e1805200c40f41c00c0e050340ca11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 785993723 1250 785992473 785992511
    0x30201090b07020115120804060f020a06060b0a030c1403180f010c0e15070312020f04090504060b040e0d1d011e020106031b030c0909020a05100201090b0106030c020c090a 75
    0xa220010313135413085c0b0f440c100c0c020580000007a00034110320f01008107540d5a072510511640c01b07140b08100c0003444c00761045008009100840e940400b05102c0f007610345011468540020340d038103000a08048590039003901900c030f0105603141041e80d06146907a90140c1034107440010708468000d22441c0386030150000c0a22601e48101c2413507440d904050500340c06c1000c1c0001e07851042840000400600b00065040b164401040c03c20f00d40242e01c41c1701c50304d82c406043c0103581c082503c05090801f008104112544100e1350060200c030100603202a220142e980c400c2040241c1004ca8682c00011f4250b460b17103128031a03004e40524255811512480c03d044c074081c4e0500004001d40c1d1a008140b080040450045140c1448281c09a6031189983c0360314030b003248513104407901552f40d41c84900c00c1d5210304c1e9104014281c05415000598881c45000b030090216031010b80f4000441000803910a12038001c0c10007207040d550090101c07114034000c102c5c0c07883c0090f040f803240c5582c1f586400b14801c0b103000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 785994973 1250 785993723 785993731
    0xd020d050312040308060901080d030b0a05060703021617060103030809033105091b03090a021f030b090601050405060a0e150a020114101e0812030610021f09030201090b 74
    0x1a0403611070403c0d29001d024a40040c150502c5078441c4001440301e5040055181c40d8201c0d2494081500407210000c40c1961a43c2c0c1c2110ba080480001d6036000d15030000f5150360000406403103062040d40e40c001d0207c00310101000c2c5e225942102d40108003080c803078403c064114810405491820038004001914040301d1091040c0129405540031207a03401c04c4c4030800201000d032001201031401d049684080b0305445640c0410402c040007060003400c0821103506240c0c1d002c1c01c601102800200800e503140101013180c0002400c01200c0c03020b03414000c800900401043e15850300701401d040805c1038903004525900200000c0344803c000c03a03a43c0f98160002100900340443d40d6840c110300007425150465500607a00390700c2810b224200400c2440380c41110040368940560881180c00ca6044040c03070fa0064a10344030b00010a002c05081000850007050229486426000003c000b0b0380c440500c48509480a100601c030810000344039086000c4262091000040c5c1c655290340381504110700340c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 785996223 1250 785994973 785994997
    0x80a05040f1d06010e0604050d15090819020304060c030f17042901030f352a070e0c0c030c030a080106020f0a02061305030f16060c080301050d020d0503 67
    0x140100780940c2e0440005030028070a04e0b03c0702d0041c2e41c95001c91340f240724034448d050090740542c800b04240000d1015019004000c44c5050085082a080000254201d1820303e40e4021010303100912a034000011101207400320344a00c8000483c58905540d4110000c3c0081b09100c07240941030301c100340c00038036144140e11403a0904640001410009103c0310f050a00c0c1c0f4a070034503a00180f0105002420108000303030704c00a420040035100f8407110600360b40e50020030465841541600e80411a0009030005803903ca50036038140840e6034440e420b134001c2191070007003a00150828015800c40b581100d90110158042903d1701707051611007450756000d281040c030181c00200d00c074000303a40c0c084419030041c20103100420b081d00280d480603807500740104d4002d200d54000220340c00884a00e0721110b000b09001420b540d034000202e400561101d4034481c07010b08251070b00c44040f030164081c00800e06c031a81c120b42e10f582981e0030701c000d2101d9a00214030a030b0340b201006a000b40010810170081244200344 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 785997473 1250 785996223 785996249
    0xe07030e0f0708010b01170f0a0b0a0f060806040203070e040905070810050415020301081e100905060f0a0216061e060f080d020a0b0a0b1503010605041701050c07080a05040f 76
    0x3c01c021500312030b0004482d43c100120011241c1d40b90707500d25100b0340c00030344002500d200b607264058145d004010302200190001d900d403200041c45412112502c04595890700c901d0066900c100410007248001c884480c0810310440c0080501e00b0b090780000c1c0d40354440d030100d0b0701007a03d519045207000f560381c10f941c0a0544650801040044404092102d00011030080d070555040c000c01d141c480c000e28010459a4941140b16004171030708021090f0404010741d8100300b082081d0801a81741d400468181d17010f158a100440c10400c02442215140919901c140f401c44180e5034503c0007500d140791ba0701c0a5003004140103c3d00007060f1246100174150a407590440c0ea282c6407005050481c840100d4041d508500c6141e80862600b0707018079881418101e00040c1210300500041c41c0301550020358051500c00300010030100d400c00018400da40c202510003034150001d804a5013624011a1400c0e43d0344010303c00900041c1c40103001e0b140b60001c90404c603080c00c0d01c81c001110f42244940c401d541002d80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 785998723 1250 785997473 785997479
    0x30515130c092403061d04030f030204051302040e06120705150409020313120302041a07021c0311010608120d0c11030705100b060a080412140313020a05060c070e07030e0f07 76
    0x15110309030080034080d003070100020a4011b102c0d84480010409018040e2240e02080c16a102c3c3c2d0480300542401090102c55207207218056000350414000c068080440002249961904800c1c0700341541104000344100b50800045c000c00800700c003a500d02661051101048680c079500285101d50340204c0503c4401c4506c0c01c00c9030460f00305118500c18503104000500941c0312800982c1880c5c1281802150b44518034400702d0403017218003032450781800030388441d0010954045003611207090860000e201d00b0f501d810040382c807141414003103c901c2d18200b100c0350340c102c680c2d00006004011030600003201001c00c0380140c21030f48080ca00301d81503041380310343c9203e54a40e841003c0c070340304086d281241802551100038108000103040580101520305040e03134650300c02d25581d0902c009400749181c5a04041d28403502d04101900d08034821700d0880d00100341820040140c80c1c0c4202e070040185580d43c07030b01c140003518501c0605244201a12091200701d007a400700300a000d56900703400200b6020349 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 785999973 1250 785998723 785998727
    0xf0604060b03160609060507110409050c0a09020406050702040f0b0a060f090e07080423030a0c020a14010c06020a03141312020c0f010815180403030515130c0924 71
    0x146081940440b0841e10b0b03424000c01c2d505c0b50300013042e541c003814266500d015034204800b02d0701800d04241e0707001d0b04103038841c1d040003008603180c01041801c1c1c0d4940352681e103440030042130340120302a40d800a0414030002000d46069005401c0c160006880050903074160000f1411010a0303402100c041342544042000c0d195011100900504803079090381542d00f07100c00d00501c41800900068540d08941210300401c000d41c2c40800d0020b031610088940d41c81c0b442001600ca44500c40c01a48240e01c04200058030300e114240d045460041651030b090114007030f43d141c50094104034044000c15640c3c5072100690070141c6211409641407202c40041d20b0140c0c600346d0051100440c02c030003150070142070440507850b803803080ca41960003402c00801c07655418050006038001e0440344c5a000c020769003c003c42003400b0030001c0c01540a50307014050380c4d0721544a82501c030310f808c52035030300400d40c000d00c9401c2c48504d0340039405140d038905c0c0208040d903454000c0b4104140703a42c403028080034004a401d040d59 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 786001223 1250 785999973 785999983
    0x50307080705071a06040e07090b0307080304050a12080c06070e03060915070c1103010f09030210020310270c0f032004031b030f060f06060302070c090e0f0604060b03 73
    0x1c10103140c114a40030b00d9503500b0705003c101c1500e4070700000044d03010030000c0c2c0d1a500404e907802440c3c800c40c3c002540da100301c00e02400380e43d2100381c024003400802140002d8003004031411b403007001d06000b4001d4a042032503140750461400a80e014503050020500c148002c0c03203294011680c079560410790042d500101030070a5800780c4401e074030b54090a50364610321102041150b2003001ca0400b04a00030090911081c00d0040cda0b10380d9041d403038006203800070700300c990090790358038026800c0350b411103085c500d035030102e100030f0764140030b0a58480800c21007054958140304240345041420005521400c203481e0903201301400c55004104010020b0500c0d51703151041200e07080000000c070415400c03c0c1110043c501ca68000a041006440103801d00700021914000045521000180b1780c50041e00388480141500e641c1030030b950707003422000a041c5109000703940740355401c1003142c200780b8900f1408000400e603007014080c1a00840c003200c1d543c6101442901e1059000c3c400101c0c4550a139003c0500300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 786002473 1250 786001223 786001231
    0x1a190e130207020d0605060613030b01061713020d0303090515090c010e010806090405120307080405010b01050315010c020102010b1e03010501210308070216080c120f03221505030708 80
    0x4107105110040159075410004514141c00410014040e200c0f02c021501c5403107010701005046000301c000000304881400309070304a52003542c07052140160040e118a13280802d54816140721100c21134503026292998203030030050310a040002c0c45040c165241402c0550b140e0803002d003040c1d2241013291041c410b100103211228240b030200c015450150000e040c142c000f8200714000c103183c20000b000c0040c00c000041c42c1c0340c824083c480d201d190000c0010305401c3c0454088540d5403c004440b01039500038000c7d24001e140c0782e0100a0107039491001181c80c006042c1090b8110f648440b28414241c40381600c846406080254036000c01424100345400e41d039060f844000e0209074188502d40d582da942082c40b05140d458900345d803403a113541804920b810304805001466205c5001c1c005460040082d01c80e89600b000c0e02c1d10203e403051360f0f07804c40c1c41b85101ca10305001504104200c00019503030450fa0b4490800561145118036100e0120038428840c3c0695900070400c00000c1c0101d0740e07000b80741a648 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 786003723 1250 786002473 786002509
    0x60d1d071a04090b030307050105040f03020d0813060e010f0204080a0c0e271c080f07021219090f080d080f060d0609080d0e0d0f030908041a190e 64
    0x7010620850000c50740c8120310030480e030720b55111020407aa6174107004440c0c60b680c00c10001d00040c101405c0484240101d6138040740540709002099042038010328065100303044105d083e960146c0561596009010078140c801c220303543c1c94842d2a58501c4c0b43c405080a0b107100700080140f120180361802c0825220b401500c0d2001585040100049020302c0b138103001d8142d482240807084c004402c080c0307402e8000905101006064060907074655024078020300c14402c00210500d00c2d12490810380c0c440da81219005010002000030074000c0c01608015600c0140364034010078039607901c540c540ba44c0b000c140c10032500ca80045040d0701110703074481c004580000c0f2540140d1780c2809c041340041c81d8104180001012192078441182c14481380d00241c4040300408001484100088080386403103030f80c041c0900c004919421850b01441c0e01c688220701e101948040b030189054280050400d03055003008800041910810142078046a030340d0303041d42403019a0720340086481c9614100006007114401280c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 786004973 1250 786003723 786003749
    0x1020f0d0e102c0a03080706020304230c06180a080a0303060e0907060c0f06240911180d020d08030106020c06070b0a0902061306050306030d2606060d1d07 68
    0x801002e44060f550b8510002c803440d010b40d1800c100100d000c0b11629031002e8003c0307401055207404e20085400540c0301e00e1041c00e081110a540195942e00b200c004281120164801c80740c610301402c2c031200526181c492101541107203110b10340010038581c1140c1050282e5003019900d4002c164043c0103500c040c0c030001e410034540b0700e403110b505941d0715560b103d201c00b080841c844040c24800b06c240c1503460240c0110050003a16905007908085601c011841110200000000180b42c4801c0c0718100d254110500c1c0d02d481c14400c44140001d0302c04c00400c0507440303140461428016501c80614100b840d02c5101c49079202d41c50700c0c00c00381c01e01d0000e00b000d50042d442000386400154603a128a030380812042c0d000120b840160010421600895003000179645c10743e8404507910350400b019601c03460b400c60446a00250703030142112610202500c1500c0d80703040595000c0031042008100e6070000d00500480e040a0700380b03900c0400d6507002e000540c00051002002e80c0c60030340074040130014042e503d000340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 786006223 1250 786004973 786004997
    0x91d0105090d180f0303021e06010b0d0218060c0a060e03090d03031a1005130b0903030909041707140d0305010b0f0702031009230c010c06090201020f0d0e10 69
    0x1540310352002c01442c08201c01d03a41244046005010000d0251400328000d2040b01e032a864081d40d40d01c0500454140e80c0310315074401c0b02141c00020404e06864101002030b060032600c500c204069005000507210700f1151800c911038039161f11010b01203150800700100506042400e124084440d15150640d458104115140154584902c0f001200e41d15140000b00242c04a03482e0030340410806d1b40961004047c0d29200c404d41c0d00001a0014045907088270981d20f03941c05900006102d00d00003070350543c1080c0220b2046141c030014003948940183c6003600ca49011000112440c0d104c5141141c4500444201011200c0b0802003114450f415003800c00141d410032242920b40d001d95803207041614000221901103407070600401c5074142d070f4030a06001c0343c1590314202c3c251000140b2181100d51314000399100940340040d040e10201e0043c4c40d002c0d84001507885400261800c044140e042d0310603000e00e045004010418080215a65034030002d003008076408201407c405040c80c13800300203001c9808 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 786007473 1250 786006223 786006241
    0x80402010509010e030a0c15090501090f09180807050115050904150c020a0b01240c121b02060705071a04060806100207080f0c13050424060f091d0105 66
    0x1a0394802d02401c00340c158650120000c2e24014080400403d003491002c00020b0303494418040da45410382d1a10382002054551004444d5003149124032040314040d8a4200460001035100d01d680461540740c02e10002c44540350309480f9032240c001104c83e41e40d41d0111540c0c040100b040d02000d08802c440c03261040c2017540b11303880304549408058401e503540d10005c410182c000c00c20425142c1e80032001008640c5d403186000d40d0b845410003819107000509140307070031a0b4440c14002400ca68880300d4042c05550140301203c1100c0c1d00c0074120070400e000d81099004d030b0380d05030250152a12900091001600740004102c00c89d040000490403080284428415550020a510b81c0407106076402d0090004030b030002c0b450510b20340e00c44c509502450002203d00300001c5620024480300b0f440e54000b030390407448401c040b14802c40d03003c1d042d04512050030300748158900158400302195071010422548400103107404402c1c0d684043d82980d076600700780700301040d01c10b1b42411010f2004020002490a9015 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 786008723 1250 786007473 786007477
    0x4060e0c030a0c030b120c040b09090a1203060506160204060e060f0103020315090108060103030813150203060d170d05010803040303050f0a030e011112091b27041a070804020105 78
    0x7002c00c0c0c5403501444001c0034420380c050044444001c000440030706c20644441d840300030f08000b00e07000b80d061000e500c0150803c0000301c2d000f950043e000b003451009540750803030380c0800803207440704141e104d1200080507039800010b8103013280903002c0080f00511a104100c100d034041c1d80034001a1100c0d104002745c95503844092070b4905000c0c00c002d40e69549249110110a0383c3c0012a50b00070750f000e00104000310009001d41c180c91281e00c55050581f2a10410728100801e000002c1030b10715508031550b00c0e43c616801651b00400302801c83c2000e00e4195613529801500d5040c180001a40840c00410320340c43d40c0580c600500a1001840c50b01e801d580b0000d016101d00948074024010026510202038840d5024110138000c20000b044096000c40d50401d0941c84400701c244034000c440d002c2400240045083d4080c41c145042540401c410f54007880205a0008202c2c005464103203044160701c0b00d0120400d02c61403144908002c02000c805000100c520b010300303420100a060820880140d0300034007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 786009973 1250 786008723 786008731
    0x901030c0513090212030c10020f04060f0c0f2105071104050c0408011b03110325020109051f0c05070f1b050616030206060d0b0103120203161104060e0c03 68
    0x81980001e20b1081604000d04101c400003904802c0d03000403c0e241039400701c050410291070314151202209100c0700c10f41a40201c100c08100440300700410444035024100d020200409820001600c800c60f07212194960791007070065607052007484001c07003022204143c0c00550740d402c0c24a241890300c00d0300d81044203004003038018080c07552103000c00d428012040c203850003400c4060081c4035210031201e00764280140068660042810724016586195060080d02d106410001c0100308044030004115001408a0b003180190b560700c01a58010650a200320b004085403002441d14080c101500302c401c0b43c0b044813440003005000c1c08610000b4218a081030360b0300d5003003a545444003504907500d042020240c2d00003135103c03400007103999140818030300c4102c00e07500036000e07200d00c0d45c2c410050041e003541070302e00144000070341001070000030319003842d0010504052044a0911414440f000c030003075405081070780e00441413102c041803403500b40100310240401030031a086505111080006034040a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 786011223 1250 786009973 786009979
    0xf06020304210c030c0603050601050414010c06110d0e0c0d0503030a050c04150c0201090905090d12150602030309120405130b041103070905040f0c0e100212270901030c05 75
    0x300c84041c0186030758040e150080d0020b41c06003d0b00c1e540d29101d050300d0194412480402c0c2004001042c0e9070080342504d04890395030510b0195201030b0b000469aa0814510854000d0303a01d41d1190f484e013280d42e02a00e030280090700e0000d00800c103240080d250410300702205100d0071400c41c5400000e40040140c0ba008034040c04c012985464400c207131140e070b00070317900a40f03489a0722007800c112107544118040d00e514000e0301d07900c034510745880501040c0d5201f04d441d1340081e442440868100c900c950b00c03680040700c81c5900000c5618110580c0b52441c0c40c01d03841200103034004020303c06260b80c24000708403242d900024030f41c0360500e8200440c0c00d42c0034418561910643d2020200c1e03c03600c1d40d411095171014281c42e020740d246458540940b03984c1c19800750034051880e156500d401140340748070b1550544c2c00c0ba240c118500c0c00710301c200301c201c40c0c00300800e40460003500b00244000c4c0d4110040c28020340102c0d40398000c48540001c003519007401d921114850075105004201080e41e140d103010035035000b5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 786012473 1250 786011223 786011249
    0x1e2217181503151509040219081b0a050a090f031a07030911010807110709020a021b0d080913020325020a0314030c0f03010308040e0c180d140f1005010f06020304 71
    0x16034070420700e010300f001251b042030001030001003401d0302c0c148800e041003880e140e80c0540e84990f00c0f00340c1110213480000381d02c802d00300a1400c005010381c0c05000001b245281c820f1180343c0f1180000e0800559600480f0000050f500041e00c2100f03000007958803c08a1408100303405564640003100500d40301c00e2414000000c1c082017411307204420383c000c0e0302524002c50b480603a0718003003580254481c03080301e40103009141034042480b8440c00b4012644000900942c00b401d065111941c195001b0750ba4241d01014600003a04083d07110b0015500c030310250b0445a040305010b910f000130f0307081021220703c210341058242c5d00c0000e4220314183c0100c500d001d6400d840e95030f1100a54040c1c820000d4071950000040000010060024028001c0e60341c10000004c050b1684010b8034a0b600840e5848480c0c03901c486c0816000d17040804281409a0080c1d047d0041142c4150340c45061031041d000c0000c107234104144090900b1158081c4900404400c6044103c00740b45c400000d44138012802031100180c02c4c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 786013723 1250 786012473 786012499
    0x161404060e040e03071101090b04080303010e0c0408060709030204060b0a05030a0c18140a08010203060108070c050304050901090f200d09111203031e221718150315 72
    0x102d40c80303201500c910300f0403640e40b00c100e41826900e80000c555900c0c00070340008030205030b042d00310058500f120f160400039030643c3d0a1107080404c422005003c3c18100d2000c0c000040c03941001c00c0342c1802212a03448030155070341140144010394669411400112008008001066030b020301101d0303100e810b412000030400c0c848107045900e00170078684114110b2101d03c001c00c82d141040c0405040d8401184c00b602100c1d502c1c1c010f03e00380c1c00304842c01400b055400d40020313a040d004842112000b403040056078076254850b40041c060b07070001c0c0c000110042e03031210b071440c5490845c81141d8090900400340100700311700c6800c000e11445415510001d4a48a080b0041040700c0e0011000c0a240024080281c55482c140155aa504103c0307460076059108032481d13260821500501c1c2c0500035005100004408405041c098040f0105040300c500e2a020640322801a0440c0903203810869855000103c4080c01d01304920341c1010f02d0191011102041400440b880101c04a07609510079120b01240c080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 786014973 1250 786013723 786013729
    0xa110405040c11100204050405100317220e06030f15010528060804051603080d2a02011b0e0906040b0102030705010f062d06050906041d161404060e 65
    0x9042d0b01c1c0052041020013158220240c01410541c0d00c01d480c20005559801044819452288070240c55450001000c0400030300800043c4240984c568483e540604a105080004c072001e40c072448086110300103001c07252505115620b8902080e030700901c0000400303d44603101f03103018441c05100c2c550f5803000a5001c940340d00000f45000652588100443d40c0b118082d214030303400c0300c080b1428010121416201d1042c44001c0050326046405079084c8001040c0340c00c020941185401030b200c0d80850305031038552040f07641307582c031121507400454a80e0304200341c008071190802d1128140007088050041c80d844282c0007d500904c03c076004514012080010b0f4111f1040c1c04025005508208020f2492038240c1c00c43c0080f1881103d01c1c2c031154820100119100c02188204030010481c00c408100440c401d03070103058400c5008110510f01551405040ca5102d50442c0040784d403840d100421201d89188241c20403241d0007030900640c005100e140c40c0d001c0b4841c901540060017442240d80c2500e40b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 786016223 1250 786014973 786014987
    0xc0f03010905060a06050405240910050409030c0b0a020405220b0d0c030b010504020f030f090f03133f03030f02120a0605030f10110708040b030106080a110405040c 72
    0x1c0d4200e41580c0341ca0411600d4180542014060340b4012030915010458522045910079500e094144038650407170700c1c100400c0706a10000c0e041c95424424094042900c1c0d480340714082c00a44030b03031142c00d940922072410740c0074140010401010944140f000b04080d803507009150520f0140c414030a01d00203418415100100034103410944c00000c08220701c0c081004c1c0c0385907081628014807441d599603907100c00700404c2c2c0c814600541d03240401800444c901c00c48070106207400a8514080d1031030b10040c4c151851454101014140000d5020a01080b442c4010109012003040c003514a003142d4513075841609190325114603641d4078000050b450380500d4460b6000c0f100341c80070034800f0b543c3d400d28601005c41d01035050300c01d0f01000e8541140000c107440e0015419000d81c00584c054000380368070048403c02491810b5901205c10020022000021401d07c0144007900011074015140c0d410800c0042030311100800c2500d8685c82c0002d1a00640401c1d01600c0865908440110f0490500801181c0340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 786017473 1250 786016223 786016241
    0xa140312131a03060d11040e1002091e15030c0408010f09060c0201061a1e130608100b031503031605012304110f150301121208090c0f0301 61
    0x1038804900c101004040d2030414084584290300901105052120400d540c4401d48100c1d903c01c0285280d28002007600303100d1148000010000280005801945401c203000310a41c941120340c000382d9440741d46000702401e102d000602a0b0400504071110106440d025011341d0021401c1005c400034041c2c04249040310082d00c4040024010428454039010103001e01c45021030b181410312040c00c900510520030201141c4580e260380f09051000340e0a4042541704d59400140b10078661501d960304007500000b4170310354030356962050a19251060040036014081c1c0410341d86102903004000c491220340030b590704000c24407203444000c4100c2d80082d241d4421065041c8000d09030358284024050b042d4481e80c0c000c00c0e2000c50032a00e581c101c814451f080001c54004003028180d003004c00c0b450404070303800219443c019007118403120380170003005d98a410903440001034920105252040008114030124a1403240c10000ca01c1d0501c000000d8440541d10714460240070114104141940e00350007403041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 786018723 1250 786017473 786017503
    0xd0605250905120105070c020f01030908121f0b2203021002010e0d021f0b0402090901170c011b020111100c031a0f0105040329070c020306060a050a1403 67
    0x95100e1042000e00040c4041c07040500c58000302010912403281800341c288924610354402900441c1c03075080001000e6401030782410140d071003001c01c1c001021440103001c074945002091045242c000000f07080c0e04d0281502c0c0900360940501003102d089284140e40141c012038484020034000001c05414010290348040e610040000202400c81c0e01036006412041d0100b00351000c01e1410181070740d8030b1060840484c0000031110112041c41240e90000c40c2c000c000410141c581050840002c81020b020b1300040101c0707464000340d072000784040040401c489400e00308420814000c28410400d0842c1c00b0010341800074826030790701c4480c0284070b0441003a034445000c014002000380020300900011444000182d40c0c0c0443c4081071804a4050b00000c80585d1014130b03060440c1d4401901608545010440d81102144500c40d03000a0107a5031086040380d65154034080540101881c020303000d45600e0140c41104c000f480f076515401a00401c0e1640350100c00c0b09243c03a440400d25011030341200c221 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 786019973 1250 786018723 786018781
    0xe12070510110c0105070e0604061d031c020c0114040e090703050610030302071e180207020303040e04260a0c030c05030304060e06010f0f090908120703150e060d0605 73
    0x302d8a0452014111415002008110a0381c0301013064402d040f014a85c541c5c08032050200f007100a00c10401004101c0495000c2000118030f0750100e46003001004a204565901908101303005504110401e2041000d02c1d00d00070727200030000044a10f00c6640200a026104880000c8101c201040710200456103c000c40340f21f80f4000c24113190361051400210010302485200142a520100017140d40384682c40142e103c01c1c0c985803a170319106c1d2070f4001e0482e0483d001d10203c03015a8003800904001e1003540d10400203071400d40303040e48074801e07008008800c5040070034001040c171103590150b07070301d69900d424400168841350800383c50111155034004e0031340c80000108010400c20750411001000d090707040700c00c0e40c3d03200c140602c03013140c2070300a02c091003042c0c600070041c00980350001d40b5824094010149001e000d1401e20584420844091010076140c034400c15800c0075410300d2100a003603641c411a11420a00c0014103560205c0c0006001c0340d40b504049003035405484000340c404440c0d021600 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 786021223 1250 786019973 786019991
    0x100609181503060e07050f1c02120a060525140a020c060403060905010b09042616210f080f04031707080601030c0e01021507020115090203040212010e12070510 70
    0x10300600791090300010b49000d88440058141004c0709100c80120004010480a400030070203c001100403c0c02684e1000c80ad80c1e0f81d244d40502071100d590303080d00511010440c1d20740710540500e00e060404822032612009109806001da00c81d44200204102040301030350b41e030400100300e18040a004020340d00c00fa0000303000040022035801005010b208400a01031619468100410001d04a0780981844ac0c00c001c200a030030344039503c41004005140c102c5040c02c1c0d2400c5422a0000074040885049040d4402042c18038205004400d000c0a50714140a01d441c6d5031400900384d00d800b034001c04407215800081000c00d8050050705401c00d1f656900007200c2e14000000a04951046c1c640d03c1c0800d141c6045030040b14491a4800c040c4a410780050440da40400300c51440480300828550855684000b0000602809044030006080088001d41c50f0305040c0100b02080c0110000020180c0c584546500008400700b0300441c4a0140c80400c6d40b11a40307801c00302d0400030540c28178140350307146c88062 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 786022473 1250 786021223 786021233
    0xd030504090f020d0c02030a09030623043903080306041b170c031302091905070f0e041422081303061b23040f0803040806100609181503 60
    0x250a006864107802c5c08480c01120013641c407803060201c0c000008465050900200d0655000001244c00202d5201c00ca113140c01a0130500280c01c0d6804c8412902234002d6903881c2308070ba85000a080190782e5018004c0a80380001c0490402c2440001e09080f0f000c400142c3c036913240d45c0000451680d000c400c08901d040c01100901074000b400a43c0b0aa02040001c1440b0100340d2003030b01d20071a005513192025010301d80030400b1a810080c825840c1c101c2d00840b000311152035001e02e6018440e0741d155880300a01c034181c0540500c0c2c4c0381350b8150095103010113590844455910440d00480d0086081241040c4020582c00f00300c02010060300f0400001200319103481d00400b0b443c01c0700d00604040161466030707440c110301a0f5030b01340f40500141b042420010030f0789885040c0f09d03040b50102c412a1030103a44484416480195078031140340c83d000031400708100d000500007903500941402e0f0aa11090900781e015200b01e0650041c420031707803c0c0c81d20300d2181c40310b02d92150114017194009412020354910301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 786023723 1250 786022473 786022477
    0xf0e0d080301060f03020f0d0b240d0b0301051e073c02010207020d0201030f0212040c030501050718060503060d4b020402030c07021807090f03030e0d030504090f02 72
    0x15580094140f072403040c090340c4684261f6400003804031759540b0745407080306020b003c1c0013140035059000e2260b034601c0c420b00c400d040c11143e814448500d800c0e10380203040200b600301c481c6003200328040d904080800095142c000c10004041004a007520041c0e198101d04075203000228880418990305401c600008060406045402c28000c181c3c58402d04a104800c0f800e0340100b44000350040110143c1c1c00049d03000750011040e4200c007070b500505158074170303890104489054a05945906600034148180207013030140c02c0e800451400c0c040180001c2103141401d500e07092003000304222004c0081100e554801c5c0500f1110b0f900141d06800c03800d1059080c14120341542c0700071081b00300c8141c3d9a04076605005260342c11803058801c401051100303400380030196000520340443c00204110300c50040e0307140c0f1020061b03101520003002461030f2484003e802c00b04903801000b4207200c514010000281c2c01000b24188d940c0581c1d0040310507601e80b07020341d614081d41d00725a584c5070038904030161031591980 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 786024973 1250 786023723 786023729
    0x60b0706021312030c03141909030b0112050706110c06030702010c0207080610052b030507152702040f110706060b040e0c130302040c050d0b041a010f0e0d080301 71
    0x71003102510f40e102c010440c400e00a24000300450b010912443c0424001d00d40c000d4a48042101030380f030207414403144c6021394005004800811103214092007400041861140503200c0340200342d0b0500b80680f00e076079a031403080c4141d4040048418000201030018402e008030b1010186c141038480c141140043e003e4200820450014461900c1c0010310400019105000300b00f904020004d031820401446410280c0200c1c10082840b0a2120440600c401c0f000506540c02541d416481e02c0c42d910342032111b000c40014420100e42480ba0802500342004c4007003038078403050148510304a103a8070109010b09888440003682525026903c0201c0008100400000c2e01c0344500300403c6072280c050b24918003982c001c2c0301070962840001100c0703140c03c4000300400e5040c0a04004803543e00d81c0014161000c000030800040c40c00300300710b00d15500d40e00624a03158003c42e02800001c0d03031004040f20028000300d541d81080010302120514a000e0320900c143c50340b01801c690700702801030905825552081c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 786026223 1250 786024973 786024997
    0x1140f040203010b03013803060a050906070e220e01050106050c010f02180f210109060c03021809060d0f0b0403020610120b101203030c14181003060b070602 69
    0x1c190413210b1506124034055182c03041c3c00e040c0c2c0100c2003d83c0c3c460004801b407940551640c90801d08040b580c0400451781310b48100d02d808905840c00d40307049406c1c01c00242682e028000e88005480310703580c2d2184000f07400e50504420428030849811140054600b0482c40d40e6203501c0d02c400896256802401400980d000740c2c0240182000300004034101d201d68030f450301d0309022481c403144c03240c940244c0e40d82c1803ca00502140c8102a20800e10500e5070b0f1840c40d01517240e544a05007400c00025004058000c02a070070214108402000e14000107450b01d42e001e44201c150900283d00f81e61341d0101c015019401c2106195030342c4040c5084503d000341654150054450040001d0a13807a01c40780321401d680759072204032880a6203030f90b42489850050000b48015402080118444114451040c0c60342c0c02a5000304180c14000b0000d45044001030003002103203070400c21190121284c2004400380c0200356409001080c80c0344c1d044006003010f03003003001d006a001a5800c20b1001c41c2e000360410f04011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 786027473 1250 786026223 786026231
    0x31b1306030506011d1002030705060906040b0c030c1b011e021e07020a090b0105040504050f0402190503030a05070609230c09070c230601080a050f060618070201140f04020301 77
    0xe10b0055410150b0303041c100c8103842001c440c02900b414401c00400d1a40721b0b5004072402e0840e01c0c0d485906094040b60801e2140d40f00e9401c000c1400815034402d500401d00d41c100301d286040103c04045603114040d0079004425003a2060300281e0760951040450a003510041135545100005c0100a54401c05507504045510440342103401309240071a24015030003002000c0040c0350540d61409070048103001c3c1c1c10302070240000141c6855900030503206140c00c144810151038980704005032040181d4101d0780154101d041442580c40c000f040354001c50307280c180241c03a0f20951412001814800c0401851001031091504400c840c000380e100030007074080c09031115580b454007400300c814000c50309540007810219030940441c00740100742c101010b2442002d2402d425a85080e80381c01c1d8281d20038401c40d484046490140001030000d0103100600c40c1c0a041d1a042100000d49070b03050301b510109141038000003045c1101d000b548034020708034480c2c4032800b02c0c0c0780c0181e0150466400310b800340d002c0e50070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 786028723 1250 786027473 786027481
    0x5040f1b090e010e06190f0903052a0d0509060409020a23070f030302030411091513060e0609101802070b0a14152706030f0a03050a0302031b13060305 66
    0x103000b164000c4c9a024020000d540e901416170301e8072504900c1c400c41c0141d9074058911125054029001828025100d0303d07912000540d200c184404d920301c5078610100e28448040c1e6114021503d08400c4400b80b400c2c9440d4006180040d45510559000c8900a440054400c000305c0e0480d00000300c00300c07003c4501c4a600002d1180e00c1042c401c0c441300505400d0051241c0001a000c0d5011310b80003405107200c0100b0003d01d20109060190507540740c04100d01c0f152035400b40b4a0042003882201ca400042400b416251280d01d64100c0400b901487c81202402c0005010750600034402c001400d0150f486a03281c685601400020f6000e00c4055450006800000f941072005000f0721040e28403001c4040380a13950780960301c10003030700b4040980d4400c00c40c50b000f0a01640e07280c5c01c80c40c001c000c0c03603503010181480e40c10549032500c1100c03859125004081480c000c6601302060700c0c180c1445080259581e03449144a020501c80407481042481021480e903c41c04241c1c0c004a007510403540b01044180c503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 786029973 1250 786028723 786028751
    0x50a0b0f0c0f1303020414100b0a020c1314070801030b010b19030e030f040b030f090a1a0a0b0a1508100807120c0e04150c08040b070305040f1b09 64
    0x5000c6500c0081080c0c1085030940358050302c402401000000d0f940910301540381da0025040d900c001d000f5403080940c200a0003001040343e0300400050104420b490301c1c0c00c0e59040d01a45868908003c1c80c8240c49907048292441d1160b040702100d0310320044000e074180789c050002f070000c440a0009403002c0010030b00201c2c601443c00c1c121545485900100038001c903d640080b400360000c001650854082404910a00e4506401401c0508055000140c483c071300143d10090922004140c400c1980c0020582404187d040300c026071516a04030109a041e80d03401540e401501c4c802038510b80126400000041440000c020610004210b0b070b0340340c955840341865110079450324040d01c009034000d80003c000d1034043d00c211741c00c10f500c5150350001956641e0724502d070000d8221804d461003200020f0750059130000d0302c03541e807880d05241004d80c0c0f80d08045c3c030b844000c142c1c010031400a141c0d07200301040a00075966802c42c203184d4030155120402c4010401e400851003180308140b001d6041c01c51034502a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 786031223 1250 786029973 786030001
    0x71404061421030a020f0c18040212010e060f0a1d06070c060b1003090c060201051e1e04050715230a120204030501092a15020102120103050a0b 63
    0x107069400841c107040501041000c0d5024860705590701044000d088410680c00380301400c240c404540150161100c2e804086041410751402d0920400009150030b00d252080a115130b002038060f13030b145400c41401000c09005112044542090348100b804000c410b080303a0700150b00c07503040104203104c001c3c034400c100c60284c100700e07807251000e0700040700003204140701c0c918800c40c00b4000e21000c28240201c00c08640005521800700000a0315820740005101503228000c0081ca4248001c2140c2d00c2c200440390440280d0f029580b007904401c9010a5448190000c580c0c05401c1900d4094240c0c2044d1400b16a034014500c0b80012081c02e0030700490545008904410001441d051428a401001b0031400c0b10750380200012024040505507100c5a05614809007015621984c0006038000c02420038240c0356815101d10422400d441e100c0d60b4a03182d114a03101e0032240a40000b05600302c014100f6800390251040c407240c4071000900000512000203802e8405501840303240c6141e4507088401c0c6900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 786032473 1250 786031223 786031229
    0x19181707090b121f090f0c08010c050c0c060a030e011d100c020316030c0c0602010911040504030e090628150e010503040f0c0e0a02090102010f0204060c2d0507140406 73
    0x5070300039800c2a542c11481e412070303420b0340320b9101002030905c01c940e5651b050002e9005d030684071b80481a0091066460920400300c58100ca0300700703181009084440c0399a294040c0c16620f00a00d0f011075040c0c5058000d400180e910000080240643d1405c4207007200380039000034040443d8454006c40901441c030724810155401420b40c059403411159060700c8140d08480b41d003c404100d080380b1a54089006180300c0009804594000300782c2000e94148a01c6601c02021180c5c8550f00c0c0c00107100c0040d41244000844400c03d4072160007070341e40c2c0000283c00041c040900d840100500b00e9401e0024104a455400d9521001ca0341c401c045030041c00b140c02a0b216221140031800400100740401c1c151881c04102500c904540c0640700d0300c5040c00400c0000c00d42d4080002600420b90a615680a011704158401c00c10001c40c00d140c509038008001c0484210040c00c6032070314149489008100e031402c001180e000044401809000b890300c1941c03401e186c0305200070024030461002076480c0c01d029030411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 786033723 1250 786032473 786032509
    0x160b0f0a0302070c030503300f1315060b0a0809030406050708180d060f0e0c1e01020102250314031303110c042c010219181707090b 58
    0x400e0260031090340254810001911a400341c5140040050410030040041003503021894a400010740030701c04c9400010204138190811840400c860031a40028455002211008000040100381010340c103505144103e40c01c1d150a000c0085004c40e55000141094001039440c40f10340d9403800c3c40640c8900441c05032000207102005004080b846960203800d0755600c20351914907440707902d00082c619001da141d007101c1880e254078180000e60702030711401d003d4020501c05070501d941758500181c0340d01d1502629406c61908100f08031900d910035070548d40c0480c140c1c0702c041a00501d0010381d030008210f2010071000101e05000480c00c02d0a00e2080d00e009029205600074003c8a5513407d84a912402c11083c42d140b1903051140785503070302c030300a00340c080d442d1100f01c10800e505010202500340d0307402003c010036030040240d00c92501141c120703800683d80b42e03c3e203020b1800913000c9a4682c0b2700e0a0780140122660315628000111010810300d04403080000308120141400f41030000024502e0034944e9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 786034973 1250 786033723 786033727
    0x10f020312011419090b040e010504050c0405090a0212070807240c2f040f0911040b01180e09010b0a0b0306010804080405060c0604050606120d0509150a02160b0f 71
    0x194055000000e04001d0f0b004040a141103c428820450300b501a88141003803074035408030aa0500301841103886258038940203200c1071516840e003660f03461503039074403900843e520000541000e00911003032402950050901301c60411009101ea510020703400b9014440c007801038001740c210f0740d8080d4401406070340d044610000c14203010564011644810603140000f118030304c1d95480103a802c41028441440d45100c0b840d01440050108582c10104003281643c034148401010800340003000c24000c00448000c41c502c00740ca00101e903268280499240307034141d2007001090b80ca400403512885007000710700030018504680100944402c1e40c0c032801031080c500700f01107403140d403050500a5105020700c10301c2e07141ca6607820224005500015a189140c0c0000d81400100b101c20305c070382c0740c01284c2160110045000b010b0041c0d103640f5204410002c0c40030000708010142c40c0d915a02d010040710701d2040383c030355818200103501d40e01941162150f001010001240e11004042601c41c4044c6603c0c03c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 786036223 1250 786034973 786034979
    0x27090f060c02281104061a0f07120c060e03120f07021213050307090e0303010b03190507170a0e0d030b040f06090b0909070308191b030e010f02031201 66
    0xe00141404480003045020701d25407041c0c1c1440d001084102a00022000d2180545a080203104004000d0219201c0d605141c000c2294080c1004500001d035030340e4030102c1d40d80602c0c0c1c04500030b910030944010048060000d450080982000030352070030394000d000c18070200c0c00403d80c558592260f4407400e2045042d41010800c01d00d11301910035849142401280d54854103080d480c0e249400a0101d140e10b659404024081030070705210319001040ca60b8400d00500f01c2101e145626404140581042e5400100000391450300c0000c0404100064020030801030800d07040040c030000507510792416415007500410304180c0c041c0715941c1103040b10405055121009501200076040310fa00030307940242c8a0031511032035141480f4510003406020710000f4205603040a0061242d00204900202c0c0c11946003080814205c03400c66210520401481d180820303502d100f50b0350030414035200f40200d1613640d02c2000301504208100242d4100340c03504240b451910f54201e980c3c4c4184000c01d5141d6070b501d0010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 786037473 1250 786036223 786036233
    0x2e1112030108030a11010e121305010e152512170906160c0503130e01050303070c0605030415020703080601020c03210c0f060901151401050a140c0727090f 68
    0x90b000d00030a817400400c00150007a926403901002c03181c614804840000c244105d6050745480000401084c00c00182e003044440015144841d05221241160300001d1503041080d00d200003103900a841e04654100d402090a24240c650850040c260200302a801c12800507982121190b104003941801400190307072780c20400c07030070300c00e00320400c020301c454a44944005403040c0094640b2500e09100142024a49900e801c0340520603840280a0741040161902094901c05814243c0d002c5040c002d550751140d2800c0d81c10004000c5102440902c080780342410550b2016103079014002c26801c40308440306440416441311043c00b030400c280100e02c1550100100035a018048003054201502c22480306c100f0400d051100c1268803d5583e551a04803c00d658207611100c4082c008207514810041115000a000d6115080340703101404503102d00300c40b400000408844580b5900720a54104959910030f4903078a04000c0741c4611f032110f43e80409584d10603a44151441181c1000c40a00014926195 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786038723 1250 786037473 786037487
    0x2090610030b0402070b1506040b03010b1612030e16080705010819050906010303110706120e010b0301020d0207141b060c011b120c09060206062e1112030108030a 71
    0x904401d264a80c8002da55030f503078a00c05046030b640610022507040c606540c20340d01c0302034180c0642e48526802d20040c00b43c24100760940f0b06617000c0001c09695580c890310400c20040441c10000c0c540c41203011602c4a850789600440c0c0d40c20565401ca4003402090749650400c05401c1c000c03804103901c5004200250742c4110200c907002108003079900441a003410180303080d2002107840107400d81c0440e0041040560040355003c031a2024000f074494a810840020302d01100c5141710100c2e2603c0b4001d001c00c480d0203500c806285034005000b159100c460112902c045c2d00319040a0741e400c1041080502d00792004524000c040c0024000d0400761203001082050301d0300b0054103da5a90f40c2c0b90424001900b29070f85031003800c4140d840c0c01d00c3c1062400b491750180c2d4000c03000c810800090a20400129400240d002d401c2041120400b20010100c0200fa50761080c41745100c2e42060001801446c0300e40003c03104c48101451010341e10000090f85940318544070a11a05000f580f00700b14006940d44a124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 786039973 1250 786038723 786038749
    0x3040b0a2c330915071e050c03060106030b010e0102030403080304020108040c03060f0219180e06010302070816031b030c081b150f180703080a020f16060306060c020906 74
    0x2c02142d46641054410940e4096101c49003014503000a4440c0d0340e1801c90149001400a41070b110303d080394503504c2443c135403031051074a4140c4003814281001c2100620030000b41c2e40020303003103541540e50303120000d01400900303100c02c0c081002c1c40441c0400d0b510210071078007605c3d041700741c0c07524503200c1d5401140d51a50060050342c004082071004030002e5a28001e20300c40c0700d155070300940ca404582101c40c540380354071910a000d00009960500b41500b14910b1901160a2038107070f4a4640c1e030704001640a881010002440c3e80000107440904000c80c2c1c48081c04580a139840b50f090081004a0708881c20300e0b4100607000c83d15510b4100300084d240c42c01851900d500e00701d0740d64a583d10244103403030100d00310039407011045080304005811310200032039a407000c240c0a06500c500c070300b41d5005448034020b002c0540b181000046005074107008001c0720f9540b006482c121500426002d68441c1242d5450180c60006410702e500010542d00c074410f1210b01c140c000303110039619110003003048115a84c1c05 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 786041223 1250 786039973 786040009
    0x21c06080f071e08030c150c07050d03050606132705070210090218040f020108060f0f19050d0b040c06051806090a050303043b0f13020303040b0a2c 65
    0x10800715400c113040c00545001c43d96031004081041c26210f403550204401800742074101070501210000c9200001c0402d6040342d54100081c40e45c4440001c5421031280070803c13200701052403c0011510707030f980c04801070ba10044004d1125504030604078800c0e40e5084e42c081c001a449880c07489441e11480d4803146603988000c05130b8454000800000708032550864066a110284a80440c00c1d541c1040080b517010004844180c940185203001490802e6041d1190707000300e0810015a0140808030700e043c0180c80700400314220200f480c40c25041040d4111070442e03082030407802c00961940500150345001c01c0b030000032411100642c2c10700c2903d410000c1c48070b90046c80c4600004080d1820f00c01000a03124541030f0441c20071480e0306a0107800c0c0308103a02d12850310340c0307402c3c0188043d0301c241c40c9812041c201885035164031098003d00d02160038200c043d40c5804000760010304802c103c0c006120804a946440a003024040c0640503640110360304040f4010442520031050714045484000020041e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 786042473 1250 786041223 786041279
    0x4081513030c2406090506030f21130302040228080717072106060306060903081e0c0303070c1103011b0f031d1015060e040b040204030501021c06080f07 67
    0x148000383c0c2907810561100b100d00303654500303000113800c080c0715501c0000740c99401444481280320450803c0e241d031404140c42c0700d00125178001110380710250b4800840d0014000d40d02c5664200411018003c0c000d07140700c000f4410380d080b90031140903111191048810b600c42c0315000d440d00c82c40354800ea4000700700200700454150004001d00741c4000c5031000c03c4402c0c20004006041c1540a070407118250030a2046c004a07090070000194841c04072501441c054200741c10446003c0d4404a1038001d4001c000d02500020042021841d807207042213071250b0043d1803810b0540c8a100a1608a80d84110140380c407400b002810b000540c026108018501c0302407a000602c40280c44808644501004009083d074118501088000076180101402840b482d1483c507040c618202001c1c04206403400c2c1180255100c1d05030404d5aa030700d605942c011a00103009540e1440c0c9c240c0701450114101a08440061a01c100440c02030b10002e040000d00701e12400400c45142020107851800c40c0092040f1080600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 786043723 1250 786042473 786042533
    0xf1c03050f070206070f02011206030b0c131211010306090203040b0f0603030d2d180627030804020a141e0d0c0807060f0228050a060204081513030c 65
    0x702c4e030080640a02031900351244041c0c0b8030005001c50b202403041c22800741800303c18000b28000f52500c070f8100f802c400f10030b039680c0c0403802e20341c0e01d10510307a21140810305a04562024001700d8100d0f0789015800f41e80402516481d00b849604034041510080d01018800c0d0002e101a180340c6850794000720024101d07410030440c0e080c00401d4441c034204d420701240121a0260b180404443d60314100305c1c52100c140852840b014840d5514101807502501894581c4a61915034044924040400e286500070320303000c0407103040203455004155004c9000c0c4e0021500010804201c0000c41410a0700403c0c82c041d07803003200d030100c0c0300881582e102640300c607154840e10002484885600011b025010250001500c2c00502904100c80c030f140c1c2d5800d541105002c02c10728120001c4800030b4441d21022490080614208103103000d40381038008204501c002404515048001241580c0019408040340340740c0d240c6172030307040303420350403a004010444202000d000a440c00d59480891000f10201c01401c80d9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 786044973 1250 786043723 786043729
    0x18010204121b090c0f03050606120f07140a0305010303021b032a030f010e0609061b07030e0918010c021203310809151c05060324060f1c03050f0702 65
    0x301040000c130204030909403a40c44650513000312035200d90115440303412b101030302c0e4010090800c001d181c0c907414544140000e200c0c40c054050010301d8001119140d4036210741200140060100f0300040d07015100f6007070006000712003002040a0244042d0181090b0000d001c5640c0b218040d880d41c0924003c540098007a5a44040148038a4610700e200085000040e041d82c44e81001d501070a0b104003504500204940804420540f0b60880001e03441261b4500070b505013205e241d01004440d60b0301c910100c06000580c49061015460034420078001c00c5000c41c8914140d0b60b03280d0b04078041e10a140b084c00010304c191351202c03c1100181c03a2005400c0c03a00740008000e00200d134010300480e201900400d0100f41401c1a40881c24903224484c203c61800c07003180404002075400704626100035440304000340c80340d201801403030040c20750140c1d4040324204101d03014048050890304103000740000718a05e0044d1810240010340b0380204481e108040416032030840340e0f035014400c8070440203010820200162 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 786046223 1250 786044973 786044981
    0x1e03090d1505062707110d181508040f0204090b040b160e090402042d0204180b06161b0305030912030c190c05040e0618010204121b09 59
    0x14450080d000700400340e50040c20480c2d01c060056801190481418241c07080c54400102520484043c04881070f950741504645402902c042114039008090030001a01c3c3c001b60381c00400021001c00c40040c81c0c99944009840103444413110006180d0f00108020614940d2803501d16400078002155401054440c3c000421054a0443d4101e070f54904001994100c00070715851401c0900d0302d015601d01000025898a4024102174420350b5170320850070012aa03409001000c0c0a043c500a110030b90842682c00250170521400d450030200c0035402480e4406ca220702030b503140000302030a082c400011a2040f5505e44c410040701c2034200421051074159035207000c0c4004600c02d03802103a494134080280300f0401020110091103038018003a08800d0640400c108080d088032408858200e4498100006106840c2d405a03420a1034040491030307009020500f0741c03041156015440781c0c2880341c01c08900300d200354480e5140003130202c05c1100000c3d40d1001d645076201e8929008200c080d8499040000f11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 786047473 1250 786046223 786046249
    0x803030106020f011a01080f0621030a0305100b030f09030405030a060c0f0207260703024f0e1006060f0306061e050c10140f060d051e0309 61
    0x1583c01038200866080d000d0003546196150395a020941e07480143c006030510901600d0b0150700e003c120300040c000d444121034103c0d209091151540c00700c01c410700c074603202e03400080d000c4000b078201400252410020b4202e181100c00b42000e082c5195a12048580a031001030302140c807500007004000b80300d56041080326030f0b450007810009141d5024070300191034061201d412406640090404100084640c0d000142111860a01014085061454504084823500025840003c0c000280b03200350540707a070401042c003c0c0107026104d00f0004a00b10324110081710f100000c03640c00303c0244001120350015014007100b2811201621200c40c204829900140c1084002842c0c403140c50008640c540150002800b807400c0244c2032003020b000d210088101602c001007030210008052840c07503001c2280c4040006110700800980e45842c584001415045d46da0b402e40036201390114044d458150008600241c1c072100411348410702280c0f16404400c41046c0c3d00042c00144007401054441003421004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 786048723 1250 786047473 786047477
    0x5091b0c150601080f070915020f01051306061a0904090c0518041e02030a0b04020a031e0203010c052107050c070303110609030f22050a2402030a0207050f0a0803030106 74
    0x51070030b0070004214038401031640e401d01030004148883c2a070005550429039040e000c01007074564003d0380591030175017414110910340d8070300020002c035254400c02d60034005114040603c05566600020b000c1078500700e0203400c0d06882000317030160500d000e90044064502c0303941101d2000f5a900001402014508010241010780c0c0041004000442101582044800441c03200c0c5a0781034010030b5581405520052064550f9000b08040d941c0c4d0040082c0116030040100360083d41c075404a0900083e241b408034000c0d828440181c602c0347c0a9001e82d10084031204900e80e4008548400618520020b8220070030300004000c4419181c0051140070082c40c0039032100000054940c00d040c0c90014000c00c250b1294006000781f805941c8103500b240c01c9074420180314030b04442c41c40b00c08501d612180d4403e940c011408580041c00c40c02030b0401020404036118525100c01e051107007a40c880c41510017060058004a80c18446441e246401d00000c000203001c84c1e161540310720310b00d46117a00a030032003c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 786049973 1250 786048723 786048763
    0xc0309010f0c021c1b0f060b0301240e01050d060b0112113424090f02010219021c0303090807060615050a020c0603090115030b1f05091b0c 61
    0x4c1481d81103d004400b0a140c0c90030a82c4000d0540b40300300074a604004c000d2155038014114410b0205a40000180d108000e0003004100b40d105250b201142e0368003611001100c8450000079842d00c02030003e4105d0300041e0003030030b6803841540e5040081c56807040c507905103d0010710a000144080c416030903048003030b21446075103450302c10305111940d6002c034088404600740520000169070b203c010001d45a40080b040c0c80e02c0072940b9400c50114800d61741d8195151402c58004248281d03aa220000700d07000f0780039a9400414014103031316a1032545006500000c150345211070500b03c00c0d0005500e90b00900e0005600c2c0c0c8156a00c240c40c0c0e01803072056507665201c1070203002d41c0c20b80154612074403925041c070070325000c0054006034582400d1007840e44a46070110008821520030340015803051007540c01e4485458481c41e00124545054070042c400c812041c940e084034030074101c0072005950005000402940c0d4100812140b0f000f103181c0781d02c080b1030031301101d10308200070000705401004404940c0c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 786051223 1250 786049973 786049993
    0x307020409021c031808060103082a030703080403080106111216080f0702010e0306070c1709040c02060115020d051806130603020705121611031f2c060c0309010f0c02 73
    0x10300900e00c1600f1080c442d407c000700410010318003808480e244e01c595900501c0b03490218272143d40d914481c0fa010407050000240c00001c05610240c0075100380e21a84402070303aa40ca03a00c0850b100394044c0041580741d44980d0f045090503075002c0140c0f038450356205079090000c010303a558094a07000b401001d0f003120004940d207401c543e00543c40c1d4003400700079001000366280c8454010039410001da070107408003080c0d5024052680101080302c00c20301001e44240309043c55841d009503111024070444911003c0300d51130b0342d0110300c08240b0000c81001c50b0303292401c0c0a00002c215101500011005910100402c008107066410b141400700a00e860b480068940005d410054200030003404009941c00c0e04201c0f210520940103a56042280c0001072001541403140c0407034684182c0110140b0b07034810f0a0025114001590084c03140c000154031103031862a201e038003588083c240d2805403009508514001106242d491000e15807040e689000498100280305000d021140980110401a00003522203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 786052473 1250 786051223 786051257
    0x220b030718050f0c0d022109030a0315060917070f1212170a090201020c12010b01111b100302090d03031d0601060518040603020307080c0a08030901020307020409021c03 74
    0x925403101c4003000f01115403824040c1c000c0c8903c200402c8038040c81d4003140c40c6482007141900441e41d1040c0b454040c1d05810070048060f0b41e40c0007c0304001c00a03080402c280c80d680e40d400c0d16201101e00948030565044d0070102510010020045400c3d1740340304a000001d2948640070300e81000707094440c101e0041110300d007090f01c43c900340e900911040c400c51a860382041440c00c1019540203130a0715002070f5a2101b80f0040741032083c0075500070f901c04040c0341103000e80c18041d881201004401d0721040c1c814258400000e803a20707070541c0300100c400e601e00042881820a2a407000c044102803030018504a0120001200100c4140b0180c000035030b90b40d20105d2003c81c5c126a40c03080c103045001080b0543c50070400170440d00c540040001c4080003980e841c0e06a0f01d580d086030001e154002c09540c2041d4895400e01c0c0c0d00c0c802d109901d03105207030b02c042c009400580071048824424041c0d010314500440e07502800003518005104030381000e5402840c858003056580c2c1c0715002c034404da9541034005944501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 786053723 1250 786052473 786052481
    0x60203190b010203090f040f1a01020d030e0c090403020a08070803011503090c090b0d081206090709030308070807110d08040312020a0c200a060c1a06220b030718 71
    0xd02840a86068080a0560f0300002a54641003045170b6280e86c141c01000410051300507044103040140c10032204001000708404180785403a000ea00311086203116050031001ea46445800c0c40741178001c0700d09000f079801c000c081e00364001e00a0044901d0303050b0503a40d1100070340c011482034501190110041c04440000300c0034002c3c1084d60710b41800307110456114070110080500c510580140d071184204007d485601d091082280c1001060343c032110254903144201030115152442054040c00041300d05001d11401000d6079050742d20310440e44c0c3c4000040c0e505503c00f0340b04000b07103e43d801440026000c201300c4c42da03a02c407503661012002e00700f40c42c02038106481c1c00c80a2201900502018400345d50022000643c02d400c1040107071024144050301100c900b0403d203064005d038540e40007203200c642020010304000d2061700404204603000f0010b0341d2810050703c689600011800020051003441c000900700038a6920f00091a90f1713030715000a20b000601c3d44a02d06030320b40003484901c40c450070300c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 786054973 1250 786053723 786053761
    0x40e040b0709270b0d1a072709060501030e030d050402030336010906140702060706150e0105031c031a0a180e030f041a1903061e08060a09110904060203 67
    0x410346550305c00e0f55180c0082c890b04250208406005400140c6001c1c82414030103440301d01d0700070010005a034900c110210070001d01560b00c0341c1d424032400040c40c7d446032084041c4041c008014504180c8031100c03450103404042c105a070305100501c00c8100007941012150f900c445641030319075013101e205101410f1000742c0b6207480d06008035034008100140d00b001e031209808821303403495a5925210320000d800390017100c40240200b4a090f81000d4020603158685080e1190006042c409a9a404c101035541e00e807008040a142550042544218000d401030b03410020382641940180c0060710116200051540c080042a100400c0c0002c05409501c200d80404078500003540c43d1030400b5010751164131540c89a0b120720103c202d02200c0d0000c070a400e66218940e4049a811024a0888010050075690141c92401280034070710310202c1003613508517401c84070440c0180019580301000e0500610f49900190796220010440c910555a196191445244070307100060316800c2c80d002c60761034000300c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 786056223 1250 786054973 786054979
    0x30a0207030215060906011107090908030108060a020f09040b0f030105160e0a030f1103070b0f0a0906020a0203070e06060903031c0b0102060114041109100306051203040e040b0709270b 81
    0x101807094a4135003c400c3c81d1b2008080c201100025600c4040e41c0c50586194890b10742d1614148080c070422142000542c100c402e180111280c0c0d0311046900b004030300c1746ca10002c02e20b070401c00c80002caa08090300300440590300204092404860781c0003103800c1d20000c5034001c2c0859820807400f26055002410130012442c15100b403803d003404c7d0340e200f134150000c058000c0c04c1c00051800c0300e680ca0b0f508000d110040e00c0305820030350b103030113180ca5800d0464002c04400306c0412851040400e029100240c0c4003c1150018010040503103011440b11880346d02620554104408000300025901e007080240466681400582c008100c480349110440baa0030034031604640010004004056045000b03600c07000c2c00301d8000a80c20314407800541644900440d15030010143c980c19040346800d580610112102038814041480322141826224400c4d4001c3c0000c0b60f50380e401190210700c038290300c91380c040124246402107544460441c6030171b040d48a500e1055140020545811400500911158240503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 786057473 1250 786056223 786056263
    0x5070309080f0c12120609010605070b19060f0b310e0a0605181b0a050412020a1d0117030f31181a0102151308030a02070302 55
    0x65650100030340301e026030b120303448400400c403c2c6040105100c03c100b56489814480d43e16449210310810300c400449010344900c01000c0000341e10f03401a1300711070100780d1110b0416480d545120340000d0242c0d0302900109000c0e13480c0d401061086080c8100d501501d5990301c0b00ea1528000c405140f110320b10341c0e00d195412000b030003d045000c0402e00c0d02d034041d280581c018104c4c65a0b101e09042c000c203450341c002035120440300c1035004101d101c50080380c095464100540c01c00d490301031043d10f00b40318103031031840025020002001030305409002c42c560345200034110344100d0742c7c0b0803d0900d2840d43c5000e02030a408100d00411440c000d480c07081c9094240074015608001c508071400e0a640180712800e4002c0d0765020960308410300552101001c04811485e81400644585004108100008a0f003049600e0803840506040d401c507400c054140c4142c0c0103200e20b00e41041c1d4012004005080e80c034415840001030340004034100c02035481800d640d400182c4031502c5050003403504500304850b4241c9048 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 786058723 1250 786057473 786057491
    0x5030315092505030c070b04110103050601080714090a03150e1005160e0609120f0f0c1c1509030201020a0e0f240403062a02030a0f200f0709050703 65
    0x10181800001c20b142e04205407603680d00b995807501c900c21400001c0c2620300030700401c0104801c8408510700400e0a1b42c04002c542d0700c90006585103502a00e400d0003051190054216a403a141c00078070301c2070030150000c10410342d280d40e021640300d43e500f1482003107038440503070383d55003001009140c2215444038010320150410070307002949000c4403140c980c00c00c03e00d10385000031078842c58101c64103100c02901c0d1440382080440415207420f04d4003c60000741c000e1480d903140102c80050440101d110062030030022070041042291444c0985108450b083c0c903101c612a01c00f605071043c804041c0c00f03500090395904183d50024099004261082d100b819100d40c8601caa86461420070b0198599106681c0160500d850f0060350f400f46905c000c1200e4100102c26880c1700b1015131400c107006206046200b0031010b00e42c242d0700c3e8014404120000360340c4107117045030030f8441e048018003207106217401034170070302098030b082e0134400388001d5090a640000810080d9486034410030760310403080e140800035506 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 786059973 1250 786058723 786058771
    0xc01090e0606070206070209090a1103070518040606050d080c07170a020f0a120807060c020604030f030f091707030e030106050303220e1906090203060a12050a0503031509 75
    0x603010300310601820000c2074650454450900311503800e50002e0500c0210b142c1508031542d200c0d603035030040742c1c192804540d00109050000e407203010b41b07c1c01000108001082d0700e0f0079040031700c0200141d503230545402c0001080c0e00c49440480f4031500403015903944007080c1c40c610b89425107541c0032440307403001010003440c400e0b0003180c01490076604440c0358503140c641d100001d00140c100d8018002446681500e1f00402807690010a1020700c55001803000820005050340c031450308590240c0400e0b12045030320301c414407030352000c010001501400030390000da503120701d0b00255452440b100c00c0180015040c05040d0882103000390004220001d202090810010a03201c4c06011416120040764141110402c3d01d2280c00401031300c801e03210581d01d46006100950118060030908030610700d0603034041102c0c441c40c02103030b01c01c04000c2c080640352440d103540341005007003039007041d1014013924401c13500145050004500400840492103485600c910810210181c0600004036030391001c142612130751 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 786061223 1250 786059973 786059999
    0xe06041205041a0c0715030c030b030a050a020603041e03050306010813020112020f040924090903050304020609031903020723031c05040902070b10120f020f010c0503070605090c0109 80
    0x26501c01c0013600c0303002c150545031400c01140c105210600200090706c0c50f2a9059001c081650036a070307014800184410181a190841c6800180660b000140310f9405810070310011600a881440640e0b89a1408083c242c0c00d95900c28040b400120000b0038030505690190b84180c00c0542c094500a03403012990000e810084d148860784442c507002f06100c02c100c101c0e0030640d00103049c02c1509000344000703060700284070f0513240804198000b540401040e000c0c0300b4405d43c121282d041e01c4903490340e100c82e000c0012580114141c1d5074103210341003002d0f20400540f17036114440741c4250010312015052070a54a50300403060200c180709800f80c20321507281da4000031034410800640100c00c00030f908038007044400741320300d810420802d4000160281041980341c1464881d5200c3d5961030b80e69502c4541c0b1035240420900003818825081c4007000c05407030100c04040241005060582c800207190740c1e011b0540c3c005200076590160b0301c504004003044140301d0002405024a0090040d40c00d0041e600488 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 786062473 1250 786061223 786061259
    0xa02070e0108150708181b030d0206091018051006050907050c0a0f0620030405011a01021c0302090d05011d030306030a060c0c0204020f0310320a090e0604120504 71
    0x48190707008100c0c80d81b03550040210606805040e035801d0042001890f09420081d50840d0107441021000c51142d480801c1d070302c0c06154004080c1114102c06601d80c0c020386054810451107100c0ca00500000a0042151a03100101e003000407654078500f20810500144c0140100140f0808004442860002281030b2410541c4071103c0b11100909042c20b0004000400c248d51801c1404100400d484100b80003440c4600e10610091040c814100c00c40c071141c0c0c01100d05213015034041c00c5015101c00c140380e0601040c0b015813500504240768000002d5403880100320560700b03039654003110b81c10503420b0260002c40400c06030041d0701d14106000401e5480c065201d014240f296141d413001d06062040c2806064580c0050055440d42100400302c2010b610544030a01165041d071000501c8482d4000102c1881d0760344c034103981000103a915041a58440381c3c201c2ca40c88142420041110b204910802d01000ca005008000e5464645010060103181a1810041c04421310042100b2007520f0b48e9104c4c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 786063723 1250 786062473 786062477
    0x100b0f070311070f17060106020a170706140c0a0311180909030904090305030a0c0206010503030f0c19210c0b0408070807020a0603051f08032506020a02070e01081507 73
    0x102c903001003241410016000b60303000100860300004c00341100b07111003a40403401c00588149903603c20f0240e90791440040020640420030300c2c04003148103014060b04405004e81d40201d0000c1004600d04000481191140c890075004910340554030340c903104890f42048200401441c0c0000c90007a81c000d400300f00c56591041c00318400154024406009a404080000e841489010703920300c1d0141454100b00c1b51200d074645402e003880d03040741c030000300d0074100d070006409140f800605410b101e44d194041010703001c0a11480c0c0040c144140d605202c16003050242c140c4103500080140c01020040b61043d00d0020092400d540c000440d240074000382d00503500040c0180e03142c200f0b10700a03a550090b0765020b51311034006480003900e25015001280318500019404050000d61841001108864024900140d0040c0142d144400500c503280c541c80103100204003000b145d0743c0d2032500b41d0b408220740c60700580182c1c01c204000c800104c001e5015001c84006031030182c1707683e100014420002006801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 786064973 1250 786063723 786063737
    0x603130c0f061215150c0f06091401090f1b1a0309120a02070605130b12040606091802100c0c06030209090a0b0d020d11031b0f060a0801060c0201120c08100b0f0703 72
    0x2107006c0c2281314002940000c103545914503d06010b80200460303202614101c00d1000403840850040c032400000c03592201e50760803000400d45544400c00c00130714000106090705a00800c0c42140e0082c2c1858000f0401c0310035135a440d0104040381044240c0c0543c07104924103001d120b00742a00401c0d07460070b0351120b20b49242c41e0550a8181000714505500100703884070000303504060105072440c1548210302550b010f02c29140d4600c41c110850300e00528400b800100001d01e880145410449800240e003a41b801e0f100204d000d46401c1014034180d0710400c04a5070004e5640070609003800c03140c1d800103402004102c010084404594440d401c084004d1145485800da14204070113100115002600601101c544c00c048180151545024031202d6100e0b280c0000743c1c004900d40314003140c900441990740d0321840e0f440c05c88261002500301500302d0600004d6804884440d007144100d0034010302c1580d030313542130741440b10503180b00103d95080f44180301800c100280041c8004001c5405141d41440c01c2c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 786066223 1250 786064973 786065009
    0x405030d0e070e1311060301120b09031b0723100f0306030804080a02010909150b1602060307080402090a052202150f0702190608060603130c0f061215 66
    0x2e052900ca80c009203005100c503001e2100142d0080b00c404603491003045035a01d568201c2040080c213000900c2186212043d03807000800041d403000c6202e4010b08004103d038109480d40342e0540040700205034400c0c10303034442c2408212144c22680d0203600b007003488607000c042d1041c45000c104101e820310090b00510280490344921640f20360700450045401c000d1260710b542d1100c51003030b00c540240d00c040c0e00054010801103032214191081840000c00c0700300001040d8500000c000c11600b081042031814001d40d01c08002686070307000210b10035410b69407510300a240520421480c60405800600b8241c5083c00300200c2c85540c0350002403101c0b03102e0140c064801c00b0700c0054240c401035045c15444450114140604044001c090031249200b1540e404c1c402d120595610b40015040c402e10000402c100c000c68241c4c10b02d20011500300c2c0103900c44002c1035145407243c048007419030780400300161514a04005140d444140c0d6a03403001f0304102070060321044402c24600c0c0103a030041511403542c600540e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 786067473 1250 786066223 786066251
    0x120c0c151118180108010617010626240604060b0c060604180203030f040501020705011119170316110d0c0b0916080c04061a1b030f040b0c010605090405030d 69
    0x141c1e5070385807403200445544d84c54a00c4c16001e003409100340210074407201c000c203007108418020842074070b01d04156140051100c0040d083d00c107040c0c4261520714000c8103081c010000c071102450386020309144041840d820000305000440b491030740207200300041400005453700c1d01150568109008032070100b0065141e0400f00380c8080000c0c030095241c400050f0701040681000094401c5030000d8094401c01950b401c01541c010043c407034451100d400140800c80e40c420100345504513140500d40301e41c540607140c92009e10980c400d482c90300340905d840483c0c1c0d19103075120000445c0e0215041c058800d01e11581c03400341940c844d8403002403030311103000d001400101c010441104840c1020103d407400310350399900036071505040150039029500b880000b02e070b60485100ca03214001da0070b94450341f0b81169510501c4c112400c00f12a86154001000891002108130014002a00d403c0c0318413540c81c1d1025005908403880f42d40f0150083e4140c10801020810205c03d41e411034403044c5000c500600341840e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 786068723 1250 786067473 786067489
    0x1505030403120c02120c070f0f03031e03020d2409151a250b0f010f0504090609020402180108010510050f0d0e0703110907030b06030c0901120c0c151118 67
    0x1003101d026004208001010000500141200c14094001c2500d9441d8100c10714030300b0080c080980401c3340e000c00408164101e200e1809050360520700142003841c1444000142e86414402c0d041c208030007000e0042c58014600c000f001080015000c026150081d500144499082d200d0744030000740d000a501010150713141107030403100ea080310188c2c400601c0500c0d0302251003400c509580491600001895501030b04100074141e880c0e21043c202602d1810081002900d14600101c3e45117450304a50001170319140068042d4440d441c070710024010b01040010800c0c01d050307000030312552850602010441d088812900910740d0456116643e544a02c3c1304000351920140411480c40707034601c0007042c0407a01600c03441401c0304584800542e07d4582d001c0341650394894003035500c41d8080002ca0141c145d9200104010101030408003040280300c0a0441203034090303082c44000c00c41200102c401c004480c0901c20760610110b204200c00c800442d0304003158068041100b1480c0c03510003200300b1590300c1f060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 786069973 1250 786068723 786068743
    0xc0915031104051203131d270a05060106110c181b1c1103091c090308120a0c020307031209020406030f14072304050a0b0a0f1505030403120c02 63
    0xc00c1190400416800c0e1790b81ea881280050350400ba007400c0031414071071625110070081c0036004c204c003c0e516041545142c074003c1000c0070600f40052080004c90300400c1c07000526060040016005640c50b1004c064140c695004a00055400092a2194640d0342901190742c1c2104650074031240d65900101072941910140945014500402c040d2401000135015100d88050020180400c0c202032188003017a00040d103240410f80c01c031560443c40d0591030a15400e42c0c032050700e0180845981c9403038140c0140e001d0220569075001a00c10060b0010040c080e000310015244000c500e40101518010101110054004001c58682600078107659564100e1405140c201c100c0c52110b0460f45001060325600a02001c3c95019255000500304050b1040010b403030b91030380c00301408840c4001000000c200040104d010142d85040101954070399090a0b0041c200c51140d03c560582403075080420742c5140316510341002810401c100001e84e01484c0f43d8905c22500a010802482040090382043d20f52a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 786071223 1250 786069973 786069979
    0xd030b10020c18281a040225111003060e09030403051e01060e01080c0f0405060303090f0414010b030703060e1612090209130b010504110a053004060c091503110405 72
    0x1d07a4001340c0b806607110b44082402410079400104014080c030041e0b010702c00c0c1d8000c4c014413132110014007450041d030700319409125070038101c240351403000024107040181e068080000e40d00c4805101c0c01021003d0309400c00c05280c01035050502d965a030582c1c5031494180b10054240300902d0400a517000d402c0840902208222003c0369038681030f0459842e90b285807510321601f4540854400d50030306202d41030064a018014520f071038002418800007a000300f5415400075565240e205014400c1141a030203400c1c52010785690b420b01c58001810307900300d904042462542031092180304201e81095001000c0242808001070000078442e0004001d0390b20007941001c02102008083ca80c01500b0f0f490241c451708080c259640c84100f4081280d45070075111030b098408019452865029101525080208006140002804002015890610308100951613286000703010401126024075140040149009008146041010000b45c0c0c2e20002c090f00303041d0385494281d129200340040768003800000e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 786072473 1250 786071223 786071281
    0x30f020f060411040c11070b0a2001020309060c0412030c0318080606010f0309080f160f06050403081303120e12030c04050a0812030a0506120d030b10020c18 69
    0x83c1080741c100d411403070090b0300c5a4640b100481c03419000303c006a00305134010000344445400c00e160483c0540c0507007850024441c0703402c0500c81c0c0000e41590342c4404542d070400542c681c148948414a08900500349407071801d804c1c0420b101710700c4c0c0304068030702c507640600d00f40342c00e1078050606a50701c0e0b0742841c0c9503404141d10390340800c1c10000003500c00d004100a0741e881510b2050071500701e048a180c81c00090451404122100389001c044c0c001e0005928417120100002c41103503603150b008001c02d0001c4400380d85900410060607001200f0760f510a204943c0c201402c403840d41e0080486403007400006d001903851005656860381000041024924176040644d43d0410410314101078101c0c0c171400c0c0c4240484e050100d15244089100a4000d00300b1070790314155196a0002c1000d0322008051580007001900004a100020043e0082c0104a901e00180c00c81c1d0039403d0042031540401d5020a6500c02c1e00c0a200e0341d01c840088009041110904101503100c2080c0c0b580e803010007031044007080b802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 786073723 1250 786072473 786072481
    0xb030f19020720150f0904020c0106170703030306090902032e0e07080d020c0303030a1e1a03120406021b040e030417010e01090f060213090501090e01050f090a030f020f06 75
    0x2042440c01e0301c000c089520101070654030344c2c41242440b4150000380000c00a20000f481414030f03402404c1040101c1c000031600c00d886230400c86c031200d00c0500c21440c41d408010b042040c140c042c4580009808200d00c10b000d0810142c000c00d982c0d90010ba1140c00581c5d000511548410443d0304c84014000418828000c6420682c1d40b11350328803580c001e080f1140908005032051034000a0a40c0794040080c003d9410f5980d0b00c0c0f1000300034407144403030445161500c07000c5d031181c003c0d42c81413510501c0b00c441c20041c42410b0304c041c5450404907509040003003034200400e100c1d40e900000c0320500812038006a800141d07080d0040303400380080860000c03091001140c0813070003406e00a103490072034404100800441989442803800e0741d00c1020060b05410401755490045007254005213121403d0b545541c4042d030365920050200c85090303000e401e5080e074580000850000a019150b0400c0c00c411000700c0c54186901001d86034100c0400050074001c56940c161039003402030100e54000d14a40040c0c641c0e5142c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 786074973 1250 786073723 786073763
    0x3040b04030b06030a0b0c0309031c02220305031606090c09021902071401050304030215041506090504020604050f121009030e0d030207061d060715060b030f190207 72
    0x180c001120401030200001d0f10307078100021a44110f0b40c00c45410500f685610300380c041554400341015030039000802c01c25045000c2c1e03103911000d84650031401a501e00e0007a488400c100841c0c06c0016900c05814400c001203a0000143c81e5012400c50041c81004d40501d015001446d59900051034104021400110300300e090340684a02da1081c09044210f00700075004a031140350740d0040c41c00602c40d058411005501c613902550f0310600c40c0c0119000202da4902c40c0081070000c60303040b2000e810501e0894070b0b01d02c0a020b128003c00120106100d80e003410b42c0012040d0080e8081e4600483c070080c103142242daa4449041501c030425030035501e02141815510001d04200d81c016000309079181050300e00350410b4001c0c0289140c041d4080c10000d410402d0488812100242d80c03048000010940c0030240d80300d0000300b880c0d0344035130081c035842201d0823101029030302c4990010700c00400520400407501c01100419030b2100f503000200220a0480d4a858000e024035207018143c0104440e2001c0826 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 786076223 1250 786074973 786074977
    0x60e0a0207170a020a030f0516050c1e09061003150b1e0a051b07151106010504060609090b0d060603052d030a1d12031b0304062f03040b 60
    0xa4000c1d0301d0314420000c02c6190a19521aa0340c0000c0107a00800c443c0001c41c0c450b5041001c0c00700186066458142c99400c2408244400c42c81078410760401005503005140c0704401d100d40710b041c00000203d43c46680300040c84454001e00302c0f80645a65114540e5940c480c2e0700115851108039000c1e40c40546580c1510300c035401c030001d06003080c11509124510301c00c03044103a8000540b10794a15103403282c1c035245e070001c0b05684807003081c0c940f04141001c1000882c5054801c1c040050755241d102403080180c003245004010391105004a250010030f0114550188014060f180302a2010400d440b0800101d002800d0300c010240c61646018408410003c000c01c1e60b520742400811b0740e180c43e03586945e0a070031505544240c1c0385180d004004140041d03015045a0071f126405010304d090f095034500200707010000c200152406604001118900040c0c0c02c03103040385500106000b58140b6082c28009001c0b5104098442d1203c5a44004900385070702ca0440070145404007030076291075a46d1507103904815 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 786077473 1250 786076223 786076237
    0x51c0507121103012d030803010b0a090905090303011e090c111501050a091d011b021501030210031d0a06020d060512030a03020903150f10050603070e090a060e0a02 72
    0x1280c14580081025812907058074103940003000d42c41c01d03041030340039000c08821411070f400c0c0302d17407003c0d41380000480c1141c40694000d02801513030b03650340d4108400081100080f60099404a0301e0141440603179000001500c1c15569404086806855000b100110b094400d80c4200620390401500141c1e40e030340421204030101e81c880480718128056010580152000d001c0c03582c21041c11241001742103000d4124550340103690740351801810302000803609580001e07203ca9001c050360802c41c0b816a80c10044034290400d285910359040d419580052446c210242022003055102c000f1f04a444a01c0c2120024030030a050448002c02d403540b410001039000208802c540610740a0001514100440b8008004c502e02d00a5854490702c5e981c243c0003034111000168042c883c51202d0360141510080f818000c41080c0400343e8149042e00003214401d40c15003089024840c140140001190000b24165200d20120b0f1292203a9407150255002803501d0b501c4000c510503150144144c0c00c03000e034010548 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 786078723 1250 786077473 786077507
    0xf0803250e12151f09060b030103121b121b0b0f0606130e07050702060d0b0907030b03031803100f020c07080a0f0609080412030e1009080d051c0507 65
    0x84002c1c03080c1da203455040700200505034483c500c0c0014051002106400c0e041c074141e141c088101a16404450226107041c2c2100c01e220700000018400d00062440428840800345000d80444d0080440e40c00000140103004119145040b032054083c0e000d2840e1109403143c00c0b0865000c1c9819003003420b4902d8080d2203545a62403001e000c640075081c40c004417064884110580c0300d40d14a8880d00b482c0740310006141724200705013441214016500d4400400700d1101100005c00e030820b42030100a48040054111420726250104810031503e010003510003e088031604c0c4091400c071100428108a20001c1188043d854841d5980040307010b90b01804a0388000e00841341d640d6140c0d0080d6036034000d6a2006009415903428010001d0800d4011182c914840c4440905048d0b035034001a404649035a4105d01080380041c0450407410118002c10190a55141c5041010f02e40040d460315040150480c0341088000254811118a50000d029021140742010040c0340b40c0440b0040108d04034581240c0c2c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 786079973 1250 786078723 786078739
    0x31b100c020c0f12070e0412120606090314010e010203072604050721061508061b0316030b06070c051c0c170f0703080a0315030f0803250e 61
    0x40d0345100050a26002c8406860106503541c0c2c4804c0040d01d211508001c2c58901c01c0007804240203400800b004c1c021803044811410b8180c082502402d0203414414101441d40f4294040010781c0e8481046c00840e0340101c11502e07190030b00c20002d4003420b24208051950742c0000f0500442540c00100300d864000344c126000820110b40e018000780100c2544c002d442036206410521400c0c3c070368086000004400c07441c002c400750665a8000540301c2c8a92894001c03004d102080111030014060103901c9110500c4c25881f080d002c0440100500009d00f00d51105040ba1440300328040c0240e00008030603c0061030f031901c407801071504a904030502c1c00303164001c503030310000c410a0844885074510065070011640b41e650b41030000301d0511481d8403424841e10b00c500000903088038014030441c00614014a0110380c0d401c01d90700b000d4140c0c2c446440101003030920740c0301080401c0108803001540c40e8046242d55981c4c961140307100c000460035800141c0c10325009001003002c1d80103008850900825034041c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 786081223 1250 786079973 786079991
    0x150e0a031112040503065707051513060203150a0503060f0103110d060c09060e1203031501050909090606010e0108040f02150d0e030405040f05010501051b031b10 71
    0x8105003e140b19040d09980420042088a07807108000401c0300000100180c4051111525000e03804036180c0340e04080d071545000743c030b6030340707603192070101c2c09002c1651585031449075910703165203a0006d4280c07001c0c2200070010030071080303001065000342504a0029505ca080c01c10341449442c07000d141c02d603c200e40c1ca410018082c02c001c6400e61064642c5c1138070104c40da10316100c2c8004118031a014a0740b1088011405000404a1040c0d0481180c10b6541e5101d650409201502c0181550507480c404d40003d956007032000700010880350f00001e21742c1c9080403003101c0c10041c1c4460050783d00a541c88100001013000b90003000540d04d201d01402d80c2e504051541c0c00b0010b48100600782c03805004400c11301b8400d0f01600f01400ca030311010a0042105141846003800340342283e05802c070320741c215080083e0030881842c003406011030803961940108015458100080e189215070740e40200d650a403103501e020000e909100340c41d01c0c80030414000340d0a0034032200f035070b440300f011840756906686091001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 786082473 1250 786081223 786081253
    0x110910021207200402070602090312091e0a0306060e040506131104020915130305061803040e0c130303050a1d010509060d0e0f0c09160c150e0a0311 65
    0x40c075510660086407500d081d000b42c8500d00c0c81c041d40764608008020442074011244c842d440181040c5c0e02502005032210807100805003003403200300e0445410441801022020750310414121380319110503804031092144140460b0540e002940040c0c2a28a4a04006070340e00940b4a068821845007007070300c800c0e5694428031780c0140603010001e807242e21f20f1184041d0030f00b0f1a034001c10640300001c2c0880740b40a0a41045a116802040084e4000f47c22020030000c02908004054004405829404404841038503240c1e6a00441c0714a01e61500d03413001081c4c103a80c60004a0301401c0714841100d464036124200a0241e80c05481000001003a004071442d000c0c0d80707566003403c1c40300160343d003030300d000d410408000d203540200c0702d04812141d40f04d205003401d80e01044807641c0c2904101c00303810100e84442c03c0203a080001041b5070102d880b035815044410754404014207509501c042e4041c2d568002442c01c00042491884903a09071140080020605402c50a149941c00f003034001c03a4801030f45a0f2517 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 786083723 1250 786082473 786082483
    0xc0b1c06060f030207020d021306060908010207020f012102030c0a08010b1801030b1203030f070f02070e0f1b1201050316051804050319030203040614090303072111091002 75
    0x981c0700001e41c50090340d80542d200350014003521780020100c082000454002031101d032044265140f5050755004100800340d00300e0071b01c00050036104002c505010107600459054104c040000381000028056030421400440c0b10820704021800119100c4c07403c0c403e00502903210141000219040da0000540000070004403072202040a086030000201a0015805401b06102c2d413980b000f41b1487c14089030800b0001b0398403c5d01c0b2040e011582e400d001d480513214041c6151180c01319004058103200d415100d0815a81000304009242038603524411402c00005021b028048502d000050700e01540c164000014103a0340203d007a503020f40581c20341a05115828490180c100c0303145002d641503071100400d070980c82401030050701e2900140b0002d01405076008150640403a5001c0203000602c1000d110b441d07582148041c9034641803e003104125a2800020700702d4082146409a840c601c140c0410082080c0a81480c14080d03111450b01d00714094104862283c00340703600a4072810110300c0011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 786084973 1250 786083723 786083729
    0xa1e0305091903272102040f1401061b081809091f150914040c081b130905010507110115050f0d0305070b0a05150d050d050904090c0b1c06 61
    0x80300d070110b13402c06000201c034692940503103404d00b041c6100000c81203800703460400301044a24142000e028a40704001c100c420f14201d0b00a41480c00460031703a0500c034459110b054400c24184403001e007582c0c4948041c0e400200000410103070000c40c25940c2c48004a09640d604001100c0d01c2545549000400341e807640c0245a401c0c0310180c1420b5202803c040354048440c1c54207a213610750345261030700c1000003235171883d01c1818062441c00c1c00300302c03d101e00710009402818003030000c0d0805881c81d41c101d4280c801c244104500c00c000740200404248003d40c00280c0300382d13201e00207000a00e0300300405004102c000d84602070650030320310300700c02c402d6854003243c0c1500c0c40200105003040c03a000038007680401c608001c82c240305081001d400402d021261a070711a00b00c40d0f9007c00c4074604a00e60000c0c51405600090013030100f10b01e0140011004a80103403074403a2032034103503260f440e0b000014020300004d05018180004c9030307802042c1c0c00ae2100040124014120b9030f125a4044600b05c1022281c481c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 786086223 1250 786084973 786084977
    0x1e06110414040e300d0905210403020f01120209090406020409110c1e03040b0d0606090501020f06150a03060905031201170a02010c0c090218090109200a1e0305091903 73
    0xc11280504d40180020740840c11807001d5080030000c0190300c0c00c5405100003a50150701c00ca80302890200001c04030324002000e40a41400c0615540c0440c03a540e808084140c1803100803420020b8050b0031390b05507850902e00408241035810141442030080d405030040c18040d40c2040290302c24144144103c840c6219800300520606460420400c0d0500c00084010014002000001603032040f950141c09070240018002950518184000d45001c0c0103a0200341550803946c1040c1070f04802142c41540035071103442050307000702c0802c001034000003150401072407a80b50620520a02c040000500ba50501c85000c0203580e98a07503c00401c401020300c1c240f03445d5445180d00d90019407040c000359088911950301c3d1880152030f200daa60aa070809043d0f100d40043c55084a1107174a8031031030050052401400c00c00040c1c7c0904054400000c168103400308031800003071083c804601c40e44030700444400b140c40d0f1070b4554848400083c00707010240c0d85000a4072600120f40810b686920321100c0c0c041e899 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 786087473 1250 786086223 786086263
    0x1e0f0a0b030a0218060408153102060c030a030b04050a020c0706050d09200a0b030112032105010f03050127020d050a140d02010e010204031e06110414040e 68
    0xc50344000281d4011306405199084a0055030026210075016201900620f00503082e0040c141d00c940c28140340003080328010381e0b1b604110b070700c4850f8110359980030200c0c0d040d60211240f2150001c104a0700c105d2207000c0c110300c4001001006140d05510080117000300703c40038000d035203554814400b68000d08070302880030340101100b00401c40c001c40c0140079103d4254004035452140e52034080391465000d04940c150003610742054814980794400740060a8040705060955050441c2c01d2498586844010305100200503c4005804200c40280c8203400d00d41051280b5a101c0100119581f401d1100719107543c2080314811411602c2c5202c400b2404900070003507440c00b034903020448400c010b00d4041d2200c0c0101c0d0034410100d9140700c00c20060302b000c01d009158000403040001d003103994a404624580c1d2040c0014030010340c01080a50304a000c401c600c184008940c2003010080210503040820440009000070b940070603c1410340000808460800c944140c04118540b00c1907509040c031b29403c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 786088723 1250 786087473 786087481
    0x81603051507140a05030f0906220c09060f0501020f01091e15051f0e0423030f03100302100c0c0b13081f061508010e13021e0f0a0b03 59
    0x200c001c1550094261070440f5003695140200740d09540b14000303110004030000300b08410f007004c4101c0e07990400c10040c010203c600d01440d810710328182d0211380d0607207075444541020520640344001c60140042c60b004208040d507800710128441014460310f0301501605240d0b40c07031040107200700151a5080846124a000d0400c1a6a180004081d00311900f14458120840d08103507841154400c0c1d280c88130b0119510709500c07401782c1801c83e075804001c9d518803400800000401c405900103405888909803103a946c20700d0000b90450003103501c00003042d0004810404040b00a0307048208981c020390703280300110204502252480100c801c060204140e040c0f080200c0440140100007050801411407031050f10341d40301f10700782072520295214aa607151000b000d424040d101e41802814a500440c1450750a044090606001489039000103543c00c40010b440220461299034803d0340205071011040100264200300c0010342d122a014400c500803800c1d050610405050585080b4080142543c0c2c07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 786089973 1250 786088723 786088753
    0x21515010c03030207081606050612070302120705091005011205090c0d020a09020d09051b01140a1404060503040c0e07020a0b060d06110d05061c060921050408160305 73
    0x424401d044003050f07800c000003004580a50003400c91050a03400000e0001040d040a50584038041c0c07004c0c0c81170b03010358a089000c40f0002005021680e040e6820221007031940103141c200001a846030303401070a035808020042c42e55500c0c0f0802c0e07803004d0302c03052201c48032401c0d42000c03541c00325000071050b4002c084803d501d10f02110020720551000340032a1400b0780f2a000003003641c0051408115854032811180100300050160100d10040300307034801c100703000840000741140e0390100c0b04c0200c07040005040282c5849140d524444022010701140d0340d84d522540280300c5d520480b002d5501c100c00c054041110303040c82d0109801030350310b0760080891405540b41d00d100c00001a22040d40b1101444413000059864001c50403103a40c1411171035201d004066000f070a0310001484c80f842400305458105503000c0e9400090b400e10f8111800280101b181d103000307203041d0352240d02e02d46840600d152181003070b54007100510564001e0807c0d19104a285400f8444030b0071540030040c00c40c5c1240b01d80d107003204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 786091223 1250 786089973 786089987
    0x1060f030b0402120d020102070c1418040c030b011203030e060c0f180316050111010b060708030624030a2a08061302070302010204031a15060d0b03060a05060102151501 74
    0x20380010000f055600c0000c910382d14000b544407007600948d401003220f40a20128244040003032104400c41c0b07000785090310005141d03042004145880841c40d2000c9030502c0a103424943c080c60380712111804550311034408103c2141030410071000a410040307401d01c030610110f00c85010b28580c040c2c0c0c41c10854482c80f40c1c0071540014841040e00c0020b94200003803035a080101c3c001c0302c41c484211854075401d0500041c44030904c04c0c1441d109038100f603003c101d15148d18044411f25a04a07107a15100e80702d8000007901c0c41d08030104142d08845411030b200084800b64011809007101c80300410071111880c140303417030189512444415107031000c036050800a001e640d14560042000f0a071412804240350a041280c01102080d030050303602040c10f104000111080c442d170707440304420001586c0b90000f24242490300c10300c3c0140c016500416800741c1031000741c00400d81e902008054610903d0200544001403500301d440900510441c141c2c45001c1c1143c5080501544254441c031009002d400015181c1c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 786092473 1250 786091223 786091231
    0x14010801060521180106080f1f090210030b120d1202070609050609060a0b040207020319060b0a12151103040b151806090901110406030f02130b040801050901060f030b 73
    0xe0320f840e020300d4120300c00c000703201c030b02c01c04e100440d90314180000b1402c5801c5940c07903000400c0390303440b15007107602d4008001010541418234045005200300405030381009404d4020f002900203242c82d0241244c250517401038a0501e0b41a0384203074000e65038500749560740c54034080c0382000c03d03684034100c910610b498004086241c09a5001700b10102182ea03042d2400360101d0b03041030190800000d1018012450140409000c1c4c2240c003903041a0040d00081e40301c411801c40c0c0400350184d03203500820045203070000f00c2504001054060090343d42d001000c0700c810543c000f140c1000e60554440350901591081c41c03255420f421403a0308564603030b030396110541c1028043c90b0104040003028031866540d60202d035100c00307215154060504261090000b00e01c070280144415034100408000c692035904240c03000c0b200f04d0f290214554120904400080c4544100340b19401e82e8000040ba140300c0c1c50004104588526008000c070b82d4400c0501401c8880d14012685691407030303034080000c031701040c44803030300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 786093723 1250 786092473 786092497
    0xc0f1008090109020d082215050319020c0f010506090408030609040c0306092001020604150f020910091509080c040b04021c06150201110a0807110f010501050406140108010605 77
    0xc0741184c001030b6041000440407209280006983e0400050040c25007040c030083c10a1099050705001209494080619644080000c0880055400b00501c030b150541400580b000315540c810f8a07101c1500c0d191120b0240c00d6660038880425003505282d4080c0d407046412503102811612a101007002c0c051014106440c0c0000441011011540303038817503d04114815404400d0101000d03100e0341c0340a809100d02815074000310104000b2070020402c0c1e030000c088840c00080c0140704501e00074000d00038021b00035040141640c0400704142c1000e0b410041da19402904101164881d00844074446180503200a580120105038582d003450341001040f44801032001d418404030100404815000d205c03c8100c4988441c4100320b12846080c102825620901c0240400308024000d0b11841c0b150500707a4041203502000250928451107145c09400b048505a900350305c0c48141290280000303001d080c6c441c40c0343c444002740545c8107185100e000a01a1203841e6203a103014405e440c0360300542d44c8945 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 786094973 1250 786093723 786093731
    0x60106031805070e0103121b0b10080616030b090405150a1d01090b090f1e0a02060d06050a0b09180604060f03150f0203010f030803040201090b040905090c0f10080901 73
    0x21418072070840a840b985081c138080d0340c5075081c81900a00004141028006840440300181020008900c02030350082345104040d00c0300c00b070b6210000b14640c4481428010402070000109405413090643c03a0381ea68184500302800042204100050312700070404e512401d6030344560020548180d5102142c039400003a40090b8000700c03894008845c0c0040f2169550310b14030400c0065441401b500f04803008000c110182c000d401e01e0740d850a2090301c40d01c13a50080c507080981010300700400c00c0360f0365003c0c00366074488010244942c0505214010584141403011022a41006400c00d80d517201d05c0040055501418510648206410240641c0c4d0842e440b07030004914070451098a1000358844c143da004c014805035207140443d03c0c0281e14041d2103004000400c0030725001055981a40d030031001a13581e90303c031480180c41000003944140c0c01c1140c0031900288811865020350b11449901050340ea0300e440c501c08006140c00c1c0280085d500c4200b00550290039131092803510303840005240006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 786096223 1250 786094973 786095021
    0x10f0507061113122a03020609040b15190519110c040c0e031002030606030f0a0f1503140604030f030e010f0504050706090b0702030c040b040212040b062106010603 72
    0x210000404c1d040f00344240c40c001040b10400590144006440113401c009500c5101410024805086148806803040c1008150840581d481d54003400030124000c0403003092503841d0351100842d82025a5411090b0f001520f1030841c503005070101c0d621180d92000c4152805100302003684c11a884e640020a24805e114040c2d086d51611300c00c0c4004042e250f100c1c0710721010b210041624200710031000c00020350051091110710f40b100c2d4107403500015000c141060b02da403504284001061426a00e400240c10041140302d210007881102d01500d003e0b418000f0440503528a00e40d540c841560010f000584c10740e9407946080c829807104281c443c1c4103001044901d841c051030b205031241a142a1090f030480c1004009982e0001d00d031400405242c0f007411706113000380d00000d44400410072038034081c03a1a01070440c041c1c3d880b83c0c12105e45803800d41504802e42080c1c20700e284440000c4170924000d0020807209000a0b40100c424000480030400812140e800c01e64100e010303058002c0039010071010226070b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 786097473 1250 786096223 786096247
    0x30807030b030a0302030301150c0f03050715050c120603010c0e0f01020f0f030904061509050607030e0d11010f05160813030c060201051f0503030702012102120411010f05070611 78
    0x43c40b9181c0243e004585035414001c1400c120451060010107005006a42c900004c80c101c11101070b80340c2601308952113450030b05001580c4462503801d545558a0202044007562481010703004000c0e00b004400c040d90340d101c040c14200c89840c0f07413240c0443c06582d8804403501e40001d486541d883c0600c1500d07428500321044d50325101c6000326100c034613000890300a0f45800c2c83d110360401081c110034003010040c1c12000117031008495000f218003e500014141c402e26000d01c0401130500e0303018140c0c5c0412041c42c10241040030000c0000c0e40081c004030f4442e0a081d1140013661517a1046d0800080020b50503990504039034096501004500727a299000004641100651001045550004116480d001c1c001030344615045101500c0c008001100348441d8600105803002d60358203080c1100c1801c404e90b000350341b00d103800f80581c0d10680002070403410000c039087c0041c0228414250801c007a2074840054a20708400005030000074400e00400010410030b0300140545208002c0311440d05c4200008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 786098723 1250 786097473 786097483
    0xc131a1b1f0b090603150c090d1203020c210a0c170c1b030102071a06032a01120221040602040302100804050d140a0c030203090402180a0f050d030807030b03 69
    0x1c0a4030140e42d8141d8040c1d9810040c400c681c0c4070344202d0180441c001020b40312402400e020300506d030303115030100300c40711f503512010741c82c0a500b41c00c140740150001070b031440140030303500c910034507800e5000e9400141410707039030008041d07180452103131281c0c02c08107803642c100d03094044c07448240c078610410a002030032140a0802000c5003880310001c2d0022800700d090254071a404440c00c10b0103684104a00c1012882c42d9100f00c1303120220014088160715402c0000c0d14000d42c8160159091171107103070002c00c0600032105070781201d5003031303e0319090142d81c047c0341c5040b070250414056854004810900041c6031510046030300c513102c3d450040c103043c0c480e00821440c0310803842d07420104100038107200500a040081c40702192041c90030406a414607050115a801071550b82410701c42c45110b070380b01b014000c1c81915400200644219214140540072841c2c40b189281d101e03002c0c1080c0500031608071107040025040c3c40c0d000c3c00e82d0540351076a503022102c00c04c004086204050ba07840305145290b40900c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 786099973 1250 786098723 786098773
    0x1203150b0d020406020f0f03030a1806060902090406060e0f0904030c0f1a090604241e09020f0303040303080133120605030a02010e040905150c131a1b 66
    0x16203d03810100041d1400c10481c04100c0c1c983c0c0040e070b408602400010880398003081e40000442c18a403400c05036542a1400b860048c442c1c0e0030100003281984480d8082c00750038204940c14800940e49041c1030700d07410300f090360342504141d044800b405c0c1e0341031078844190421710901d13001401c2155500d91f8050b11490700703230490340d40c50541003258520401e00b80c0d20342c005042070080c01103424203a4884940100710402c809a4a140d107102582003c1550701038078400032242d1003090703041030306540140107000085c0c0c202d00c9440e0200c00c1ca0058107000080d02c0940c1d61580300c6036450303420901c26410301c5580d144900301194400c07042940c0002c0000750401e080d541d545400b185816240c8844050382d0203074010343e001703078060140000541c0c4c1c40b052040001206850000d400d01c0345040c002e050000c540c105100545406087c00582c441c0342d0014021041c820ba010b041036904c8844c6804000302a182150004400b8440000e1220340c04c00e110f1b59180144003244c442c050608440300940000e40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 786101223 1250 786099973 786099997
    0x30c060e121204060c0525060b030a03030608060c04060206240a0b120c092812050d0305010806010b040521190519080703052b02030108191203150b 65
    0x20b0244020400c40c0c0c00b03003800098042c24941d0400c02403502e00710303200003145110744400c2c4100164206008045e17210100e41200501500c0c82045141406006007405115503d04d5102d80e00c0001c8288050340b0a64040e0355050340541142d44900361302880301c103103480d0107606a8490b41c0c041e111580c5ea6184800c010001001e0460300c41000c403440c1102908000c00c41119680204001c0b419587d400340c2d560360005541d8030b02100039900300710052910b58190001030301c0040d054442c20a200000800d041c4d03111050758203100580c0c964010a858481c20300c1740414001080c0024001d03460583c0d421454450400380449400c507400d0002c034a00003201c0050400c10071007a40c49814401c0030b002030341c03840c0d20011204056a18035a610301181c803802d5009010068045945200300c10f0b40c2454040103820460714060010032180300c680294801e2080c64951f100d0030251012106000102c0c02400e0341200a185849103010000e0303000d44400d81c0c0b181411302003a6000704660304094060f140c20782150f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 786102473 1250 786101223 786101257
    0xc0b0304030e040b0a0b16030c1e120903260c101a03030f030105150d0903021605030a0506010e0703021b0319170a02070201110307050604030305070507030c060e12 72
    0x2100034003080340e021810650003001d50070000d101201006045510790004602098156403640c1000c5a583c1c1040700000d25441d138514035070ac0b41c0318079074501c422007030f02500c2c03c001e1610b0500c2040d19840200c2c8070040c4582e03002c0c10b400702c40480040719a2002d070b61021b111890301c003c8100c03030740c00c03d22200d45001240d980d40000c071646456540038454400402d8006601c0d001182400c030505000510a0610549001e10a04044c0f11440c080e5001000708400070303c240581454044e4072112141c08404001046541c000f0b80ba20380000e03a200b5068110000c0c000c07a900345900d5000f507100042c500418141c08000400800e0700b4070031840d00da50340b000c000c2c40e152954418a6010180c42d003905604001008010035007a100540c0019084a141c660050b0385400510050f0368221880b50805000c0c0404110b082c2402004500310740b0547c4643c3d410449a030b680c0170251614010a0005000691003103d80c4002802035440341c44c12600d144101c0714a240030503484450307944400f58a031007a07041 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 786103723 1250 786102473 786102497
    0x3c04050406090c0b041a0c01090506071d0a051e03011503030509030d140a030c02010b09010b1b010507020a0813030f080c07051c0b0a060e010b04080c040509190c0b030403 75
    0x9081e003043c000e01030048415281500c1c00302010503142d25010030403454480001e1011040c0e03401d6100001d070991140940d0002d01d404035024000030a07029031803a800ca100c40c11707148d6a00d0420700410a9480081226040c01c1c80e00c7e0702c8492400f00c20820940665903034000118503400308448500a510a40c2d03042e0391940c1080c103050412040090399020b21002090040944008809894070b0048602e03000410f1140e10300c08034090614042002c6c2c101c2400c00000c84c03808940c174000d2581c00d8203005005022600d502c0c403a400c8903000c991040040e0864200c01f000160301c040107001c075200d10320441c8500b0b910303030b21901400481104215034600001503507041a0106002e50402890f048401064030010810002c01040802100420110030800060703c10b08642e07100c1c3e0090501d1100040b40e039038550340000707483e0b0b1050141286034400c2d114000c1c018502401540c0c42220900040c0142120300f05c0c3c0045007a03512001191500101c500202c0c600038200055031240c0d0190380c50071300d070a42d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 786104973 1250 786103723 786103733
    0x1c0203181e150f0601080903070611070302010b0a0501021222060305040308150a03080703020f010c030b04200412080f0c03031017060c0f0d090c080c3c0405040609 72
    0xc0c0804420b0060058041000414206480d1660b8403090a0130503e000d07980310489030341140304000005203500e00c0c01454510006100c009841801d1007a0000c0040c141d0700710802510700418410240141d01000300d116944201b8006482c0b0030f0b014001c0741380741086118040c1140345698108030300103591135041000785580134040c0c9802420141016450354000d0020032a10202400003030250240018034003301071007000028002c0303101c48000c10803e006030500602070705030f00302d030580710b00c2c100b40c0305044030002c44825040508000c0420380c6024500382500050041c49035060f242c0c404140704040c0120400c2d002000c00300454070107181d803498980c5e0004003620700c50b0481c0000c2c1c889619105501d0300002030b8182c01407419141191641e001201100c3c880c0301e40c500c94058203040c25019410041c4005485c000e0f1002003094841202d501003c0c010302d600c21080700d031605004080500f0b800040d1070542c50314034004000c443d0105802d18041400e84805075000c49040b503071154440c2c03c1c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 786106223 1250 786104973 786104983
    0x20706091b03110108070e1207030212070e06040903020c0a0f0f120809040902030c0a08030403051227010c020607050a060609050c0904050603031e0a03111c0203181e 73
    0x1140d01c82550308150454540b00c20100f501c031000e50500c0300100204d106070b402040201a41ca40040051500c00c00079043c0644a4a9510080b4020000280c2032007140070085400030580e801034000001560740c0c00308210140842d2401034055000c0c4907804491601d5061032003010b00480381300485124070b8007024030032100c410360241142440c468000303400100c895044036145841100d021900c01c515000213410118902d60242e032140b140c0c00006a2990040050011a03010f8420307200d0810f100b003008143e40c4100b080d0303007030f4460b604404200607540200d0303441d681c00018076100c0500b10495011030070540c000241a40c0340d41c0046915410483d190240c0e8000d403081060602aa081ca100d400c0070030300a00507068803480d15400080c29035103042040d18044c0e0004c1104044000d0f280c020407060741d2201c1c041c00300080c0ad05650076011171180b002c40380700112210700507120405000d032850083d00040d10941192120000d011070b901c2c410840c0c2c0c1e4101003001c030150a80303842201e0041c600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 786107473 1250 786106223 786106253
    0x210e1f060f032618031605090117100513140a11150c030a08060a0b070f03030509010219030203060102190803060904170d0510050402180613030602070609 68
    0x205040080a21041c02180c10316400c80c0d0784007600c28442288055078140c880d0302400ca0000c20640400c1500300f6102c03904124030408030a03070a41b9001c5c01030840e1858002e04501032142c00200010041142d4121070390305108a29105007628410740500203a041500d03415510f000100c0e210310111401d0041d416800407140c1582d00c0180f6103414603030b070340340103840c05c0c411842c0c464a28440e00c813022072b1040e02142c3c112071118003900d6a503c000b0801908002d015244030b070064521540c08240c28100c41e003140c00081d00000c0c03240c8420b4036540c08a02074103005045126a5409200c3c80c650310f05058811820031a1540700981c41c3e14100307000a10744001c804581d501ca10b0080a00f00c041100e900461f0782000083e0f4030319065030303150308080c050021422050307030031b076000042e8240f00003005510060141680c3c1180d070104940d203108100a902a0385840068410480040500f602d082402486054410010302640b07941c1d90b00c80d03038201d81040c0380c1600e926444d24011010851948080380e51 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 786108723 1250 786107473 786107533
    0xf0f030b0a030311030c1014060d030507120e0603040309230121020f030a020721022a18150a180c0c140319021903210e 53
    0x61000d1010028070460312a1102030240440c1181521407100144100e580354007500c0221500d00c3c50200c14400100408503407005040100d001140071494451035031a0f256406641d8107090082645446d4180304540060b1001c0c4102c25521362400d484010240d8811806500c82040540c03038001120780d02c55000b40d21503000d002c6156410a2030fa00701041036202c0c0e80301c14100780301d198040b00174402440340c10000300e03402c4804003c00000710416002804128400c9140c481203800500d4011042d403460140345016800100e441c0d801c40d10050703420103016042c5c904c4030002840440119071009130f13105040c0160440c12b0100090340c2c1310f12540c200d8401c4241e900700c002c81d00c0c121a909144904031103503064a612000d520088901c10100e001030316800c20400a810100d4030b80b5144e8951151601c140c2c0c050822403811110303030000c2080c49200d5100249810020f0f5240e5080703a0000e002000c0c0e000460038004504c0003403625114418400c48090000c0c06000b1844000c411b0391405208002e00b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 786109973 1250 786108723 786108731
    0x21b04060f3f120c0803010e0a060510050d060b040503032203080d050708130804050609132c0a08090d2a091103130b190603030f0f03 59
    0x1600040c2400d1100301e40901010444220441c0e648003000728051074055005820400400c62444000c501d0034402c03403240581e840f000c001c012007540c0d05484004007801403513084c8010842602281c00442c0d10460442d000a00d0f1502c0c1c00000c5c00c1c00400c0014900014004238000c468661035128900140101130801801c182c07410300000d50b64400c01c0c0c1e13180781d40d141c841c40700041c02c5e10710b503012400365038416005038607060707448580320040c802201c0f0040054100d5011480440116001c41042c40d04070001c1860f0038101800d10a0b542d205400300b54101c2c004038035000c2d40c0b6030315200b81010180c80300c410100d041f460001064080e103940340340c4209034105911080000fa1014115415000103072188042a080b6042200b4400c0d80300c071040209a480805c10340c002c00a1148103030a90398091401c10594151010322403040c01701b1039030401a41000401d40c40420200765119621040c650b07041c500d0300c10f040d1080f8043c0c071010307807003100865590003807014205d42203184200704602c0c1b407034100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 786111223 1250 786109973 786109979
    0xc0303040305030702040902120d0c150e1e210702030c0102030f0a031805010507090e0907180b150d0b100c03170a0e012a1b080c0c0a06021b0406 64
    0xd43c41c2d22510a009101e640e4541c6000300715252610b0705d038245250403040d2200350304c4000001d454840600c00c02c4a8034034002c0030690140c0c659102e03134002e960010f4020b001c480c0c81c51003542849081401000d032140700e00b6036002d5140030051503076054150f1005001d92107400b144145468484c1c500c441034155082402800440d04191083d00c94041e013034600401c42c45c034400e41c4664050b240ca48040c01c194280003c00828503001a200c00c100c41d40102038030350036510180030a40b2141d450143c1c1c0084131010259801d41ca403150060720034024010003030000005180e50b65901c0d68422095400e40e26180e2000e0307191841c0c81102c1200c011114180710301440a40e5600809801d03030f01c10310720700d6809040c6c04168080b40b5580030b083d41d001c1c01c80081100303108280702c0300400c0d141e40105482e1609280321241d143c43c480e14140004c1c404004903100110b94641d50340d641604455121500752080f011240319075505c0080f80d07002005c1d0340c0c02030007100c129980500c282181c0386203100c1c0200c0c2403841c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 786112473 1250 786111223 786111233
    0x90303011809080f0c15151018150f090b030402212805070803280e031f050f01030c0506090d06090b0915072a150b030c03030403 57
    0x7010520480100002c0d10521600e8200c14a01074400001c02070340c80450400001100010706c0000000200012035036552581c5208a4544032409a80e800009625015003114010350040c003500c003240b4690030715692212616034000ca040d414217400102c42002c40c03015039400a003104080c02c00b1152031071640c45c1136000318109490f4004010911503100072a0703000b0310004c1c814405c00c488204a1141c1c404c42100c5450b89824590400792a00d004503140042d00c010000125411440003485070450502d00070f6501031523103580070501040c448081d00d056815681804146400044000c80e054008405041513045840040c102c15940c9402c100510101d03c441c0c07a008120742c01107078400d03a550610f1000c242c4108140b0b4006000c50f00b0100a40204075642000c0d40c0314000010440e01411105000380300048816500c1c01c002c18101241d561800b040341c00b02000082c0c01c00700d41c1e0040f40c1556500a40e50600d41d0f42202c0d03803580d506000006282c00e0002c140061400c400860915045480d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 786113723 1250 786112473 786112499
    0x80f090c1c03020a06050f06010e04050f060d0312050403020d0306090b0901050405071101060e0411182214070504150806061908031c0b1f030e0c03030f040e09030301 73
    0x5441081541c4003004030400d03208000f0141d803941e004000740b1541c1030018200710702c080260703101800710b4000d00d03140105041500c201ea01c1020340c40692072664031030005000701540008410350421404c0e45202c0500306650148034041e9210ba40101030b00406210010308488490b0000f800240c20400000704035502c483c1000d0550f9000c440000c6d0a880b074800c03c0d18101c0240b40d00e0340c4a9420007100003004040c8403151403080740100f6510300158908030402078404850310315494440c2c0904040385811038a400407038501414030240d81e20786501500c800c0159480e5941909503544a00c81c240100d00b06400307540815045400c020208a0404c0091a00c0e8032000707040a00803034140f4030020340e40114401e21001410312206403580c509000407101d0380401c1e05400d89400710b052010301421400c0580314000c07002600c44003070403c11240f090481c040d099910340502a881686184416990140010401d20440d074940c46d64a0b071603c0900783d20550b00038086103480e0014001002a2010004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 786114973 1250 786113723 786113749
    0x901050d0201120c021608100f020c030301030b0c36100203120402150c0303010f12030c020f010306030b01080717010e1e030d0c030501080c040501050f01030f0e030703080f090c 78
    0x800844c40707095594080746002c031100000c0c14240021b4200292400000c17680520a540380c01d8140017000c80d4a418109074419400e42248aa000300b0040000c2504c907000b00da00a03402c02c2c2031510323042e001c0c4102203050400300186a404c08a1140351801c20031499210318145100f46ca0750b008070b803034282c000303500c034000d03000c03004c0100c000342c170008017195282c040b8943c0da504104511030700d0713042c0303924025500e8009010707001200805030030100b52182c140740710701801507056135038018601140d428481f0b280c07440b40c507880c14140c42d50000701c0011344040c0c026020b401c0080090001b0751420030b56211003011040c04c000310341d151601240500d4030210320118805681418580c3c0f003440c156840d4a5441086203038280036181500d840302555064000c20304a80b40c0314125a9501d0880c1c0411040f60801c0c42615813100000d1541d142e294040c8d00500c100084c00d00700001c02d403031403101d081e0440c2c1c00f00d4070481c00600e052080080788045840d880d0b0b006035000b8000c18038000180d0106881c07003200e20b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 786116223 1250 786114973 786115007
    0xa27080d0c0e1002013e07031209150c17180f150a0b010536040501090c021905070b18040c09090e03070f020f0105090d0309050901050d0201 62
    0x10300342800c81400741c400590440c9010305241c1c44034252840003802803840c0c100361100348485c159440300780d0b240c6e2840741030212051184500c180b041440841c13020340c00020101c052051310280c2804410043c45400304082c0038100400c242d203526015102121080c81a8906010101c04884640c0103c44c4a5a510880b422800c1481c45a441d503080d25101403680585094852256212021928030b6080c03805001156000c5c0301c0001c5d9080151018081e08140750300c5401000c42084080c00d1003403c000342050400c00d00c0c44180d10020100b029503070240c005450716510f4440750440b81c0d604110040e051b04541e00001eaa180c1640d407607a48a001601ca4003044480103c4d24842c840800c151418005000500401c51056108809880d0240921500700340c4c80c500015402942004001c0b2101c06922036668000011a50b00b0020202004596141044424043c1241d640c07502c140e400841030207522014440d5103041d04200210300c050300030902800403c01c070302c070060343c0054120f18100400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 786117473 1250 786116223 786116231
    0x1c020304110306100806160806013b090a0902030601030b100f03120207080d02190c09060e01030507050301020a050d0509120f0a0e100c080a09050402030a27080d 71
    0x504010081d40340c8100015810301522040c8103400d010f0f0313600b440441e00000706564141d507900d60a4810f0b0340e0055101e001041015000450941c440d031a648811500c10303800340e001e54034121603450211000c0c80688540c50400b0f0100c0c41301d1a0081049501c0040a14184040d60040d408207403516010305c801801d114203d40070610f4103c4a05250b00504000f580c1c0381c074010703901d0418a842c50740c602d440d003025010389030740491200404100c5446d209286c0e001005942400c1d12b0201d1051307103030b860030b81c1d80151307030840030820414074001c3c07500600300200380c2c11041d41541049410310b031441d8403c91080c0c1c030420440703000f00d03008001d81e80c91503022034002407155580c014150508020006d0003811410005201d000c4040c0803000c2c103881d07185503603840803c001d84410b101090f0f0340b4040c03031004901c0504483e40082d260708000c5c92500941e02d01b190644d540c80000c103040e40c100303964508950b03444040c1e0000c014040f0b030680415402981059811800648602480e07120340c0307040001558031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 786118723 1250 786117473 786117481
    0xc0c0715030e0d09031a15011202041a03010f0611151503010606120c081005090c0423011d0d080d06030f050105040506091203070806040902100305010503010c051c0203 74
    0x942c0806012a071100594104501c036001c0104031030000d00003101c694580403211420300b032a803003000f0312500c0300b094851a103409200064440070046000c1908443d000c00c008075031108200410f05160700d60492040c2c0700d506000c0320000784071041d0045401c210710017100303c000c00e00001e0380b0304851505140300d840640740d541740b404108850004064040d800e01d480080d48690000035100015440d00307080041c050001001c9880d1102504c4200c6c149030151000d000e9407404400d510b8006406480d400c0c946903841c0d00c20310510480802c808101d40c105000318481d075070054102034007440c5602072040c080c42070b48000f0316940300001000d0151540030035240ca90025a6000c130002c2c41c0c11800021940c0524a4044d01030300c42142c0c103c42d180160804120100f100081d840e000001e442e850509561314000b04888030b403030060606900c13645491078800540c6421088a24a054540d00440c45605000030b01d801d4a4001000034100300040145a0303840008480381c15180b0701200000d43c1d20b1b11 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 786119973 1250 786118723 786118727
    0x7030b040b091018090b0118020720030105070503010e0a0902040605030a2009010e040b130206041d0f0702070303122d050708040312200a0e090c0c0715 67
    0x25a00a070580040301c040c14000e51a9251141c2c008035841010318112800207080120f040e02c410351001001c02c2904c1c8010b0209801741c034495205140600401070801c0300a4442c0c600c4210100c201c0d500e01154060003075558142805015402051820103520b15450039078213555028000302a141a255222104411940d403a0445002442c1c01812075400c0101c1c1e082206298600020010010018100906603400e20301446070481e03c503501500703901c0d603882d1124040704100414804452481a082000680c0c5001c040e0000e0070300e200d044542006800c05041b8203c60282c940300700c9200e01e01c1001302040e40022103105490381854080350f02c0c0496000c90019104001091100070b80240b5003c000328059811821301c08160b40c4203000540ba01d20307096400070781c10388000e0000350540d0580048811a504444c070715a80f142c61403038098070b4a10050a05421202403100000c3d400b900d241410301d04910400d0300414102d509a00c3c00c402c07402040d68a004920410040b440e850b150190070314 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 786121223 1250 786119973 786119981
    0x903080304260d140603030f130902120702010507080124030608010218130b061206060c0d020c03010b03070e07142b0606081b0d0207050102160b0708040b07030b04 72
    0xc0d89507010a51942e82c0c0325402c0c0103030f000b42c000310030210320f0301e80705a00c0702d1402c0d00701602809000d40554a4011100038010a83d4008090b0b02524a109400069410040c0c0f0051203a400e507021241c1c0f0360f00705008001e094a0014102208102040b00144540d00006001d01c1007508500041c0e190595001001c0c0d02a00c3d05034880e180c0c41d4804260f814000d48405e80d0765070f4001e402c4070828071214044648004aa140500c541e030403c1c0180924110000d40c0300690780c02010041009007061204001d05d0702d041d0f001e9a21b80010b07000240b144000e8182400790448261041700509241030400c1e003440d01e1140000c0039441040620b0819041c108585000c480b28141e8020801c0d851150004201004990300003005000602d45500012040d02c107480c0f080c022400140606d0910b044a42d060104e50408140042c0040c0c1c20002200007840034802403010710500041042d0788010740c104640720401c01000801801809820040007070245a1040c1d40810981000201d07140b4480101d1300030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 786122473 1250 786121223 786121253
    0xa02012001180c06030e0d0903080f090301020319050a02180609190314061b070209091e0f06130b07031e09061a01020d05090603180303070801031a070903080304 71
    0x811005102c0c502804800e960003400c0d14542d89050159410344d000103030340c40902c803002c8000144a00400d01c0080d00d243c004040709400c60451500348a100800a0700f203030300544080032031011043c0740c03090075859409120b602c804000d0046007054000307003c6920418181f0111886150009270740a000e0b0b49079a003003191450000d080321156500ea24181d580a90500ea2840d058442c080015448091100305558254200400141480007540c20b0011080e4013510096690180b001d040030030b00d800c54520802084420024612a961045581d00b4010050a04c1040c507a40a15840c08516504502a00410f0b646400030303070740c882c1c0040d140c0800f20b0184e100d5003960400003002c2c1408001e8119140702d00e03240d40303e82c110290171001603a40f0305c1e20412220110300b00344801c184c0c40c038102c4099a03001000825182700340c4059161181154001c03106540820780445c0144140201191038200400000032030700c04a00340020042d0008040d440700401c1014000000b500308620340c0907000070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 786123723 1250 786122473 786122501
    0x9041509081201081b04020a0909020d06060e0d08121504020304080c010c0e030d1d04110a08154b011101110d050402190b0d0b030a02012001 62
    0xc0034818034059a0580c0800e09800c1032501e001d002240e140e9004c00c2c814a411101c1d03a408a40c2011a820321002e9000503a200082c850b0030b820000d0000110300040c6028105000000703081e50030401e001d0000c0a0703114146020351401242c03000050112002c85403d120710304d408180a540c1c00c404002e0200e401026075411500110a000410481c90042c0c100581c0000003444100f014500c100d44c084614640305038507038880c80b03a0490340ba028030149500001440340703603014003d804022030b0541c0c0142821003628040050044052544011801e41141c030000c1786401d18a4040d0004d004440d00c0c540003507841a00241c164198092000481e031500ca424450710100032000c0300d03c0e841c0100d08544680801c1d146815401c07030010602c1003030f08825400840c10b01340340030400410020310000b003080341c101c0300c0714040d64030302400c044004004120519503030b580c03152888412030a44042d40345490007640004101c400603a0025a44008520f010510000b5a4074407807405016104502400d51 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 786124973 1250 786123723 786123731
    0x3030306190b1210090504110f0111030f0403050c0613060e0609040504050c09010902122e0306020d0605060a0c200604060206010510080402031c0c2001020c031b090415 74
    0x151a07020303400c3d080d00c00e648210002c0003131aa102d0511056803c200c40c000d0142440f0090b01d0f40c80d160400c0c01109155040c90807084016031b00203014a140d006643c40c0540e000c000c2410420000c0800c00d50445000983d1f0303403404c005008403d80c490b202140251020300c101420071400a8407444151600c00300b00410900207801c0a041850b100c1046c40302c101e0090f000d0200128414816008844071054800480d154665400da001c0702180c40203802000e5148070f203005440c150600c280164095070050b080140d484504641c7c030001c660f0127a020500414040c0804182d03d5000703c50320107025042001d4410b00d00c007408007090070344541c4d84596441140894040740c0c01d580010300341c0c141c45064544404213a0080741c1599900c01c1140c1c000c0d456400315011684001c1900c02c1c00d0311b1140079040a141c0d4100642d2000c002e041d40c01800c0126203010b81c0d00041d99a8104050826000140d01501742000c0c2e01502d000e441a290098a001308016004070707040102845960310f51040d5a10100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 786126223 1250 786124973 786124987
    0x1017070f0c4101050718050405060a0e040b0108010e0a0c0312110316050c061204020d060207050d080403020d0f0207090b0d050105100321080a0e03070c0e01090f020903030306190b 79
    0x20365000c0d1661001ca0b940c0b070800014602401911840c0002c1c0c1d458031041400c034604010000980001440c2c1a04130b4918000040d0b00351025018500581c031948240c03410b5818034180a0031214078110a10043c3d00407856100070911503007000080e00d8118419101d00c00c1c58450943d6041007004031701905100c001600111403803d075248440e40c902c50030545068101110800a00303000d001100001200c1400101d030042c60011218500740340f0845004d818010580c03100303810003500440100c0442c1c02401000300b0180e043c041a110b01d0f00e1810000d1000c000f840f4000d507600b0303050041007031705075803002c07018110b9440540071842281d21100a01451621580481609680303120071a081c2241c40b201d4031445030403000301308000c1159590091143e564200210152a000c4a100750343d00040115034007148040c1c4021003c1c001415640c4459494000048120303540c2d40d9079020402d20500040c4c039543d8011040300e41000e011079520700c14420b40d0304800710805072a400079088a00000c0e001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 786127473 1250 786126223 786126323
    0x180718230f0106020709090510091511040302040609020703091514030a1b051c05070c020303210a090c0e0a06080d0903031806020312040507051017070f0c 68
    0x6541a0f401c550300791080317603035584e955100761840680000d1040d0884050801012119845469264007a0301c64443c4c0d00980034500048840c06281c054880c1d80001e801d00642c2054000c03d4001c20303211400f146441c44648001306006254041d90551046400c07008088a00c01e180705e801151400345140d54070306003414403d0081114105040c40c907001c3d181450400d42c05201550348001049a9101700d80780441c20050003450020900340520410403410740150700c0410252404054044245140c8420000c2a203070366072004002d20101c40c1081e218100003048003c421003211240414030300a41c55440700d04c0042c100617003083d44076215400c0d0342015030380d016104c00200c0c2e010f600c5101400008000240d080e22040c0900c1e030240e4400c0000300014103480654582c4140200141c56500f526074000841e0f40c00c5407060200095210b502c40c13446483d03c5900e96400c000c040c01d041c40ca00e0700031031015201240a5102404904134003440c0d41405004a81c2c2402c402c240c184d00c0c42c0c1d046000144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 786128723 1250 786127473 786127501
    0x4021201140d0305070b0903041a030402030c090907030201050f0d0203040302070e0c0a0e092710050a021305120f01180308070212181206070818071823 67
    0x1926030041022024010030707041001ca1400382e20b81560f542440d2030240d841d01408a00c01a008040d0b610042000113858400e00f400c2642c11240a10030598a0415004142c5403904515042e0b1082c0c540b0b00c04c1c440d010100051a004a0b5420300b0016103e41181c400250035025403521140010300001c10001010f40c08a1420180d402414800c0f440f1384071a00022030798003d020414000c1051242c200d41c1600d014030030fa651103800c1e00071540c0054020aa02c0000e15880132891132564028104000084501d01400e9400060350501b1400c0c00d403c0140c2c4141d10103a845100c1c0180300025000f02240340620900c0000070b0184000e000c00f11810160004551540b0700682c0081c210b400440c02d05403001c6030981c5450401c3c8046d0341401e0740c00f10705013803903891101ca644d4000105681201a41c0c02404040d00c103040303030b45520ba420704e895070502e000e2001c9281e01c0505a04101030905c40700004190a441841d030301a00001e01c5095006030640d40300280c5112001111100d0400184a8601e01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 786129973 1250 786128723 786128729
    0xa14060105100f080402120f0a0c15050f0703030917040b0703030b1e0f030a0b0a09020a050a21020406080a050609071e090c05161214071509020a0504021201 69
    0x601c00b4a285500401140e4101690341080b0006030401d01080c0903182c8484514407051005041d2100d1480c4a2440c034030300400e805d81222a61000301e0104007035401561404860507030350810320b140410031203903080c040c4610840141415034a00c45072044c4816401d8142c442040190015502d9840d82800f004682000d4001ca000a0400440d2419403c10408081032011002c02d0410410805da040081000c03095100503010b101c1c039084240400e16809070140140c0c4111400914054039005120070007649401c800d01070702408004001500900b040d42c0f0082010303922400c0310302e00e548002001b0304902d0340000400c0c1300e2040e151050104c00f2600c60300541c1341604981002d40d460b4002c181c00c90030768031420b0f01401c00c42d40400080d000c641040500103030519140c0d2404400d00e013559003108030080146c4040030f8543d40802d0b0250030030482054000b12000d8541010819680e11801d2000307075002c11040da8a0f100094110b4a55140943c00b800c00100159200d0034401c00104219000344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 786131223 1250 786129973 786129979
    0x20702040605010915030f020c010c090e0106030507020d080a0b06030f0f1005060a030b030f24070e061605070b030a0207022d012a03090305100e100e0a14060105 71
    0x744002400c0d40c080e4404000b00c420030034580d480c40790181025130040a4000d08916816000c100c280341c4210280f1856010b210251034421001d03041061030480305a05030004428180b404062016a580021f10700758820f0f0146000c200503070ba0302c121200549125840c0640009000c001d0118440103e11114460361010030074910994410310034880d0780c00503104041d00040700700075183c002c0b4480c0d040040e480300301604541840084004480c5041002c40b106008030203103e101a04030452040c18076004140f82c0751407450700803000e00040b214842c1c6c0c24190707540c805a40401d81000380a0000d44003d11a4041c00c907164601800341e8006507022480032881409200c1c003103400401401000c204900800c0c041120300d008140c0107403500000120105000a502c880b01c610034498942689030301d138130903a1468800341c0b840c41c0136481d10f0038021070b827048142800c0404070800300000740b40e51000726007d404980030804640107030404081480142036441201410310390702c2e90004010b0304a038029 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 786132473 1250 786131223 786131231
    0x306050f0307050a1a0906030430090e1305060f0712050f28050c0702041b02060703020f0c0a05030a090608042001030e030307021e15010b0d020906040902070204 71
    0xc00c0c101622081e0358024981d01410783e0200340107070324903d100c014400c1c180302500780c51b1407a200c00040c0e242c0c0084508a0b61502c5c08070703c048a040800c03c0311054081485008082d00c550858050120152800745440190782000003d041d40d400064a0235559002001d8a025080c4280c0341d1030340718002c4412901140d00d502584142108510505214400741c4158a243d51241d000c10103054414154107140e25202c0307480c080c00568544115400b030082e5548031981e030080761051006444008113100c406d0a03401c0342501c54a42c01298082d48001c0c03610300183c0c0d408000312881d81600a4080d01d5285100302c06d45042003040001c028205070300e5680719807148a640c0c000c100c0c0d900c00200d500800500521000303004c00911000d4030700326202c0c1410003281d1106010260362950b0000c4821100590003914245828806c0c5070301210906001c1c40901b0110029404a00107400184a180c0c025000000c040403190070590548400c040010300710381d40c55940b54401e801075002500306078030803032074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 786133723 1250 786132473 786132499
    0xa0c0b01080f070e060607050304080106090b060309030901180909030c0510062102010203040e04030507020a0501020708190501110a02070614090d110a03020406090f050a0905190503040e0106030605 87
    0x10440e42e004000d40003801400c2c14101403221002002d4107103500070340103020b0180000c01c14809000506250304c00025031034600502c0a0980380c031404c0f0355000724410010300908110101c100c492001c0203003015200490003500591310054184c0c4501c2c240e518000e504000c06a0007a8000c0d81c15004000721703060011b40d8503125040301d020384070f008210b01491005041000f1605480488180140107403824503503110b203440101241141d044001880000d0311808502d0400e00e52801f07058213200403d1400d0404203059a1207070340700b41d03048508910504800801800350080204024a80d02494480300003400203583c52a142c05040007284c0d050301ca2034602e107485d506441c00000010101c0c800c1c29540c0d100d400c40340d91001161500140d040c103001c009a2114007410004080c0343d000024106041c1c4158070450340c026105801c4e007070070410018085500040c4100e54014141001a10740b00c240c41d10328030f1485640e0000402280d0b1030b0002644541607403001c011100195071303008034414 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 786134973 1250 786133723 786133739
    0x13020406021b04051e0a0608030a0509190311011101110c033406021c0912030f2c1509150609060d0b3103031410050d0f080a0c0b01 58
    0x401191194442e0302031680f4002000d8840c000c0700d4010a1b0b030500040c41644581c030b4541140c1c040c0001401140d000100484141054006e00003c1c5881d004094180750555540303600c042c0024035214100045c0d42c1c08500818029401001d074480c18078950350f41c8905001b0841c1d140d400071400c07034401406080c201014124000b040d10b96803a0402d09450b1140d5059441c03000940140000c90011250220503569100d400d108400501c1e000740070801911500000003000e8548101c2c543c000c8a0a040c0201141180840202220b4a110400d440d01070074000159103814031503a038070203e0907412010300c0038011000c03860315107900503a1040c0300c0316a42c080601c403180700181c907160380044050150202188c8410680c541151425861120041007000800703040034100e25540050002ca000d000101501841007030240c0a404501d1021403814a00e15003040e01d1502c60790340100d149850320030401064600400350182e00c080380546544550000030405817042100715001c00e50718001290760b503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 786136223 1250 786134973 786134981
    0xb0f12060a2307080709050d0b04170a09030204090501020f0d060509183c0610050123070510110702100518040b060c07060f0207061d0f13020406021b04 67
    0x414035031545002c64a820b141160003000050400301040100e0001251a58070141ea2101c818010f400845050629041040c0d1900c4110011022804104502003005800004400403a5011600010100300c1400e04502a104080d0940040000090410f40d0903145078089001c2d210f00f602d0b5520325984845c14180c0c061102280c40480342d109241343c1807800390528040c002406102180c01140340e001e550800040d1146003903441c29001542000b4065034190800c034010102441d146030048080384204112041c001c5010220200002d018410701c40c0420040c000c000301c9040820034030303d40160b009466000207904070310450030707035242d0a21180700310f0644454508448040303070440383c407808110040014070b000d5900700b1418440c0e00d82000041c030014000301b0316601c500318541a50000207081c025140c0000042c0074203140c3c10144000300c400c4000511f942580d000d031040c80700744001409292000341d800401400003d002c0341c402d81c003040c080e118642c06507403da200f030480000c105c291 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 786137473 1250 786136223 786136271
    0x20708010b091f0504050a0903021014040803040303060f060f030e011e1808070309050319030c11060c10020903010612120e060c01050702010603030e0d12030b0f12060a 74
    0x1203041004584101040030320780388036001030140c03096090707a138201140640e041101d03040300080d62001a5014150140144100031f411008100040341030103003050001d98002e4000340c403c00c00400081c0c01c041c005d620150282101428071394465555440081c1b209415103400400a4100380507500101c00c140281403036510b1803000c00d00848200c1001c800201180b40780381c03d403112440c64200100300c5090081105500950718040c0da5030800d004e05140440f020b41c02c54201c0d480c8000ca40c040b070340c0300080c809102e9000441d881d01500c3c482c00181d079070192160101840c0242080d810b90014541d000b4a0080c005400030b10600b80d440c000b09001c2616a0009032190542c01000c0c102984100e5040ea145180208054201612031411030308442d011102c460140c1e40d10703103092041c1034200304400640c0360700b00e5110824418035640d003000b09141da40f0b00c0c814107460700c03503140705a40c440344164900702c4003410241c0d10004149100b5590101692468030a0313107440a441400300343c0f858a2403071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 786138723 1250 786137473 786137479
    0xb0405041a0a0302010f0e15190f0c0206070f1a0108070f030302031605070b07080304152c030d0f140633040e180c0109140d020a0314060403020708010b 67
    0x5800c0c55a0019184e8003002040c110030402e155850700740e02d0ba604841c4a0f2078885148e85039485022140c0c882e41d1150304a40d00006200605554810003584101a8084140d041c0d40598844000d490f2404100c100600e00801501081780c0c400082150414440d04075490041100c400d1980c440c484a0541642d000190040c0c0081041118904100706140c0c0c145101d10210b42600d80d990210081741e42100d03004940340040003007407000344500c0b000409525140c0110811400203030b01070902c000d41c1c070a28a60001c030b88821070380f41c480d04140107603030325820b03d110188060380c0b80c02030081c02400d2420003050130144a202089490a0810000034044031000341c5285800d141c0c031201d803104400c0d420390036400c4d004000200e103410001c44124001e2111800900c03030a24800011410040d103045400c0c100080c1481c104000341035130541149201c4240c030040c1c241181c50000c11500e45168001901c0301140880304a440c0303000050580c4954001e03401c0d1402151200101402d8440391680700b54 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 786139973 1250 786138723 786138739
    0x150b040302060c0709090516150909050403020f01050c1209060103030906300501062309040e030c0f0c0315090607030c03020c1203340305070215010b0405041a 70
    0x40141403001c000e0a1422112048801c41551030b0614015a0340002e001c87e480c1d000700c0360a4a500038494850006042d41e030f070002c2d004620640004102000c42c0c8181110952290003203401d0500a20600c4084503044009200340c1c5882301e01840640d0100c074026811000d410300140c030b50303000401c280c1d0581340d066903907094403450000c0c2220550710004165201c20b50701d031240440e40c410604046150030000c200865158580200038261030f042061a2001c2160b207400c1320041e21900c1c08075400c2243c21500002d004041e07884852130341c0210a10340e8191320070000302e0b0000960000e00b045a0130750403000c0340c0c1d90f100c02d40355074515250180c6156030541e20030004114058000e0b08803202c000030b10300d001401e10300401c560078a440e0301484001d0103804008203000020502c1382c075001204002c440d4604248030320b01d80d1201e02c00f00d103241007000c050799500400d007158824010a250b03040f2080c0461115610303545148802d50161282c1440f8600d0550480002480390713048184034040101852 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 786141223 1250 786139973 786139979
    0x10060506090d03110a05070617040c0e07140c07080706020f07060309080c0d0801051002030702011713082b091e0203010221270d03020d0f06030f06150b04 68
    0xb00742e640d00755400301c040c40303221405242030100c1044104c40d5079006200501a0354a01383c800380c800c81069000010000d100d404120102d911a00818129000c000b01c000d195a034068045a40d1500c4c103806850b03e610024014a859400090400c01c0d09d00d5001510307e459aa200141d13907854090b11201c440d40c00800c020441a030199100f440303a20b005400b807030b241c402440c94941c2010105800721000c0341d043d00061102c1d0400d103800b00d401206a0004600d0301e801500041c1040c2408451101841c0c0e40d10300180100c013210900070006c0d80d102c001c0302c0e104d03000e00e1001c0c03110f40300440d824220f901c1c0700100401c9402e000d0091042142d08544c0312680301c0b0383c6078214801008406010798140d07408000f05542c0b039000740c21080d604d04400d010722846050107020000ca41060f95448a00c04280c0010f440ba072100115240c04891118100180d0b5400c103070b800c003000390180450340c42c401c900d0050001305001800780e458000350310ad20820402c10360f140c441039000c00e00342c0c0152460150144014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 786142473 1250 786141223 786141229
    0x601080408030712110c0f060702150612031209010c08040c3501201201050108070306211a0411010507050a1e1a0c090607020112110c1006050609 64
    0x842c0c200403d4078090903d90b212082010940b203200d002010382c0a0005504441034105000d488055101031024050300c0c01c0a0000940c2c0745191039112581082c074002054081d500e00034424806a119400d40b030310b0701c0c15000700b00100340045841030210750a0002c4c030040d1074801d0f04c805106aa0050245640900f0700d211031410f621982507644d150f02030b02c5940000400320342d400400c41c225000012400c0b00102110040f4522014044c4920090502c40100e00c0c1c10032004c06410b641c0c007803910400513581c81c0002c0740039144035071000441d01d0500c2d0340ca0030b050366040c9034a201240112581c0b1000707541096007a1164100300c0d8040e05020700341c3d035103a100d58450700041c4031541c000c60403030300300c102203480e8013111070004091448000c100203002c40410403280c1c6046480d17000207130250784524200c10409114811200f05070710410380081c0d09411a800b5651858040140e0881000b080c4500042101c0641c4803640541091003110343c0004ac040c02c600407541a1140074007498108250354040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 786143723 1250 786142473 786142477
    0xe1003050406090624270c140c010617031c110903010501120b0f0f01030b06060f030a0c1818050a180b07090f0e0415020f0c0a06140601080408 63
    0xc11030b9440e450740c0420b07000c0b5243e4007441c1c0c0000d5600b8880a104410440d40b250800016400030a8410800401d07920032840503694140d0882c159401040700000b1440869409410001c070030001000802c40d0f040090055001d441680c0703001d025080540340b684250f90f034a00428480c0c0c440c0f8003207141c81440e00f600c0340d08104400c000c64803c05041c26076820009082d1003091300800c800000d49000c600c00d0242180c011500b144105290440314140119185401d982c1400098545038071a004078038282c46220407203045a5040e40025200e0030710200034006000138844140004160911046015100044074011210307030703c2460062800074002000030700303801020000d0007560b0b20100d20003a6034201030040b50701d108281d03800d0076103080ca0002d042201150801c801c0c003103010300c090108070b219402080d00103400c43c500c880469103400b4520040d1044401000d440840440d2940c541e030f60028201342481d220350414806c054000d10140748055040b0b4986000942e0030700440e000c1040f03800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 786144973 1250 786143723 786143731
    0x8070e1f05090a0902190c0f030809032107090501020105012d08010510030c0e06060f0d0b10090303020615090403050d0902150d14010302010e01200f03030f01060e100305 75
    0x200141480c0c102d50015054070304030760201c650541c0000d13004150b00c80c000070010003540c05040904089406495a00e54252201c1c4003c040c0403a4002040004504006680d505404240d155802c81815020011080c400b0390300035001c44e61072100401c8030b60040c0501c6044c2c880c0d00c1a4010741c02200b034608a40c110312904402d031022100c00c00410815000e0040c3c4e84103031f00000c0c1c009122891454502104120b40d88080d42e42851042404019600c45c030441c0c0c0001c180640054031101012440801404282c80040d406040003440010301c40e0802803030342c2180c1c06902a9031095440f82111207081074a0590f41c2c2d4040210300c0054006402003000d4400e11055603030000c1d81280d1680071401420f105550700102c544080b80d10281c50b0740c84d01400e042008144441d0038103526550001c0c100a00300c801745414030410640800769005019031402c0744800c504111079080300c4c0c282e1116185d600980700c4400580404002041d0740e03000301c031840384162025244241061000908600404001e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 786146223 1250 786144973 786144977
    0x10221031f030213060e0c04030503040302040b1c0b0916050907081305030c033109020906090301050c0c070e0705091306081b09010f0e0a0e03121608070e1f 69
    0x200000c0b015880300340c616540210844800585a42064600000900018900d07500300308108002d1000034004816141100d50684001c03980362213010005041c085d100c00d010f14004000c0103800107002e600d4044030b01465020081c1d0711500309580c20780c01084058000e007504940c6820102703400380d01c1031b50b84907070040149110481000e060ba0301c0c1d900f181c1c400d2080280ca68004140d03030072944804140891000c130500348100d800038080303034800308001e198811203001ca2f42c0403508440a44403042203504001e40100204503924140e5101a0b10790402c217240703c101d20642c0000700c0c4015891020341c1c081c90700f540750241044442410022040f22421a5580d4551680000185102d04002a03204600c181d100c5a14607001c140c00c1c40a102c805a02c110341041040c1c808000300b21800f80e4070b41d0045c1d11018080341049680144a01e140b00300d070b0f90f41c0b0101c40200c01300003011b9201d01c02d91a150440e9503801c042ca86130303a001120a030442c00c480540c440001003003c0d140851049100c1050b444c54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 786147473 1250 786146223 786146281
    0x1051e0d03030b090702070503150708070e04021c06030b0603030306090a0f09060e0d030e01020f0403031803020d0b0411010203040312050c0109020909010f051b090910180b01022103 80
    0x181001c5400c11340e0035600351015034402d407018055440c050111f8001107400c0544254a480c0a040080404e080508000184408486c5015054071950101c80601343c1d010403a00c220210146400001c1400c0e110991b1810944030120710f0383e24012040b68041c1c8002081c21400c0c1d114880301500410030f50b01d08180c01540c2d10b00a000050f094040c0301c03074080c401406840b15250442c40a410f6451070034456242d640f0400c040c1c0c2004101c01d090301c041c0c0740c0600c3c0034085c0e010303080003821440280340c0003e50702024441540040001c3c403955144114400d02680740c0e46a010300045e0727540e014500005000c980300c03a0350701104034801d03005840030341900e000100d0242c0942d00402c441c04000d035035002c45039455259503102c24025004a80e0414200c002510914890b00d074000494014441704a01c10805030012520000c08108210041e18102d807031001c0c80011048508000c0a11982d064098041d0104951a0b1202c80c0c1c000409160032509013459035903100303d100303040440000c0200d401100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 786148723 1250 786147473 786147491
    0x17190308100e0c070b10030203060106050705210703120b03060103020d0213090b0a0b0108090a08070c080303010b121e0103142a040e120f0a030f0c0309020901051e0d0303 75
    0x94071003141d018007031000b039180c3d13954220f00b80748003290b800409101124500220400050300d0000b401c2d4111406032401ea604c402451034220700700303607164a0040f603041c2d10322841c59400141600400d00e070791180d251221000040040502510940307094164103410020040002d410300011021440b44002c05030300049038040210012201800801d48501640c0410003100118901c5080d51a15090038440b0030792038000529581e503030508100410307003c40031a010080100f48140d80c00604118170a603612580c54810782c5029810241185109000400200b4000f00d02d119651241c50a0055484c0721a801c544400c200000180e800000901c0740540c940503102d140c0c10303240e401c0452540c6140140c403003002000243e403c1c400d070a4810383c01c00500c0c8a1b21300c0c58041190f281c481001c00d0f20b40c544c02c850750f0580003018000340c5c1002d050308109002000607810fa018840700392003112504071036621042400829262280030039045000294000c50901c0c0003000e03e10014840d03d0082900d000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 786149973 1250 786148723 786148739
    0x1d070207081b18071d04060308030105040216050a050307120801121709040908041e050d140106030f1209151b300e1e1207031b1719030810 61
    0x8000c5848000040c040740c05c0a0390b2083c80401c00851078800c8506014032400c5407607a10042c8010320505118a03400507030301e2030079000c9506c00c0c2c2c4000c0d0440701b910700802507810081c1c1c80754030400f805c580701170411400020541c05490b419058a10440340445464030311b99885000c6540d06500482004041c07044200030795490003420720303261040426607110361912444100c001006800914800048401407189807201800c11062940240e4020200d03001415582e0041615820192914020072042c4080c8060320f075916902208a5507203041e4280d80e0615a8188542403440d00700044500e00c03a4564084420071b500410b600074074054010416441c41c5042406030301e840102e403d600c1c1d0450100e490703006986ca045c00101602c031400b84001000781090940100c070741075407080c000760324422602442008810007840c2e0140e2061403090b00304c06600c165881c14401e220281c1c1034580c004440c074802040844042500d40711601404030035a4041d224083d0040001b18a00445980016960 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 786151079 1106 786149973 786150019
    0x2041401082a030102040e150901050f010c03020c0307090c110705060301030803190e1c090e0f1f061d0105030f041104020d061d070207081b 62
    0x21140b01404680d580c0b0040c0390b400d0361010030003096030180e50802501400c034041d0014410091072080021000c003d000d0390b40c00410b0440607031a0395004a2014440c580720303005880581c050800442d2801c04541e0062540d42d032920581c0002d150400c0000c11034031003002c0070b007101d2410040401c04510040c4401443e00d08000000f51200074401c030320b402c007200b81950602021009443c11035481d2440150310811146004600d5121405190128102c499800000039159031b52007420160f140018000030048036900e0b6035580366402d1010300c0001d4030345a21a02c03850b0f156a800c0620b40304441040300c0c1800010814032020100d81d600302507104ea41700e106a5502c00394071740460043d00503040120078680c00c0490114600c24140385490880c18043e0300740e281381e6a42807080783d031022a44940c2051341c000511810394000d2864082c0d545560103040740030541c50b000c980d00408 = true := by decide +kernel

theorem cover : BRFrame.Cov 785971223 786151079 := by
  have h0 := BRFrame.cov_init 785971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 785971223 ≤ n) (h2 : n < 786151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
