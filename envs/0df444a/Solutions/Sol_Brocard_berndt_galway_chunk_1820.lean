-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1820
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:47:39.278883+00:00
-- url     : https://prove2.me/submissions/b669119a-a5d7-4918-90da-c3cd40ddb697

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 327158273 ≤ n < 327338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 327159523 1250 327158273 327158281
    0x90a0605180114130305030d0509070f15030b060a1205090f070501050f0c160303031a01082a04151803030c080c0f01090c0e0a0b01091a090909060907061e0503 70
    0x2021080c0c80d00d482403800034400329a01d91030025281c0d0031520001404905090108ad02e6500c042025002d40d0350b103400e82c0256600d80540da044101030520081c0902d5034844071902d10b40c450ba4001e005600098440c0c03003140c517040080c0c2c0c0132620000d00309007481e04851322022000c500402d4001c100e030030900e402911034401c0c42000020784603108640d2000d20402031481401c403070796520801224041e8604004003648a002ccc6c1100d0014914030900050500002484100f090004840091181034241c0154451401f81185079402600003024001140708460700070381e405441280c000700840d61180003140b840d90701030100c0300c81e0303000140798102c042854099850100500400540c91000030700c802c0402c0c0c14407440250050062100306083c00f00000c14440c024000c1c0c03440048182c2da48964245007519041d083d4034441454405800d0400c41907116640e0480903a008000780c501130301d41c5042a07611640360404503840407050003000c01d0000031880840800456080b003a05007199250b507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 327160773 1250 327159523 327159557
    0x1020102120a09050d03021305090414010c0806040f02040503031207050c0601060f11010b010206150a080303190c0f0c02040506010c050a03030c031a13090204060b0f090a06051801 79
    0x10861200211580070081000c0310460b5080740d0603041c0520f0913900112800f00c030440a030b100f013110710403c0340d2400070100624102200c2c09540f043c062494100350607015210a070039111000c8000000031101e000b070010307915183c891340c00740d14400c11007107103824a4040401d440e0702902c203c40082d07aa880700010641d50050045480e83d108002c00d456880d03864401c05440104060200c4d00040c40d84a030084540d00140308100010105070010319641d62503080c0360740c0e9107040d40c400c1600110b6903031000400541c104007450084440207401001c048240843c00101e51520342158104000341e01c154003465040b800740c410854041e0f80c0403801d0395078040141d55035001003038028154440c00022205150785984180c81a0384c0e655400d101c1d25080410600c05800c0c49103c40d07603c203400c08175041c540078035540401c2c860341c800360020440301d80d1481e0003c8a60000d0201d403007110b800040c80c00d1145007105591001e0b0181e4145641032410720034021220580414070941802030740407110740c401d9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 327162023 1250 327160773 327160777
    0x933030b0a020304022220030601320a0503160201060e0f0603010605090103050a0501140601020c0d06140108071404060e0a0c0215090304030b1b07170c1009030e0a0b030703090201020102 82
    0x9207200e0b40218222806e00c5038030f402403a481e03075801f9041202034000020013108001b00c0c0e0003004140d40b1400940400215010a401c000494003034040740c0194405c0501100b0700030304070741c0c0b5091f1200d503200c1ca807401c84080300d4502040d44604592400005020450302e00031901e410503540c0d0400202541c0e0640030900600380b5070811a030100302c03000000100400050700c00c4440348a2070013840206015014401982e0007601d0047c0982c00c0300b9079039031190500294940c1024083e01c00451160403000120b00b2400d000e80000d441c54000c0031080c003906191804a0181c55001d89007001307414500000140103040240950b03240c40d888640c42045144200503418016000c14010f220506000002503903030340c480d110131030710520440000b8607000740b048001c0c640c3c0c2c0c4a007000e6614050791603a881585040441151101da01c0038400d001c80013104112024a01101250000310f510f0b00b4140074203000000340000c0c0c82040311440501c41c0ca84480142c0c3c0c0c001c0b0345c82c140495400c1891005034064 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 327163273 1250 327162023 327162049
    0xc180b0301060b04061704020f01030c030f2c1612151d1203090c04020721020a0b09011506030b040603170403061b05090f0a0933030b0a02030402 64
    0xd98205440407400b07003104001402100d0035034490540c01c9001d1505a403001801302c50196201d000c004a0f016154002e07008481c88141d43d18000a03031482c5031900a003110350307a050b01c1551190603d80d40d0700c2d0030740d0303010744405022002000740300000090794100c41e9441d06010307080c0d030000f60000325020010f10f0902100c24444019003131015403107005044c181180485814009032141c6180c0a0342c0150700000c880c083d0300e83c80c01901c09844204244006540a4481241d00c03541059041a00c07107100c0304040a4008694003034800c00c00c090070700c18000d66024088540b02e903d0010004c5031122500c0d50942207410504000c030707202c8100e10000b8010201540003034203200c070402000c41940c48541c005d000b602d01c1040200300c200325aa150960821403070030020f01049040014881e1460001c0e055601035800801c4100c060741c4540418040c0c418200104e24006850410401180044000d03a07951000c2d0700041501c140c90341e00c56843c09000505100301441e03000010030259254640c4030741074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 327164523 1250 327163273 327163279
    0x6010c11061e220504060b07170702060d05040b150f130b03030a110f0307170304020607080c01020c0706050903030403060f0b190306060605030c0307080a0905010c09061b0c180b 78
    0x3c80e84100c0754110361901107044140b024454150100e001c1c0703800c0c032450041d03500144c0c1142c10108541d80d0b502540c0320798001508001c2040c03101e0300061b51000000e160382c0b00100c901186a090501c2e14000d1260054a481090021410560226141c5409d88940b08001b2681f0403200068030029000902480011541501002075080010360b0000c01900701c1c40c0c8002e00301e541c00909035140c5501c074000e20000910303100d038440300c40d0601c0521202440d00240010251850600f141d036440107958022841d4405507500416003500074070007032202d0801849a814814a0b001040b00000c0d00c03482603000c02020f0656500705038201103000e51208284441c00303008107144061041000110303840e140b00446c2d10509242c000318a0f00d20410a4038082c5102c04001402c6d615811000c1c1c9500d603000b800302a6a595441c9204d01092003409000c2300414151100364809007003450051021040402c194901d2020130f001e80b0010346032103510000c5400000040a028002440700c3c40540484089568 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 327165773 1250 327164523 327164527
    0x7030b0f0a1d0a020109080f0c3c1008010e060420121b090f060c0a02090f07030b0904050601030609150c090609240518060403120806010c11061e 64
    0x821100000740f070b04089070007600c54540da2903403003415030768420741519a61010b40006a51011a0505000803a00801500d0928205d01014500c080489842450b15400418a1100c0d5015414043e0108030f40540c2d900d400c0c000c940c1030039a00e035041c0c20060300c590f029580d5a42d400ca4841c403803150401c00300c810060225500c444034060030808080c20b070b803480d03640070810380180040a024000c8a0180c2c00190413000421000c404000035a049046034580c035005150708440103995402030381d44a41e0f015144040b8038180910300804407003809041034001c415603014400818000580c503030440f130307200c9400720761020145086401c140000381121845030500c8806440c3c01d41120251095500503920344800d5940c1c0c07102d80041584640e500141c5800043c8200d43c29031094004194a010008141c00011401000319003507078001d5009a82020f17280d55003100e22903200714030300e420503002d2811240d460402d0716204042d9201d0a403003481044005080114a6481c0f525045080c6100d12100d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 327167023 1250 327165773 327165821
    0x6040f0f02120601090312050307110d0306060206010f030b010b0717070f021503131203020408070f0f0603060f06030b031f050f0601030e10050402041812090807030b0f0a 75
    0x1c2c1d00100c03000e8006800000015407039511440e107500899810003004403001d151172606840ba68805003c48007041404155032940a80410181c0d100c03a460f41d0340016a18603081d0020b08110068012140004070410200003003400e01070b449040d1608120f160760b580850f86041e500115428602c1c051254000c26034109100c0e503143c08400040c02034603101c0c80c8402c0c1d0b0030340760b01d640b00443e548000d802c0401c80d10301c04201c190314103048004d0036050051a15445200f1145010700c581d1221110f008900c2d424400c582c5d000c0900001880541014041d60b41088249845410701340122010580e4070682201c0d81c2e42c04100d5024210050500c4450101e8038250701c401805048943c0c11404211341c0118170254404d00c40c035034500c03840b50003800c6880c466019030400b030308000d042603a00c180c869400c086a40301c0c8070400c045040c410750300e072540c031140030310080d010141a52140c0c1c465004030004002041075240302c65070100090010748103940d03c2481d50342c02003c1e06200d44075501ca03021000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 327168273 1250 327167023 327167051
    0x8070e040b09030910120e0708160b040b07020d0305120c0a020c01080702190203070816061b05190303090f0302030d0b0604120b0c0f0c0d03140f04030806040f 70
    0x4a40114020306a003201992060802d568a2040c20705a0303170000140700781681c00b02d02c103250201e040306050002140310520900c8603482c002150708a0b0319590044100300002c08008000c0c6002864a44d280600702880c2c666105002d01440704081d01a141583c05c3c0c0042506c100d00702c1d0745101107811a110780d0f062802e0300e04403c0d00f0100d041c2025114a90000c0c0d295070280e187c076886007102e5030080842c50b80b10040c0e403020502c20a002c03a09489610804503186070103010155040382d42c0b00000c2d4915241030300051501c0356555044c420008140c8242002c40c00102d5100559100000301040b21100c80c60101c00402c00e440c0f01400030000215620105580400104002100d00a042c04444590020480ca51140c0d228480b485031216203200005001903125603844803140e0700302804c116401000313180a17403088840403900c0d0070000100140c550540305c1d00d0300481304100e14040e04e14040403203214214000c0c10180600601d1000500583c0d02e0350007c1100410000060054000c08421 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 327169523 1250 327168273 327168299
    0xc0f0f060305221514040f0317040302101812030501030605070306081c0c02120f070614090f130603050a020f040510150c0c080606150301140105130807 67
    0x500380001c1e0801c1e0105001c825601c40e0300a044042d046261004107883c0e0b0740c8400d4103c046403111400f0f80322070719000040c040501c01441140164844204030260f0314000340052070054204004014071818000801d40c00150405071300000a00010a890840d00206810310303820f88c000c21908a1949988610398541c000c28105d920039041806561600743c1c0680a42d074003402222810340c0f022280b07648005402c03038044042c145604010300848080e80120711301c035542c001c40d0038040d80650b04030102950b082000c24010811440c000945881d1454664218400e620100b44142d54111030b105e1641da564441d25009141a1030170051560f592034066120031100e1000da200e8102d07001044a942010b001e01845022110b43c0580802e040c0340340c60b84c000c9019000401009164012000001c80d940c1e002005440c01000622262500c001042085003000c0303444800ea010a0004010002c1107417941111100d00742400342c2c8682d0301944e04c580e00d400302e80c0300700c0305881404400070340244903c030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 327170773 1250 327169523 327169529
    0x20d0609060f1a041512080408190f0303150b030702010e07120c0e0a020f0403082205010f0c03050705120307090b030f04030806060c0604061a090618040c0f0f 70
    0x8184016a22a04801d00300d400c00c40340c110380760f500890300059030f1402d58000040740460101200b1855203079411086161480301d0121600718002606104102c800c011008000300e15181012081007295101e200360301ca4007070010103050325001c1a2441c03a50f00b000e1040500b40d80c0030b03599183e2510100c028048d00403040b400740c880c007410b00d01041e0788403d0200c041403543c002e141c00c8400c0385030421740d20711020000e200340304480e400d129103c8190006002000294041c2000350380707401403041840460003a100c82d28041142c401e03003c002c1640c0041c81065982140c2c103001c1c11011302c2d405c0507507851281140c000c1003401820209030f001c0c14014090b5000c1d140d00d1340c9011a00b40c0f2000c00302c800d4402641d81c40010002000090000b070721606102d503204201801042c1440301015005103000c405880454600c1e0f110b2020000c01d90300e00100082c0d4580c12107082c101e504000010494071906000714848001c20310300060280404200c02500800f81207000f119501c1d0307107c1c02110410b240c2c0c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 327172023 1250 327170773 327170783
    0x616060f1a0108040b070807020f0d0c033b0d02030f07061e020c040207140f0d0323190603240c09052d0a1d06060325020a020d0609 58
    0x440400c1075540b09a580611490b808100502c0b15110038905465242005100070110f2048480c6420410000d101c0c02c1013507207003504c0d00801c5c824a4507010b44615961a06002e518000304003919811446c05440c0da104119441c1407070088804201003404143d0510300a90580300ba0340d4100103441340095030804980041c0d850401e00140c0140600f0f600c200080180d005034030403a0a04940d18044d070003010b550b4400e050000c6d00680d070b0196036041028440c60480c0302d1b00002214102c080d0140507156951190400c410700080c500580041c604501401e0f100c944640854982c0000c221640f020703000e19003122031074501c020008040f03070071a10698400e120890a00c400b4041e0b807130144a84405480009003107028145080828060b9483e5005901e215640c104205646641321940480c0150035200780407015024a1800c40c18486d00c0601402d0003035100300704000c0952200752a00890182403001481c1d14210390508070710b04a01c40f20041e40c41081c4005001c20000c1c52340c0000e486c14483c03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 327173273 1250 327172023 327172061
    0x30506041202030a090314070509040305091201020f0406030f020714031809062110050709030c05060403170d0e030a050c10050705220f031202060a1a0616060f 70
    0x8800407a00d034004d90b18030310003044c0c1c070321818400a01c00320702104a08000381e0866896a0351000040d0f00402c0a407400e03000710b24001403002071418003000b13041217524084001d5240c28501090f01140b44036234800c6070101035a58814001400e071580440c2c1946401070b50461042244c00b030303466107075031040154029901c2d440000d09041e0400342c0105115038801072051010308800170f10340801c3c40b40d00014140701d01450a43ca1201040381c03040138000c00059480180003421b514020442c551907400061042d01c0501c001c200190280c0203260410700c2842c2c1094542180c4001c85002c1c094020020b100d500000c922040300035030200140400300c00480466100840d481c4200b0200c030b005680e040c000030010484100f01e040e40608195003c00c044559924071540d4140c10f55040c0d000b50821200c01070300341c1a5000e101e9042080d103130860342d940350803c40b0310b04540a141002e910010441d0103100f02052840c281c02d62070682a0311903420050034040c10302210100002003984002c202c0900c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 327174523 1250 327173273 327173303
    0x30a080a0e060c07080909090106060207090e0627060a15120c0b0c19150c081324050a150b04061b02040b0604120b01050409051509031303050604 64
    0x650190026110701180a003442d615900021006940240c1c402e07180c29404000c040b030603449408140d44141480c0b4000680ca83c18100028142071895001c2c3c89114180070781c400c4104000b05586810034101c1c5003002e000744403c240540b0902c045104102e00c0d005900c100140310003503400ca96405202c0b40020f0080540780e60200152180103000513050010300a400d10524246100070040d186210307044400c4040e0002c00c20a034480c4d1140c040750b5400d51507031a400d24090500a601d610100b50406895510f8255034903051008070f46070141c507980b00480089428291914034006020003104284046c1c0360244021001c0e20141c000000707654604003002491505a10582e81610b0407035551801504101c0f40403418030850400580e8005d40d42c43e000b400c241d491200074002042e0b0024682048001403c20400c03c48059104502072424075070709c1e0780001c0700415003148000141c84429603a803a080c20492440c000c403208e40018048441c004000e100d0001202c0c3d00c103d01c185040301e01140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 327175773 1250 327174523 327174541
    0x17060f0403021e10150e0a15090c0306051f0f0804032303070e030c0f0f031603051b010206011401031d010203010621020403020619020a050303070309061a090c0f0c0a05030a08 77
    0x4074800c1b5900c80c0740041c04174409050343c0c1c024810308035050704201702968032803180b413003210240c020f58004a642c9070030030400d40c1402919861550706007120504800b19407600500030f0744d00180c0600c00c1011290000702018081c13a01d10151500f0b04400800901d00c124450205901c00d651a1021640c00d5812940c1780c5000100d450101c40054144408480c1c0101842401c500203404194180118071244d100d00035055841c0009501a0008007242034104903100c408241d01301102c0e0454121034010710010350703076503c41c0111440a1030005214290180c2001c20451810180c41842d40004000200a030f80080c0c1d049088000c0c60800c01c00e8105200303038204901c5140300c0290841014480c504d044c0010304180c1c4944002030054501803442c0f41e880da800c590040702d038807021076500c0c6158420700509204031801c4854101c5040b0110540740001069044000d100b95160100014103c0014003004142c0d40d5038041f0000b207448004051074425140d4002001010000700c0240029142c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 327177023 1250 327175773 327175811
    0x7171b0606041a010c0804050405090114090703080f0d0f05010311010f0203040e07050a050409180b0609090a0b10030803040c0815040812060103022101060917060f0403021e10 77
    0x701208980e40f4916800380150782c0c00f110094182c9103940140b0002035561580d0050070300c50b4126800003e140c0349198600325403200e02500750380c00d940c444074080c00001c030140216850311900501250301c07100c8070380d603500243c8402142111020b007040000004c00c41040c28504145009032295210b904071020101d0744c074001e0b03108001c9280c0f92840031440c0c25000d00c00401940c4202e242240c603003a02d4180200c2a1084140c0d241c0103282c80004010510a050702c80640000c4100c0e000704003418007090705070361a0f14240d4042c003405140c5010900004108217044000c3d540482903d4a03450300d030904608143c0544556600c0b4003500307940c40790380702c500743e1442e00c280d43c082090381c140f402c0c090b0003100140d00108054103041e401c010082c8070000d11003600300200c2c0102e42d0b10a40b503040907001010514076500245a407806a00703004881400812039591124201e2004103241da69401d08918003800c2e04440d222021900f01e9490600c100400d1325a45038180e83d4050103002900d00030031f01d8407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 327178273 1250 327177023 327177041
    0xe0d0807032c01061a0a0f1e0e030705130f0c181712190e01050f040902071106030c19051303060e0a0611040e010506030f0c07171b060604 61
    0x205614841008000110b0396000da220420302000040303258407081401074500821402101140d4003050f0134001680c060100d4010140902d07140c0315064640040f800910071201280040c0324100107a032004d0344041003000020301c801000c440000d82402c0314280284504400404002c2c14951000001d500032000401034241880814020f00d140850041d2080c0c0c03078a5060305240074100405008044140c042d01c9442d0040d442c900e4030590407080900030100100c84a8140701040c41550454000c03202540c0071034004071000f5940e0500e034582142114484001203900c4000441481300900c2c201c000382034032601410316044030b60f41000d016a10b030b02983da207140080d060100140002100758010500f0120b03600100c0b0b1b451503140d550f500a4401074958400c0402010400704070089070601464010705d0700b6030f461071441c2407000e400001000d0050000101368800228041084105407000d20064169640c290b10380e4032181042c031208400f80c01e203940c07510403c0301060171850309210718490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 327179523 1250 327178273 327178301
    0x41a01031d070608071b080a170f010b1b030d150f050f04091a01060f0e010507020303070314040e0a0903080f1302040c021002040f2c010504110903010e0d080703 71
    0x7002d45008012110840000d02c40760410030a00f45040031040f10b40200c0842c184510750f8542c4551502400400040e140f440c4a0102e41d84a018408030717078000207600d4151a0040401030f0344612100c0c1d403054000c107420803000e45102c00a052070329900160701440c0c169110180b001e1486540b1611010314a030036001c1d5550010568815003501d107400d40c03250a515110714043d5000e9010740e50b44072003180c000d038822008030b40c0098072820704940c4010241c141110034201141044407580210f6600e000b9090010306005100302e02c00f040c0700c8140141d90062540d0081402940b509500c0700c8080c099407001100880c10140200314181c5032000e029200b05220b4145005030031f00343d020000035044840442040d80540d500c0207000780b256000901c0030f840c04446800d80d9900c0c0c200b40044445002138503d080c03103540700d50301c681d1078840441c160448408a501040e41c1c0300b0a4540752052084100f119070644c17805d40c0001d503001c030124400d18883c0e280c0d110407100340d44040d070580942c0d10344541c0a403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 327180773 1250 327179523 327179533
    0x131e0201021614040207060f090f03120c05040510170406020403050c0907050d050613020c1513030c0312060909031e14040b0c01090209180c040c0f1d041a01031d 71
    0x1403d41001c1c1e000e051140d014400100315181c0030400e8000b104e4071102d05035003485418000d07030306054100d107030002b801d407902d50104100001180c004045000c2c6000d068842c004003040d04000c1880341d828002c40203202680300400d810301d4505080254014801201d2502402032080c1e018608022000e109880c2c50310794502c0c11016000c401c00410000300490362000c01007400000000661010b40314101d4584002c5c082c9000c41c54031800480c00c024036404c41c40d43d03240843e00021b5400380d1200d034040c0d49070400444011000c00a5409021a03801c1140d443d81351035190014140d02c80200c5442c00703d5a007030368021a91125040714852000140b5034042c0504100801422880c1c0000b0a000006803000003042212540000c0741c15a003601e4a00c404078036404106036144080c0140c3c94807203011a42000345450404014044c0080c421004091003a041c0d18040107040e8501081041a8010010400c1c08804403a20362000c0701d6000150000c0c0c64500c1c101d40d0b6100b0301420f00030080050004007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 327182023 1250 327180773 327180809
    0x100618200a030b041407121104031718030a060618050108030a0c060603080d0603020102070e04030e150c010507052d04030b07110f0a030813020d0803131e02010216 72
    0x10b000303080b07a000c0407508590340d1744a401400d0910810f0902410b9941d94940c031541c400d407071107001e0703800201e400da00c9140c080104200140002910140458044509948480ea520107850600c4d002ea6010b98060052000304020080690300c408250b0302803813100e01c040c5d402910b514040711f80034000c1c0e00050f8070401100c0000b40c02203001444c210311482c5c0100e13503591250340d0b40b103468018912400d40f1a0f120101401150b03014019600504100e00c0ca070a035501c0d0685004110141100f81d07940550b55510885040d2514102155600d03682c042c020320090070800c50041443c0d00c2031030300503010b900e840c140000001d80036502c100070124180501d410b19045848910722000003605074018412040b540509600090241c03910b10b0300010081d142d004114103000c4e01100c0001d103680c4040b000c0c112010016556248404280c0e41c000c21030540f250744420426503021040d0308080c2130300821141084501e04100f0310030b001c0324400e07803d0310003c50601903608441040c034040e0f0071302c00900c0d003002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 327183273 1250 327182023 327182027
    0xf070c030c06020309190809010224010506070204060302031e0613080301030803070c12091a0903031603020f0f06100b03070206070f05071505040b010b130611100618200a 75
    0xd542c10a02e00810380e031288940c01c5403041b4030070001004550a080114050290b5a018400f44140c1d050800300c40a4050b814180e0880d2800140200361103800c01007049025921990b2111000d154060200c402401d03014100e4074180d0b00036640c04800e0320800000480300009902e0307007144150b00c40340301800e507405c50741e41004a4200034030380003c00c88025010000306d40400e102d40440c4038241c8031454041c0c1422500c80a00c6000341d40f5103441d40c010001b0309403a0300c00100300c904072001040000348000c1d49180403410002d0b02e90300415603116400642035004400b01d1814001d139901e00345880b2180d80d903006455240403c40b068000361308414001907010740944110061441d680c1340042c41c00740556180b521910180440c454141d60380c400308010080e1079a145c0e4054070881c05054249051401384034032017003143c080c1c0c2c02081400140303c4c800080401030090040103511007442035640301c11790040c4110310400600c4059040c038102c000900174803c1d84483c200c1d801201645850000c19003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 327184523 1250 327183273 327183277
    0x60506060a020a0f02030c0316180b0f04020a09180e100c0207030f030c05120301170c030309040f1401080319090e01050f01170906090706030e0613050312010308030f070c030c0602 79
    0x5d0382c247c090702d00c42c0003160360180610441d0340201e01400500c0750421062504283d0568400d40c607551410f0710900260703588601c0340300040c00456002d030707940400c0d2504503010043d984c0901084900c166420648034503c0d041203d02c000c1c0c40080751481112080350f681612144047c4002513040719500f8404640412001d0314528007a00f404081101c040d079440c2e28003107041d08003149814010006102d40e400803042c031191900400c0040400e13003190f100080d02d80c030411102c103200310395070f03040709120700030030b0700503a566800340150382d9019a9260007198403540721501071101c440c501d01214604500035808041030741c1002d180c0354050303070030300b0b00f4041b4400b400041181071004000040c040c1d00c41049010780716101c1c02d40078020314200a07110b945001ca294000c0402d05080005920480c030001400701c0c2d206802503042004a0b11a00b0010300318411081d011024200c030030004020303c05071000440c0039110342500c19402c2c0c2c6d2601011580c40c14070100082c00161070301d240801040e05500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 327185773 1250 327184523 327184553
    0x405060f1902010203040b09060402131d0a1214040308040302010c06090803040302011508070815042306042306070e010e030d0c02040c08061f0203040b03070507060506060a020a 78
    0x3446890803880d410031a01100c001d252420050f900041080300304040001441c1e04129814000c061600f41680001c01c0240070320000b5102c0c07a555901d4102480e038088881640b800e19206642202549042040b81c06548042d01c20110701c0003401c1c01040489102160b007125000700307800b410142158011203180360035020648a090300c540344403000c0750800c0c00950296119400000780702c18001c00c07007130000143e07502071002d5421080c0c0400c04c0d08008200000e0420642c0c605090036901da01d80000321001c0700c0101c0d0789012000346001d0b0a420001841d0b40240d0180704080d480e803000d025400e9150514004c030301240c0d0002c001060405001d0106440090014100906d20290400110346001001911030340022441c07489001503040901c42c051601c845440d0040c0c0c60701e40303e400316070001440114114200c200105469045200340281d80240490000080c6d4034100b00c103000b841070f00942425600380b89030602003145c0385445070485500c01e0700354001e002441c005844034030401c0300c400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 327187023 1250 327185773 327185797
    0xc01020702040f0e01050c09060a0e03030408060702030d05010803040b0414040b060a0c1a0402090f04080705031c0c020a030206010504020c03070807050f190305030c0a300f11040506 80
    0x481420016030b100d0003001c1008400c00e800140e00794103c43c0e40303402e440b005403000d103420000b00106001da8940e40d04484c4000e80c58101640d2496840000c20310750f00c07681d0301c80d4045d0f009400170301001e81e6006c030041c0680e50288005014a989460040b5203904c81c502c2000b041132810041008020300d01060b502a00744000c0c80090002c850780c01003101c0e42d01c032140010010301c54042d07003401c1110420542c0280b41002500c003503d40703403d50110350788134030241220715100c44a07000141040030601c102e0b4180d65104064a0702d40c200507207070f602a00e031090101c104c614117008980c1401d07480043c01c1140503425900805c250391800c41804025030066150380007900080103500301103806440101031041c4a080200320340d11460192030b00b441c80b4035800400003112251440c0200781c0c4001525000004504516a590401201907a0350356006c1c1c500b004003c0b049100140c1c5890071074045003090514201030200030401c08000088886e00943c495242c1001e004c14041402c1179030180c18105050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 327188273 1250 327187023 327187027
    0x6090f090e100608010b031e0703060e1f0510050d1205030709030c030f02180108030a081009051305061e041103010204120b0615070f020405250305011707060f050c0102 74
    0x29079014016505643c0000060785c6d100d060032541d40c2004c114240c580e01c010480d101042c601b542d0055140c038207512000c1d15094641c1854081803005121010044001e8411001503021103101c110140c5011200030040032402c00000925040c40c415011906903c464101d4034031007040010b40c0c031908054041d0f010030068180c00f10008042400043c09180120780c500c2e030070140b03481000540c0022000e03080030740065600404c16840c0003c00e40782c101c003042c2803580096540380c03c0c00a196807182d0104000c41e04060612245201c01030310b681805000d101552482c2d551005030031052013018410182ca003d100b8000340c0030444110709074108001c01400549425916410015051742c22542521100c4009013804420302e04009444000416410414240000c81e1506038440d2080c80010b17004945078400140790080f00748000c00c4015150000943c80107039860020000c00090044414200959490480100c2e0005612048400c1c959940c4445011180c08441c60303041600490b1840d134007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 327189523 1250 327188273 327188293
    0x60c0d18080106030507090c0203161205090405070507060c0513030209101509140405010b030103020f0f0a0603090201080105040b0d030c030306150c02030c0927070b0d050108060106090f090e 84
    0x7805400001d500500081035018101800c0400300c0b10100000015503104000c0e21410030350b0058be50306041d0f001240014804c030415810741d290702c038052150398440d10b040c040084e4560450013801e0301a0081008004030300881c0c00980320380c462500d5181041c0241442000107290148210b90300c0121554002c01c007543d02e0468070304a00070743e4081008038244107400d000a41e85c5c00541048040112018443c9514140c0421000d1006000181c0240d001340d98220581e107401003008030f50315001d05034811490707489200a0042c1440300c0304034001500d4000001ea207281600504810050041c0400c20307440090b5016210a04405405c44c03e064980e840003501e801c0c4030944050303035021038403128940181481054204005450070911640010381440f4060082c083c0d111540710707110241c00020a0701c08545481d10201342d0201c0d880b1040010b03803940810b600d400203070403689030b0411122180d803141415181c0542a00814031200c01d003030700401c84482c0d190070010144461005690001e51 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 327190773 1250 327189523 327189539
    0x206030c091917060901060b09010c02010e09040501050a2409020304150e100606110615010e09040609020406050d031403060a051002010c0f03020f1e091f020c060c0d18 74
    0xa501c1000d040484000b4803d0300c078030a0061a40c0720507048001c00c1401d00b0011141d00b80d004107401e243c10424200b82400441e40520501444c14800a00b40b40752482c0624206010740700c1100c0803181941082e17102840c006075420382e02c11010103070f035440c03c0fa2800d1008020003900024001d03242e410b0060300c034444102c1144503800c035061400d005000000c071049001c1081c0c0d252980a44100302540c84011564500401c25039004038180500d940861841c40040343e5909903008156030002e20b0100f80010041903a00c40c00e0b00314400c2c0c9040c84899614020171070f444030024005404074000303245031107001108000542e805000200074174040390f150f00104a10051003000c45025030f42d10a401c0d24a150447c0308294003101504d019450014282d1032409a80586640c002071902c03d0002c01d2010040c07a01940c200f444003a06541c401e407038084902c0075a400d03e02c001e0000d800341c80c4000d5281d003004011140318480e144001c00e04811000000c5030010240300ca402c02c0b09807403135408500b4407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 327192023 1250 327190773 327190819
    0xf04030209061903030f18080a0f02150a050301090b01020c0307092d0e160501090501050309010e2e060e011511010e0c0103050907030201080c2b1b03090206030c09 72
    0x507010b0382d620168221707460380c00344c1047d07440c007041c0115102c000700401c04d11900007100d043c8150310080a1105807031602c003055410752040158480301502084084203650320601440c12601c0c44070050066124003030040e03884d1680014915003603008100700784200c440640142084c5800032188440480d51440c88504400d840000d0554613900c2d00d0603138a00d1101044200d600c0d8200050660069280c03800183c2420500d01c551418008048001a19520207600000150f0b01a0b000c0e1003006140d6601c04c001d0110295504001c40c000442d01800e2000c14403554055410562a80403180d08288000e40c54200c0d05401d6010800024100d100f06a42030144072128040c42d03000303004007080e000014040da440184541c80315840505d0400240c1e0f4080b01c1b9030342003074682003e01c0da5900100c0c8850080300400c50300e0703005014000c2c01d403107852159901c000002c541601409079108503000f0110306641450790b0280d4031000c00c2c00420342040521004041690b00104a01c1c0b4011095403540d01103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 327193273 1250 327192023 327192029
    0x1051216060804061b08060d260a09060e0607030e040e010f0e0f060415051308030403090608010b03040c1406070c14030c06030c04030b0c070813080f030f040302090619 74
    0x1080b5805020802101c1d00032030014500307001302c8200a114402c1c0040c84030390000d101c0c0303201e00d007016080d1092045c0791725203880300b025003403181e14501c10914094800f03501c071030f0310080024441800018540d10914680d040701d9402042d0300e00e001340b07e0700c08403400c00440071065400342e920040c40c803000c2c0c801d118010358411320718404100104120900c0b400c05d02c1030f00c1d07210b4454014408001c006050b040d40c1100003024454002407d37101c0d41d00c14201380c049443d0081400c1400000d002c140354001c1458000ca80e95a92256100ea0b2100911611800705403401001114090f038140708010660b0300c41100c040000d001a070829060303803503100c400c0d003e0b5800881c18800185102045040501ca060b000307610580d140c510310700b000c030300311071051165100140c10303c010380e40850000b081410449e4241e40d0055505a00c1d045001c0480c4030821141c8100340d240d01c030b80502c3c800049804400d032803105022081c8241414a1602403001c3c8400007420a61300c001b101c400c00740c4031200c1030486c1c006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 327194523 1250 327193273 327193277
    0x21020409020d0c1b03080604270807200f0405041104181b030201080a0902010c0f050c01080106140403031b0f0305030702060f04020d1509061811060307080105121606 73
    0x410300507202c0c0034003885180180f13a0411010340011901082c0c121203c603401c114140e40001e0800c1c071000310001003003a4100128482d034400031208080c0081203010f8210140600c1804410549001c4031010003100b4500103504000c04d1811412107103440e621190b0300c1402201613000b10404100054100e410070307850740813056001070301441440741d4034840841e51b14411600f11043c41c1150000381c1414402481d0f85092500d808040d400c5911440f000e4410b203038001c01940f45150b091409075100d501101c0c0003130028040300000290103100304802950392118581131454a81540c404464003900c4144071480e00f071140b10000001070f484a1841d0f0460300aa40d899103a080070a402410f1210140c084224020118103100140c0c2e140420410711660081c4200d003842000300e94040a0517500c070015244914210071542030354120704000c200d1501c54141943d142d07040d6410800c840c001a6400800110440018000e90034001d85030031000711039100711030350380350707841c00c000c450340041d820440c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 327195773 1250 327194523 327194531
    0x70f090b040b03070f1d100302061b0d03061e1809020312030106050309150601090e04060b150406030b04091a1003150204090b041803050a05090904140c09010621020409020d 76
    0x84641c511b040843d010002111054045e8240788080b2552513141e800044d21405c1d000804006d000c1c480300c0e10349410500c100075211504011746001d03004000e113108081d04064034070a1102d505405c06060b0301510052061920000c031002c4441e00105000c0f28100c1c0c26200b4210b04c003000b600c0030f4000e94000d00d410381e41d407656881d00e0b0300d900d400d1034800044010300700295020f0001d00e80c3c00c1404038040d00c40c595025062550703681005401b9042940341c06070009444074200a0404841e402002a100c8503101804400101402d00c001c6901210015129114a40d4902c800450303030031007a900030344c03960340400015880c2e0321444001c0e000c003180c0c02411399001800308010342c0f203405104280c08003201c04002c00201300608072840c008070b6400a08000b00007032900c1e0400d01480c10340b03a06080c0509440585d141c58940559525581c4070300c00198440e42c0040d0310700b4546144001d0503500c550b0341d0400207001d04038028822900c40c190111080c0d401f408080707521102440540f1428007500404a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 327197023 1250 327195773 327195779
    0x90203060a0e1b0d06090e070608071b02060703020705131a0a081b01020f01020d050a0506040902061803010b0927070f0611030906030405030403060e070f090b040b03070f 75
    0x10000300155803142c2003501015040103440401101d052a080310000d00090361400501180401000590170481180345015802c68400c80000f5555065a559446003480c0341c4600606171004130003101e00030500542001211b0042c10100041c1504501c28012034035003984800002c0c411300504610501d84940d60300b07a040341b0403181d0061070902401940c14001850510820740e885803000c82140200100c0d01140002d1039100304424220342007480c0c0219211025000c4100c05400181c510540e00c5007420085074003440d151189440300c0d039000302003901e042100e80308104601461038941354555602c0200402507150341d901d0310320515000c0070120781c450b4034240c00e0340305805010304003540390f000210902203a440c2d0450101503441b2400c04028450f0f400c40340529604c128490550400004820300003080b200102600549101d000240305504580300b42e42c2d5500f0a610484c40ca0001c41c4508102c0d00b002c035030020100d00da001d0404105c0885240c0440e2408286500101d8441241d071410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 327198273 1250 327197023 327197029
    0xf0605181603030e09041703090f0f010605061903020d090f2a170703050a030203040f060c0c0506030408070b0711010c020309030705010e190e16020d091e08030409020306 75
    0x11202220316104001c4101e055071001480e10040d000c049002d2400361010400780080241d0314000e03003508140280d1303a89420300f213042d22a004c400300b0300c103588140781407049a0081809101e081d01c802900340c5007070403000c072503802c0d22900542046d82450b500f0003049903100c4039800b0304008175010f84800e20204030240341c130b00c800b60020003804c00780e400c0c0c91349602c40c9080c00b50181c07812a00850640c49521100168980c14610640e01c0149a4400c88000c0c808058012000d841107030b083c40d581104040e940c10003030307030070300707030440f00240b118400c42020700c86132030414041c5400a010385d0415092120742e03905d0800c840000e032116400324502c5200c100350310000740a132400c04c1d80750748007039030800c00c204000c00c1d51442c050042c070741842000c101417900c94075108017151301246200080e20a05546c1d001c500c0040b20150b40030092038049020320304582c0d00024030001e180345180d54104842e4504040444010400700207800c0c03a0141101c0000d07a00c0b403c102400180400c030900580c0d0741810010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 327199523 1250 327198273 327198283
    0x1020c0a0b0c030f010b032d01050a290d18060b040501050f0d0b040203011503030c020f0a060f0f210f0f050c07060902040219020c030708030c0d03090f060518 70
    0x60542d0b003101002049202440b4050f010304403005078545a45039100d10451200c03400402203c4410203041040c6628038201c0d00c1d8200c1e048035404d6400481851320703007003540d04051200e0301c0035809020f101015400507034084000c00c8600800cc5001071420f0043d6442d03040d03440500c1050310515100c0c0805000d41c6003600c034040c0101000c403083c1c684002c8050120300d903a6060340380680702904210014040d03460a40004445a400b0070190040c207440e45005020114100c41c00c2e400358200962105d41030402601e03c00540381c0a403141c000100301c00104440900070b40940c101084000762804480211030042c0401d070070300c11000402c488040c80001011100112a00f0401a04044c140300d082e032011003c503400141c0020b00800c008040b800800c0181c4501304110200351004801b8103400742d4049900d0003100412000d0f5042c10390b0f00c0040c01da69014502c03550f001500920229420503000740d11007594144501c3c01084070a40644500003254001c460700d140fa4811820700700c003110000c0c05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 327200773 1250 327199523 327199531
    0xd050106020622020409080f0304050f01020a080f04030c0602030c0919060509190b1201050111070302010801120303061703070c0807060c030e0f150c0d110d05070c0801020c0a0b 78
    0x8002d11282c03405001078103150382c5400e140791980e01000a0441991543c2c1c000191440c0c10907403c5a884050425400c281d42c822141a9024060080120101007060003240d01e6601d55035190001900c500580c2c601010024204038288261385014100080c6140041c5200d40c450004150b2144805024031401c40c1001101e117402c84840d020610043c0c3d00142500c1e2101000d540980005c0741c4a41103540c241e0443d0850918061b0100c1c80103102c0d410030050303905840082e40d031802018810600e0300c0e650304ca1400001d000c22a00f038018086421180c1400c28600d0091801154040d540c0c00c40c0b41003400341400503c116040050303c401440f070007a8440c8010304020000300111454180c00500c0c1d07401c3e03208020204442da40034000c095850103250803440d6401003078900d01c1161580d150f5240d0f80300c424808100d01405254a140c18040c0c101c1a050032003e0000d0410140c00c8102102c03142d01056044901031180c002c0452a000c1c248040c140d01c1c0c40c00c0c0010441444541851614050028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 327202023 1250 327200773 327200777
    0xa0c02030723071205011e050f0604020d2705061006091e0305160e060f06040314030c060f01181a121207030504170703081204021906050d050106 64
    0x4400710000d400515004210070340c0d4800009240704000308142090101d5200c2203910350a0207018007440300651042d01d41000001e10410302ca1603240c005020b0b44c1e41222030a000080003c001040c43c1000d07002010101c0582c0000960461b0280c02c402c850840c44c814640c0b917102e10690031041040400c07260790002040081170060b107140080007055825980214100000400725403489860b040701d100d0080c3d035000c400d4641c8000051019401ca14082c0301e0800c03484070a1011924508080003071280035580540b444e49064210340b0303161010510101d01d418203100c2080b8007454504140030050042e00c019a030f90101c3e515200103864216608080002041e01e031009040740556000707401491144290385071405034151780300007030a0203c1035000c2549450700040b403000309a4028014800d6414162020034201c18150810382d6815032800001d001c0c52080012901d4800003543c400d5000f071000340140c6c1c510002c0b07201e01008446a900c58404554080781d13400d0205140e006040c0500494 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 327203273 1250 327202023 327202027
    0x3050601050d05100b0d020a03030e01080606090102120906040f170c031c0f0c0804090b0102100209011b050708011803020d080912071a010609061b02010806090c09030a0602030a0c0203 81
    0x240c940c00c0d29645506035400b599a80d80c800641d26885146c0c40c108100d0b0000e2090300d006650f8100940410420b111140c0090741020014801c0d2070800c095403202107060303005058440e9803c250a469600c41080c0c4c0e1392014090000143c11740f4000740c09409001440b0a050180c102442d00034600051099a030b1312070f800c4003410000c05401e06218600c4581c1500e0324003208190060103485441401201500f81c0d14009030110b100f500540052445400c00c1e0b086030800356401402104074001c0d044403500051242110f041410409080e4210490281c0180d50743c5580d2880d00c0703421034400303040b46801c0000000d1142c043c5034050001d9450004c50b42850403403864500280d5458000341d002d03416201c0804626203081c0f014408215100e401000b21a0b9a03a50311054041d00c4c0bd8010721400780066000007100f9810110316908500c00380d4182c40350501602e0742c404003d1520700007043e0f812074200034010603849035010059456443e0144000590702c7c28020b6101d802c0e500e00341f240030255402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 327204523 1250 327203273 327203299
    0x1c0305040f0305030a090f0501050921041406120406090201110d0206061005070b0405060103140304080c0d06110d1b03060602060a0207050a020907080702100903050702040c09090e070305060105 85
    0x100ca9a05412564140f6150795a540c94080341c10080072603010140003129405c1c6072808004055122500903110442101d0103181c80400030800384070385140c0d0200321001800b04105850f09e065501c0e0f40700f074009202d00d085c012085031201300483c0484042d6565625904500107658121281848200300c2c1c40181903207501440303020390364030000f0f8145402003c0111400540714801c00550340101e40c4101a07904500300741c02c00b0350781c1e41003c0c00140d602448070320064800b44000000c0f03e08403542c0e04040d1410350340c0b2200300301100040810580c1c40304d03101c5010fa0701140d07a41c0c0041800308140c400001e40765080022550a18003c10010410b15241038001d225950700041e0003503024100a201503600c50507894220b003815030204000b90000015002e0000094008010394420748041d0300b204c141612030310018041d00c560400150124608018450150902c2e4004805045440c00d12143c1290f80754400702c100c4a00f82d48055803074210079024010813406100282c01400200c51641c19803107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 327205773 1250 327204523 327204533
    0x150a090b0a0e010f050c0d020312090609060f04022b120315030605060d0b04050312070c0c1e081b03151509040c03080d0204030618150209211c030504 66
    0xd02c0301112070500140d610045409849441110420542e010565441d2030480710080d54a4002446076284101040300244510000090440c4240404002040b6940b00c07106100c0305450050404e9810848400302102483c15030305d9208440501849400d41c1800039082040c1b9001c4101940010181462622b0006100041540003035a81203000081c0c42d44480000500c40c0c89601c00007020010482d00b000309014000c40038100ca0401c82401c1c800c1c503034134018101c4a5502c030b0000280402220310003448403041c0b21107503017000c3d0020150b445003d510344a00d0b0340313080c8040301034524680c0c8401d01807242c1d0600384955044010710400d1020582099850b06001e0011311164500982c5800009028040841c4006000790381214480e40c1c0c400800c01c0c420003079800f5000a640140c140601c0c2510b4086009178444d2168000301c400d0114206140c42038040e40c044404180d000c800f40b204040c008841b00041c03100b0b855101b0041c01c1c40090440884510301e2640000010325103443d0400c00461 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 327207023 1250 327205773 327205787
    0x80f0708061803041a030f1e0a1806050103080a090b09060f070302072c010608091203070e03120c06010807080309040f0204170a0b0c090f120c150a090b0a 68
    0x7500b8024103002c0881801103166026980c40980305401d500f00001000104100850184c56040440141c542c0c030a851030114103d1032a54070305005003c000102c01401c2c9a1080102e0b00050349070080c0e5201d951516401e490f400c1e0003e44000e60005035902c021074002554000601c41c8941c1642000703001e200150050190000a00781e0400024154081510030311000c0050306070082072a0f09102c0c0000481d01000502403495502494080040b52141c00744525034403415041004140e80c542d0328070b2540c00d68101400340d000b4040c4030400034000d9031f82403110300b604680342a5410344904914801d140703854010303806400d035600815024018400040100e400100c01502c003c203000901d6a00c64000b07201e00da108021100810b514449600c2010030034003400c030300405506c60640c0711012480318070301c960f501203580300c08000644003043c10300e400207691084610099a8107445e100c004268541c1c5500c41004481c40001034001d66140c1090340c42010703180e248a424141045150040d00780 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 327208273 1250 327207023 327207031
    0xd0329150c07030b0702010501060f0306051023040603091109040b0a110f040618060819050411030105130302070f03020d030e0411160c0504050c0f0d090615080f070806 74
    0x81a0006604114038001c0000d03400655004e5041000351900c0c0d04d00a000b00420f00841f4002040010300108840c070030b00512081c0c03080200b0403000e44100c2081603582141050007219680c0751500c50f440464080405000206100e4a0100362100f90345000c0040c450f541804038400c0010405110100d00203500445d40301a04040c0000e403598401c0d2035068078058001361802c003850001c0c0100300a6840301300d819900080311650000301e42c4890040e14006421a030b258040e40e204040042140000d800650300680a00c0c074844011007044046404e560040b00c0306c0e61007642c1003d00104141c0c2c10000d840c0207001030b20440780c21030705503070004407402100c500260401c4102c441d448182d0741c55034030040c2c0c2030742d03881c5055079110100c68080801c199441025603908921f140002414180342c09003034400c131940c10040745130506001b00c012440c2c1005003208000303031350b0b5041900000c503140305400d1500c9074031fa10200e109203441c50752840c000e25a9a203c2e0703079400c001010007660100180a03a08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 327209523 1250 327208273 327208309
    0x31e0c0a0803130c0b1c0605010e01031a03030406090302090711060c0a11101d1c0302130308040906170a110405060d0b04060b030c0d121b050d0329 65
    0x1e2900c0308120080051410503001d050301c01d0805000503a480305c80018450310400d0382012040d480c04901410441e240d0f031149502048440030b882846604c65030251456040c1894110000ca04800109145812540104011455100c424407e518001d82700030703400106031814082003d0509081071b21818050074081c0110004503560f114280914000481741e240842100c2e2400d0a1525040c050b0407901c0800c0342c00101c82a0040516102040d03c02c00b5020810412204001c2d4407001c800035030016000c041400402c1c5004000150b4000003000105540b90021420701e041c40014116844001e8504043c0e07400498081e0004120f0210311401070006c480029030741da241ba001c51a10916032500400c070012040401003041000d0f8052903065005900b06d03500c60070a00148176000c00c3c01e10014004030ba03040320710901e03a0310501c180f034102c900c0140303520415050b40da07426143c204144010808281c0b03032001c5401c607210340c0742035035500305080c030103041f5036031405000c500e018190030703450f284c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 327210773 1250 327209523 327209527
    0xe0a030c0f0212030c1f09020a03020d030908030307030902040b0405040f0b100b1c0509121206040603331b111626060103030509060c0c030f031e0c0a08 67
    0x790f5880602080038140f020f4142d0343d070340181381340d066190f410840035100766480c00407101206059070302c102c01e01c0d26405405c0480d910300790340802c441c100402c3c1e022010016081070114641205001030750141c0466140419120310520412013a0b445a5041c507000341e2410080001144002c841004100d0700700b0710740310440d1903030520f48082c42c41540000075129030004226081c403c2c1e00b1412500b20031054000c0000b070b252400c1c110740302c07410000c81c038a02e07080038000110000c1110856a030021001400040e10b26941e03503c0301c400c1e030320300c1c5001882404016041c4111803400c0388441c3c2c518440803410030001c41c030000d283c00450b5000700c1240800c4a00c40307414104074020020b18212000400d16a48400e0361081e6213640f042c0040b20b02801b001d07400320340c1c0403000c1c000503005050704d506464240c20400180f0602c80c0c10f402460324600c2c4c51043c1d21040b502da44060207040604504000516a180718918203214041504042100095000c129110f910000828582802940070312195 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 327212023 1250 327210773 327210803
    0xc040f1203120c0e011b1718120d180810051f06020304151715010906170609060d0c03030f0f050f0405060f07051b120f0d050a0302070b010b04090e0a030c 68
    0x210400c3e1b4924004200304009440d400304900d40f070024062030341440742c03548100740141c0d00f48801001804a5194035030b0100308102e100500880442920340380c1c1c1140300f007049a44880c814030700344003805440002c0d555801400312400c0c8019280c40034228644806105504d0954000d6680c4a80d110351910001c00c03611104a0f0740c400c12800d4070f03c0b115030f50010600d003071141503042d202e0140c03440c6030f022550703001c00010002c0c0035401080c80e0b044a99070b9111190741d62800c0c4650944001c01d5641d11403004918080000c0c003100c030384ca004e140a1341c2c0f00d010400083c0343c00741414903600e0107801440028010348054003a160700b02d60907a50203642d070310703184c40f4014002c070064001c456000780580100b144926440c4842c0075408903140d01241c8216140c2e14a150054680d49900d10054480d00400141a03441c1d0140b0000d2403542a9031800610705a6541c51300f012440c03003a007214000a10008041001d480280030f10044e40801d2800361014000650707018000c2c03445120001d00d414410132003070f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 327213273 1250 327212023 327212057
    0x1501020c12011104090c030c0f0806100c0206030a05010e010f0b0403060b0a05060408030a020d1b030c1b090b1305071b0503090a08030306040501090b01170c040f1203120c0e01 77
    0x90f42c840c4402d0b100542c44503100c2801101420320340030604000b03481c06030048a914031451496080012545071451207031070f200d080c050606070081c02030b0306001d850240c810040e00c42c0700085118074807403800003810354104041d100041038181c0c01210340702c20340380c000d02c206503107801110111f81d0701c1000016201d0b10134011990042e042e520240c0d004802180024205001100410300742c94a0790075109001e40c0a04252228080001001002103940400000003402403a047d0324050041441d041d4814002250044100d05074004040c2242c80b0485c040c0c19060510070440c882042610500061070032480050140f0b1a51141544000342c40c00000c0034020184215110400c01925000c002d603140c3c1212641c0340d01c15105980590318010000901c00107600c544110010144d5401262000540c107580a41da03000e0a10203645004202c0042e501c050b442c4407034020040b002040100c0d24a6042c00b62401c080c5408080b40c00c1c4c20242103c100c070764040002c030748140302400e00240444d24100d1b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 327214523 1250 327213273 327213281
    0x9060f33030934090b0a03170408010515100f050405030102030a0c0e030c031b0a05090108010c140a17070c0c060809070504200903030f0304060c081501020c1201 71
    0x1840c05528000240440c81002042e456032000c1d08510002d401142d44285034640100884408808480c035007092000e076845402048a000000b0443e0340450380301d40b1144080c4022a400c4c03490b80c140054104145602805806d51000741080e840b80b9402940380803c4d41c2200018101c4208101184078406407400344058501070840234000310340740e00c0c100b40120010312110802e8404241d0101580d48149000210b41c9001d2501601802880b003903007001ca900c00040540741a0311203202c08000c62241c450503034942c001c081000c00401c10300c82015025000d68003800e41001d030407000b003044c505c600e07030000c0d034501401c044004410f013156a0010121407075540044000d00d844041c080000300d8070703401000d0a00070341e109401d0b6943c8581d1207080008440712407a010800b5042400801c0d84100800e015181c510809800d5900d40382000700c040369140d10454040701c02c0c1e0340d2590b604817903e40c0a20450b03444180840c8404040742c1800c0040e40d2000030390081c1d072082d91031a002c0d40d221002900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 327215773 1250 327214523 327214609
    0x110405090f07061d10200a0201090527070903050102071b0f0b04060e150a080906070203040602060c030402010201090507080318120606040f06231201050c0a030207050c1e09060f 78
    0x1b0190f501200c541d2000e074580340310f040140e00188a901000c43d041c90b0016100d0100808210303c102000c08002c11910410801004103003400300c101d034000007041c0280014400c41d44542d04c01801d00b1035203045050038560642120020912102d01848002890021501584d020303040c032056400c03800b80058804643c1401040d0004000315041d04000e400001c4203014031ba900d410390b003480d9183d01040340e60f07000b1031152200607030105020800c0d800c00c1c40021174000b8010f20000c20300d1000c42d207500d458101c00e54041041035000244180c4580f81c02e03030f0401d581c140110307040024552081d6845541e40c10245c103040c4100e58981c00b69002d1650f80c3d0120000384042c88000441070000c040603001000401004e5029222204801701c10303690601c40e8504c0703203000b000c055050410400088009400c1488115114420400701c042c0c0c035502c00325800c1024030415031003402c0310011024007281c507501800140c0a221002c031034010035a50034440e42c495441c1c1360f940d403050211004c18900c540130450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 327217023 1250 327215773 327215807
    0x30907090203220f140610030311030405030106060503010e060f15090f041505011206030b16032424050405150910030c020d080402030613110405090f07061d10 70
    0x21040400a0121040c10007601900315000d01800804410780c403070304107c079402c96280d0000c0007880042d006444810700d18850300112170909841d1000700c0c1c00c55585030000c01c003240001c001081010302c8031011641c4a45c00352254402a03030600b0105489200c21030b0510a0f01501140203003a503241d222000308004001401407000e08111000303601c00100314014580003034524040c003600001280140c9044982c0007190003100da0713407208a841910784181515080648a040040d03408418070ba01c0c13442c04002a00715050140b0380180c600000c48090389221003907442003070310007500e40c0020545044601c240c070b0700b0085030280c1e020070415208100702550b002581d18541c10030140d040c0c1c000030454071035400700d40380c0c540004410344200104541c000d5060f4840f5000545036a6200c110110312446041c40101c0c1e4095200018103031201240c4101203540101840c0210304030822214005041034201141d10101c1c1c400f20b15500800c00d51568001e0460410b1119150710a50314045800c0001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 327218273 1250 327217023 327217081
    0x302070621060303050405042a2304080601050a05010f0807031109030709020d0608031c091505130c0617040227010b07060c0302040b07110301180b160203030907090203 74
    0xb038640540150818090503000320700d0700e494484042424108027421090144a8000000c540f01007101d03040d403030000c407082e03424824005252983c100006440507050f144040c200640c1040240201000d80380c1c40700381005100302da801c1400d50441903454005e40c080c680418a54119000c1c08101d02c5100c1d07009030148a00d2400013022590359000d071000d940031520500610b41d0301c00c40f01c1c0d07403800380121188190034800c961400840090340101e00582c484e0302240c821000d18040101141d03021280303100105c00c0c1105071004c1109921004024203111300b808840034281200c90170346654010070090213003009070301e04104910003d160b41d044410340c0c12040925a181c1c11380208030b8018000444001d400c0040085050b8001d0003502c0503241c144c0552424210320781c4805092b14a031554454055581e05840550f401000c1929141c0c240030795040d10a43c02c007210702175900d10340c10120600315001802403056002001c202c0104513814030f800075840c0d45440e1009820f551608501858080708 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 327219523 1250 327218273 327218279
    0x26070501020315040b060f130e01030b160206071407020d171e031302091009020f0a12060b04031b0b07060b090a111c180c0f0b07030207062106 63
    0x54000398800ca01c1501c8014403c071602040c401910b03440c031401036010a007031000c8181ca83d1844098880c0e50200c2000055603030b42c1f0652510503290a0700251054101081040304c0c810154480810744d080300d100401c3e144c502206d004002950020000301e41e640005288001d5585d0a4044910039401082d02c1801c1501c3c600841c8040e030128844e20301e4503400d191952500680c00382a80c5c032562010300c100d10441d030030f1341c00c1202070712008065a5061f40c00d201d000c17030051164409402d41e641d141d684956918040e09000c0e02c5c800340000c840d0342c85424030b030041c0030614008003507408603940000103941c0300c5085a04508822003e0304007000291001c00d01c2c00c1440280c4c0c2000004440540b02c1703e17065220541e8140036545c004a8120707000c0410400d01c074000c1103040d0680c04100304400000f43c0784a0804001c410440043c1c01998003041d080d80c10700940c2e8450307003900001c0c0440c10131185001c0459601a4a5988a01c6410148264455440100c03d0310300102d501e400403020003004040d132 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 327220773 1250 327219523 327219533
    0x108220203160602070623030f04051609050106110109050d05030919110a32030309060706050912030f0a0b0103091a01080d050a090302040c020712050a060b0405132607 74
    0x34251180c2000a0341583c400c0451f896902c051042000301030686501d555034443e04820003c0014101f01d40340d00c619042104845254400b40c0045c002421011505514102c4001d001d030013040b9040c2e186914001c1d551001400005100c200c540c07080c00c082e603c03540c0b5501c4250070036603a404450800e450b01240700c001c128150141c0c60350320700202d40c5c44120720303103d5140100e400c0319450301c1205200c0011007204800403403509407200c22030007000c4a10f0410120b000c0740d829000039200f202c089407100d05000410f003003406031010040754481c5443c00d501d8502d04810105030058070390160981c3d60185000381da442900b1110403e0b40162002840c009910940f64100a003441008400d005818010881c03500c694210f078401d003050380c1c49401203030440c2c08000080c054118100d09512403840002080c0380850364a60580f400343e0b024201642181c10326100752a000c070200b40c411494202040740d11140c240c2c0d481105a082038000022030000c0c850001502021207540090510103d0010301b086 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 327222023 1250 327220773 327220783
    0x904110a15020d031406090a062303010c050708160c090501031a010503010c050403082d0a1b15050a0f0e030d0605150714070b0a03060e060108220203160602 69
    0x25006500700c036083c108200e011401c03640d840d941c0d25001e041c07800c046171561420422442c1c00a01441d800904207554881e44001001d2418551425180c00807182c2203514007071140b0301c50f0301007605086281000555864241e403140030101040d2000400c010001d1145c10a0500040c1c03618880800013541c5a050501869440b11a5111402e000c0e0002169900f0180158000c1003c5503c0301810141141d03580406d50700140d000a41c0e410303d1903441450165130540716400e002d070030760101d5510102000300400400d103582d07032018101b41c54101c0e2000074580c0c003c07140c0b002c1c5a02c0c0c0009441d8452180300d40240610003140c031002810304400040c0c042003c0f0080a145402d041c1c2001500c1d624003d0206100c2220000c0289110501600c00840c7ca4042e6111601c08428103403100c403901e800100304c087e00100c600d0800030f642c40c078080c021305029404a5401c40c0d002d0901e07026501d060300d0040e40c0c80b00d5441070141d002c2c03201c400c1c075000c641381040b0030785c0c8444000f102c01c41c0e543c0d16000025a51 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 327223273 1250 327222023 327222059
    0x70b030a0f0908040b091311030708180a080a030f060311030708010905060403030203370f15050103021809090f01051b0a0c11060a020c03010c021b0904110a 69
    0x21a240c60031080803003110b4400d182ea450780c019840e5061910b000070f0305035203802581c54560080c0c000d5041e00b403a42410301c146c440840c0036256044e180d0402c1d034402801c030000240380b80122403601e030070101c03051170001d001441c00358450252980d61100b81411806800d900301c040c02c041d0f0800300d011040014100d00300b00d016006908690a195032200682d09907400701c00098441c4d081003001c200424800d40085510030480f542c1030f401d071809001c41c50580c3c10142a560303208100700c0020304080c04140a2000c503540f5851042c040e20b03000d445009882000d0b4400c89040c1940016601128004000400030502000b0007214141c9480b0300b00507101c4a14042030070740b951070103001070300d05c191100341520584031008401d8180300804205444601c00d6400a60318004021000e04c20750b61503800502070040f940e8090001200440c0501d802e5030701a0345110b0942d00015000120a0b803011480800c0c001c0885982100d0380726130070090b5504a054074425080003103d180821100040c014007205 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 327224523 1250 327223273 327223291
    0x70602010b0a0605030114060f0a08060306060409150e1606030e19210905061b06090d022802030111030718121202010b031c02071a03010b0f0c070b03 66
    0x2840c0c00c0710080200d0901140110404038406200500c5062110300d17203e07204090150aa45c070341001c0890a00060704000710741d0001a59040030043c0d1070409020480d003100040c2c40504c080d2900e07a44400300601ea85100031003060780e80c072980512a8042180b0513800d0b14105101003095203a61300100900381920076510765128000c074a01140005200403808550040400312002400d00302c1c1c40108140c0300c1401007084028180450107644500c0200b038030f1607000c0c0e04410310000e4440c07058109100202a413206411032030020740965001b286840c042a2212204a100e01c4040002712040d00c0280700a901366103030003c01548200000c2c019405070441d40c4030b640c40204d0005e4080d11140941c024110903416044000c00000d8081006c11008100b500000c10b4020348e84010070b1030a41707401c8002c2e400d07168527040104400c4c1c0504c01d0a01078088200c560901552a8901122511061003035400c0100c0002d0300003024046581680c9000000c2c00c2510341e410740e03501d0b03910000d8200ba42d103050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 327225773 1250 327224523 327224531
    0x100c020c18010b04050d0f0506010e090c0a1a0c0a0c06020d14071e030302090d0606171203010302190b03070305071209020f040b06040e090307290402060a030f0e07060201 75
    0x140d400080080c050484000f08000751030142014113100901d110b40c1c0741190100701c003900107000150180000341c041c0000800c034100302d00d00981e1f0146011003954040c1c0c01421900c1c1c052024624200c15040c441c180c00a9843d9a0542c0803003440c42c280180402624002d1207201c04201d0725404240302641c0d80070740c0e68851410031201d10304580d901c075441c0000d00380c00c00740048030b02003206010204002c601070300f00103041403080804510f00e2640b4041c00c440082d92094240040103107411070109090005004099070079088001603003a00c01030101a02c150b20096618088076000d0343e1440281212071003294880c00c0c28803018001d017200340c6216010840040c10901503850318450520215002020726001607540c4d002c0c44014a003040b08250003210410001c10f0000813066103c1c040c0a001005698034642c90a00c0a01c40d1030201c0454100391010310a0103125540100c4070fa0020303012a40d00ea03403044124001c0e0000e042e11000811400d0410146803084003021900700102c4080b500240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 327227023 1250 327225773 327225799
    0x215071709031612021e0907110f07060c0b090a29060d0210030b040f02070c15080907060807030b040905160902030702070603020c0c04151a041d04020102100c020c 72
    0x4112504600a43c0404595441a20054039046604d0740d941d14104d100300c0d40700c0c0c80c2407012600d1f000b401c54048001c10407402c0810458101040411050b00800380601000340c141480146800c02c81200030f0000750128020441d41320060240107039081e03000350341f1548044c201610040c148608009881c11051501c0040c04d14180f0030404c19a055000b0515a101280140d050340289183c1000c150802c1d540c3c0100302807030300e5038401409210301a80d0684e0b6402c2ca0983d282499072482d0a0000401200c4001d02114090001d0510280c4265040002159a036424224018050b90b10343c5039002e801c002100c010b01201081d01141250244d0200040c81e40b0790104c4c20981c0710580f95000103074000303c02040928402d60203484400c0c0f000c0143c03400c9010002c000b5090710070034039500009902800080008031310001e242164039070000c842d2820107141c01b4103900c0d4010b190713003d594010026000034003113a20901040d400a500c0a50030002d20458400c000d5a501e8174444060240d60721100131 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 327228273 1250 327227023 327227053
    0x120b01090e07031a0709180e100b030d08040317010e0a0e0d08060d080408120921030403200d0b0603160f14060c030f0315040513021507170903 63
    0x2c098a800c201d1400030faa10b00c0c8218000b1003001080700c0200810312502150060700081c0302a4598441180407030840b05000c000ca060003030008001e901685880302a84464a020030454070b094002c0c108044680c1c1c46017070660b19400a02041e01c0c90030401c00001c81c0701e00095020034003c8002000400940c210003030015521640e040c82c003404039006034001070b2146494590482080d120300d60745030030560748440c01464891401c019425046000c10a400365051442d450b4200151b03000b500c0640d42d6528100e15201d1080c0e01019000c88000c0550103001860508a80161400909068000d8481d070422620144094a80c0b5120f4019035440c032841070000c42840061725008517801404600c0c2000c0c801e04120610303076481d003050042c0411708011606001404111a200300c4081c0c1ea46480d2400321482a00035581ca80f0032450b00c010b000c1c0302840c0b86605805954140d0303c151900c00c007001003401c94050050300426100e0709561048509811030701400180405400700c403078200f4080e000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 327229523 1250 327228273 327228283
    0x615051201030206131a0d0b01020d120c1e2102070b01090203070c0f0507060e0621040212030c0309130e1f090b010608040b011a071506120b01090e 65
    0x200080e00c000340c8006102501d400801004d0f441c00c1a0040b00c08280e9401307201003007800c20399420780c0001d4041070b843d80070849802020300e0303d03009101415071900700d1034000d003c2d84551901c44490503511410210710034091441940f21001d1404101c07010f103403003040244110b03460705100340d5612040c161002052030718000d40e000c6e554002c2818a2582c20911000000d4000a0a01040000741235903000420050920380300301d00d0099000c2c0c0f12483c1004000750140b20315614150080108010142c40401902c4010705540e140c07004040c5583c81e58000181078680b90140071000307000000790b020740315000000600600d6802c2d03510040c40950404c036041120f5007404070308101c0d04001c0e44203100400c01d000384002003086da0310000d49242a034407900c0500401343c000e032000c900ca080600c020300c00507031106401882c0c1007160481004600b040ca01a90103444c100922608401901450ba07100300e0300560007400440d4199120442941001c030702c3c0e01c0b800e1042170003042c5880b580c3d203180040424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 327230773 1250 327229523 327229537
    0x7060e0d0504230a03050a0611070f0201030b1f03061a161e0b0406060302091003030e1c150506120d08060904021f030b03010b0117010603020f0c01050901061505 71
    0x710079003072615055070718820848105000d8240042d240c030300c0302c0e0359540e2085039000d50700400040c0401042c071714060080f40d81034003d485001500b407000c20001001e030b04502107503560a10340440c4a41c5e0f01c5000c2007c40340390345850310540c7c0c4a440d01c000580d034558010f50855940502c00e4080686404214001d403048031365400e00294130624000c007080201d0114103008580d0b1007000a00040c51f01d0380c0c0501d101c04c0d42e049401035100e590800075813900410f4603421001071760010540514503078004c0c1c842035130002c2e468000e034106120100404101c0810b8403000d0380040040c4174042d103c4107490002c25040301d10500c81e8460b980074460046002842511104042d00d449840c0d88031001004003d04008104980c0400c03218101d5190b22580100499031980545021403d038010074109801d4810031525541006660386000c41101c010030304a078110780380c600b030041c1e4940c00900340d4000c0d4850319140e8a0158244002d1040c07203d8150f000c081200d0b2105080c12020306400c004403030b180302d00c01c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 327232023 1250 327230773 327230777
    0x41a1f1404050a0611030d02070b040303050606180f010c0807050a1703090d180b120402090606070206070209060402040e0f0a05070503071e031503080909010e190b0f06040b07060e0d 80
    0xc01401910f001e05c1c984c2040104400469042814094050007030341c1c802502280c00c180d00205020070142c06000311a04120101d41d99418072208800307030282e08403100c10f040e216106103010458241d000f81a541101500401c2c100c0d550803c604000341c0d18810766104680060009203000242c2071203609903401000d10380e000d0221304205002c2218a0500c40000c03540101d11110002469920200103024045a0b04180c0c000ca1030980104004002c00a100c0380c040c980c00c200071401a071301c200840f074417964119000ea40c641c0794900810028040c0d9040308810501c03460510a43c10102c0c10800d102d00d00b0710300e0504c507603920700380115070a002c1618980003140c50054950200c060205480001035103070314002802c0416080d03a80c00b020041d074003d546146001541c0e42c1603040c03070b04c542400b42c580c51007454040d0419200720144007030340142d0300c02c41c20741d1184006c4603646c031511090721450008000e1070700da64540079220403507402544111682e51401c0404103a00d24013140c001341404c21a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 327233273 1250 327232023 327232039
    0xb0105030f060f040f0c030f0c1b06090c0806150103090b0c03060111031614010902010e190504021902010e010905030f0c0309030109050102040f0605030c09041a1f140405 75
    0x4401c440c45014040d00240d030103004110740325181d49961042c030502c40026131020609003007182c80030301107d0b401014188194148141d1510b001d401241001d04ca108400c034015074051181080c034010440404010807100b0400000200030b00f0014815000d80c030b43d1b04416040e04070400042d401c83c1c0030842e0082041143e07400050040480d64041c1d50f01080c103040c9009002070780d617841420b550200034080c2c0c000b554800100180141490340e400c440e14032600820104809400191a0940c07107600706105419010800302c032005140c92940061202070001d41d05c52018962080c001c03902180c1b030303000561802900c0b1040c2101409400b0489806c0303005146400c1074000c82c0c071201e601000c02c0e00340710f220800504955480c00d21840c881140140001600c907810900e04207152400c0d64400c41c00c2140c10b0050040c003100d070f4400c0350141041241c0014110a0003020394014101003001c0301d0780106820219891250b55502254510150303507101c52100040f8440e0743e145005074095140c0142d15 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 327234523 1250 327233273 327233281
    0x606010207140f10120504141002030c0d151e0501080f130b0c070c080c280b13031203090606080a2a0f0303030c12060602031204063c0b010503 63
    0x400c44c6800d2003145a803601103110900b0f1100381090741c00948044501d256010900310760000140540c1d40c0d800b2114406610354106003000880c2401a071321100740d12580c81c0800341800301c030303071030040c00900100102154ac01c0454032542c0703c208c1d0740c0c4200340c00f240404001415242c80044101c0c441c1c1c840c14001910341d1100d4441c040340c80300040c40750700300000c10424400840c6240c25540004c0c4070b07c400400388005003105001407079400d41a250300c08001400d006d0012258050500299484404c0454503405465410072260702280e10140c041c040300320b440e000247d4550032000d400c90050500713001941e590000f0039621800c440d4082c218040786400300c01d918450030911840d08402d00d0100300619207a000641c16143c4030350080307000c20742d9182c58425042c1c101c442c409c05110b054108103d900e1a00c040a0744920804444a88180540c4005001c0200940c45101f4224045100d42000c0081800344d4501000020f85405854030806601002c0030701e0b8010400c3e90700d0181d5410742143c407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 327235773 1250 327234523 327234529
    0x901020a0f03030e100204091505030d0809070e18010c0e030a08280f021606050f0a030e03040914011e0b070809090a0504020f191e050307080606010207140f 69
    0x120381c4800314101502c1c2c0e901003009400402001d48105040400182c4d65481e1007001e00c00c44221031340c466034149080702d00700202e41d400303e10f02c9007030020717410002d07101d69803420302506120160f0002c00505c1207410601009034030400e80402c1d00c400e2103008000c5070070459800d480300400817109980c582d0000e444070000501d41000707059a09451100e420f2105a00303200c17140d52130b00c10403003d0009400304040314035155040180d11301c0b0300154880c02d001981001d078000c0c1117200307400d0302140303440b0f0000300c245c00b01d8444c2c0d0000240c0b8900b04143c0c0d0300c0355142c0700540e0181c0402c0d94424031201c09800041000050800c2c030b0300e600000d00b81c0b1403500f10314004190308a40c00098050b50000014890001c08e52540c40045100e01d0f0304010004e001c1c942441042140400310f9081401213a4801c414079104001488090a4402c90003000780030210500100ca801c546540025426005001c800500c24000040250103008260241c1300070f15110381380c01c00d6070f801400c60765500240e45103042402d0b007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 327237023 1250 327235773 327235793
    0xc0306040c02010b0909033a1a04050106020624030303040f0f0f0303050a0501060302161b0b040b0403061b020c1c140f010b031207060507180b0a0e01050901020a 71
    0x100c0d14000440c984d903102001846a0004a495100a4000142c00d03840140140761040c00008003131907405000da00c03103000700130307041001b0030780c2d112943e072030a124100541014500e221740400610078070280d0b8640c00d00a40300e90042d110321001840c50021801c2c044030b66000d1071030904001d40194255600c0ea1183d0703001107070300b041c1541c0c610a40d001c19008110b8408401013070078000e4401140b1814242c0f403900845005a0004041501c10301440d0080d54a0382041040140c0000c0c075050000c030508008400382080383e10041c0f031041d000400003084813080002c3c0048900a0798200400c95641c00c2d0342040801c00107040005030860400700c450387c601801d02c1869041100300000041d4656540c0362007419a203081000a03921000710000310310000d000f4446280800d4001d0300c80c419001180c03500034082c100740200102c0e03c48000426551298140c0c4160190300b4134401d01b401c1e80c071941ca150b260300c0b00c0c2d00341c00005c00310403207000d0b10b50103082102c15888040e4000e08800c200d03501c0d207000c16 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 327238273 1250 327237023 327237041
    0xc031b06040b0406110d050c100f0b0414190b060a0507030210060306090501290603150d03090317070209040308090703020a080d03150f0501120905160314060c030604 73
    0x20590502011450a141c50050405098962501013890142145d56454005070389408000c02204021440c425400459284403044001c60007294201d640c00d45030010388124207180750040d00d0a01000904104951703000e0007000c1020403404900d0341050080151a9801c1a05400072800c200c040b68207131041004100060103441030340c0700200e803030350300000f5a4419803080d03a0301c9841300008000d114080c032844000c4010400d00850024200d081340c002040301c08000da11070344020000404585852000c40009000202501d44030541d601d00642800c2c054002946c0c00e012041d000c050321891101182d00c0b03150008c0c5814510341d00d0780d8040f94031900050001c8810b009900002006840d401014006014100094090000f40920085c22135040722101245100c224200304022901d001800c01615000e113084203002120608480103813803500002001c52190f4051141680c210b244000150f0344070b2a80c2c14a20020440351a5440c1815103840d019250108003280300d6103040d80c031017004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 327239523 1250 327238273 327238279
    0xf02092107120f15050609071b0b13050d030507020307060903020c1002030c010e06011505071a0c0706060e0709060e0a080318011407030f1d09070e120c031b 69
    0x80c458540810160b981002d91046503030f1900d03410044108500315040c2d02410307400307030380c20022850014000307642000090040b20600148549503d140300e0302c069841c81c566008400307c540da04022007a403c540d010204283d800d0702491901c032070300764444e0141c1c0c0d00400f2a80e000b5401d1446c1c81c0c82d840c0081401000c02c41c00c0d0f104420300303940e403600c519a1400c1808403030307009143c40d0b074908218603094501c01404d140711a0440001489a00741d444d010380845003080c030b44283c5a081c240b8021508002e10150f90400090079401c11203c0d2945000400364a071003080140710150f035408000c1c10044040d980000072a1031880144141072284442c0124000300074003802d440c3e07030f44402c080d04560145200b04081650034449000c1d950308089003044200c404d0030041c1c9000000e880040400003a80180004c01c14120b8400503c3c036801450100071040040041005007020400a4138990881e404ca600660840d824a5800c107004108a0344100011f0042d041c42c030b14580e04031081900c2c0217110b50b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 327240773 1250 327239523 327239533
    0xc0c01030b060c010c180f06050712030b060c010603050d050f09240a0908060916060e04270303110c19021c0f1103060c16050a21030f020921 62
    0x2203c0da000340294417650b080d40d26003040c1c202c5240402604044203422011045183c26400c0048039403100884091700d03002502010308005852080300075004081400b907020700c3c0420101507156042d440002102d2003a01115450a0300c114151542d000743d00c0c03640303800700c0103012140e50388c28050741d041800140f011001c110b4510702c0311a40140e0700318115250018030300f440b0900600008110564000c170340800241100a040d00e24440203011a0080070100110b13036828074040d45480d04090180952a4070000400c0c0310000304861703400b1038070b40c1036000a0420710301c00c0f1441d010004555688025001030004100b001c1e10410030f446c0180700898111048441c0c0c040d00c00707400307088503140c1d0348120030454200e80207091040031a07041c02151303071094205000b402104443c1004648842c6201c027982404420310713007485400c0c880b0443c800f42580100c0540f8644142c0d10154900c549002c40e03c0800c120724001d00a1412802032514840d04400341c01d1102005003244183c072680102a0002c0350 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 327242023 1250 327240773 327240787
    0x80c0a0311040f081b0f1219140105100f060302070203190b0702060108030f0301060c15091203110408030d110c010e010506040c050702030d141b0307060608030c0c01030b06 76
    0x40729071103a8000000444040c8003801aa00705101500310514a4100c0311920b210401c0002c22a0742002d0425125a0581d0714019840b0420301403054080c004001e5004100030b1410008070125829403107507055403818000980b8940c02c010794500796080da003011015242042c405074001e50002106036410f11501c02000b078481c41c04890540391f148109034040150804000203440c044040c0c21464040d0018041e0070200c03181641644e04403041c80c07030914070444030342c1055441c030300d4084070f034100c12070405c1003900501694509104140040b95400c01c08024200d412003030fa40601e010b03c4000d81c0082044817422a0b03160000034054044880107403038889940141400c503074206c0070714505651070743c00304125881c00703200703580c540b00d4103040c1340d0f14120b001ea00098803a1002030304e8200340301121200303206801044081c1c88178001424041440c00920900316030b52500030100072510036041c410040391180c404816264421460343c010420390200a0055000d02641c3c0d100390342101081c4850 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 327243273 1250 327242023 327242051
    0x6060309031e2d0e030a080306060f07021806091501020703060c2a0501050c040b031602030c010c20010e0d122a0e060f040902030c040f030c0e07030507080c0a03 71
    0x401c4007015a0524440c1400107088040e0013407080300115442600704501500200750700908480e800301c8100d422641d520410741404160740135907440a500181d011108500c4030000c00790880c043d103000c56035880660340c0d2842c0155119821104980103801020b81000010141e400c100c1250380756041440d000c181c810b240943c200f458090040307485200d4440c9900f0b000c42841440c0d00810f00303000300c1d8646030074080c94005910014107022a03030380303503150308074946071003403007650040c40a1000901a020016100501c8001c500b40e1010031030b40040100e850002d0140f03c0c140c440e11100c405041004c071000d50a4410101110001000390788071004c00d01c01010f03000b130b6820b018000c1d080c0340000004960004001c42c80041e600b83c000c000802003929243e91401c185c070100d580c9544056507039581d81c01600001c6c0100e034040d0250044040300403080081540d203160070b40d03e04010101266651460440070340ba4150707089004207025802268212004000800c3c0c0b00c8110706011841041a07488 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 327244523 1250 327243273 327243317
    0x80307050d06150507030e210106080709090203151306020301030c080c10020c0f0d0602070803011d0106091403010915020c01060608190b130f0b0406060309031e 71
    0x802000035000150303607400148a100d002c01800094980200790780294401422038401d0003006818080c01d440c0e80f08141c0d590004d007000b48890200041300d050580809240a0009801464910b020b500303000b05900d0f016100b4024542d80050091180208824150000c06030203001325007000000001d01000c20481d000035802184a101d030402d05900c0c01c42c082d42400c840b95245489a80c4003020011560b50018100c40203050413540005000380100009140c20459070b4001e080c0703800403d082040c018580007840c12036150000030000750143c01200e0708009800d00075000800c090420501c4401d00100703502c6600c1101400000d400402605c410311086400320308107401030b0300000d03072007a100004c5c012240181854144071159003880715001040682d1124110800d81d03403021080566a03810000180050072000104486a0031140082c0500001000340e03010742e062060000d8400c1c400d00c030f140c2045405503079259110500322042d04c601c40140c0d074010100b003030b024081486680c82d288 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 327245773 1250 327244523 327244531
    0x9010e13051903030b0d021e03190f0b0105010503011206050406020903010912020c2b06020f070305040f0509040b040201080403020c030d020304180204120f0507180911041b08060301090803 83
    0xa445502c001c15490000e080e68040c1c0070b800d0050341049001030040c1c0b940380b901c4444030b034104050303c40b41c0e01e5040070030718069141562039160f205401c0200140304c0300001e000f40d000c1c0103880c01079140c1c2e00c40700155414031082c807070303508a8401c040202000c00d9140d8400c90b0080d101c1e4002602e01924480041d013500c51515040e5011008800c55581c165010803200000520564400c1200c0548054142c40c0c0f00c2c014040c9548d0070b0030184d44070308100955048a159181c000781040c2c550034181402465500180180303940d48981d2030000c03603c0d01e40313200f10b00d1013075900c0841410203590350340c01110254000f401c11800c0d4803d141c030760551aa814080b07242604080e50040d91160300d00301b5284500707050103d904802c0c0380704000c00e0200c0d05058528180c601d800541c034a041d480e082c645140381c9207190388a9030920403840d1031500d0554582e080381602d107010740c0341c10340c0c60042d01c1c0c20030040310011081e06682d0316001700c28401042c01041d2055100800600014002c55581c490342c15541c0111 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 327247023 1250 327245773 327245803
    0x1701020a020d0e0a05010c29090606180c13030803090a02011b11010521070302280f0c020a081203061e13090615032001050909010e1305 60
    0x32840508040c1e04200a5003042c032075151415001e00c0220100310191070b68024541088070141c20314040c040795001041071120010200e004a032020b404404000c0d8064031a03114601807140800c00b5454981e2130007408501403e070071042600c440c900c103c02540712000440118a8040c000004140b100303010307501c00d200e000042c1080108a10005242c1e411800c00031160480038140304002c0340488990030400d034401e08140b941e42080c03803040f00c51260b00200140a40000208100309203a142c1c0240188400703130009803084460011203000b80800b00d10490001030701d040c181c2083c4600c60468049060f0020385601e200d03540303400384241040380c117020503103c4c800000188905801c01a450700c00071011480c1200b00941c2c0080010101d1a42c4605143c103c3d8840a40b14144a1240d021aa03c2420015240301e05542c92400c42e20b0781c0a503020000400c80801e14455140d4012401c44042d6140181405096030a20841c241300d100050202d840200d202612100041c0040110014000c900c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 327248273 1250 327247023 327247027
    0x70b070c0b0919030b0a1503051b36060d052d010204090213150801031106041d090d03020f04031211060411031b1c170f0c010c0e031c030204170102 65
    0x1210b10800d5540300460087e582e12180700820100d0300106951205c0d0019641050041c00100c2c000380da59000f420300d051441c0d185154054a82103001d050140e00510001e01030300c20360741d00d01000680f405540c000b50441d04600900344141c4c5250b03241c05600f06c04803c42c50500f91152007100d0880e006a00f017510f120768000350b900004911100c04034021301d00074014a00601c0712107401010ba11042c400202140d040041081e8540d9400042da0050418020b41401407603940030010001c8500340d8018045004a4140c1d01c0c0c0da40c400d008444929131001c444a140500d150349070811035400c2141c40c800c2008001e581c00d900881800100d00643c002c004080100555100309402e080d04140000c40f00b80c404240c50810741c84040c2d00801d210684c05003400007000c542800c0c00c114815500102d040400040c00042c504554001351900740c0b0307094000c00031400910b0094a10205087e00317580e041d4860301500c2448030703001e2040341801d41640790160a040c0d886910485030500c216882c80d007a500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 327249523 1250 327248273 327248281
    0x6030e0c0301110d05100b0703020d0e0103051608091213180213170106080609030a030522080d1514040e0105071e020c12060405070b070c0b0919030b 66
    0x104000000280ca42100200031002c41105541e22a01c55401500c40c401d89640015038801260309030385001b02001e0390301e00c0e83d40c16586002512a08440902000f09920410105031b81d4440d01c9501e04c05c20610300024940c103600c07401a1004400104086194441c00c05c4c9862099141c1000c1e02d050707051480c250102c241012109040b4213103000d07000800604c14403100c440b0000303001405080b211800314100300e103880070310100d0240401c0d8200c18280e201d240144080800000000c0c485003c0558041000340c840161074000c04550788071280c108071074180324001060041004041d002400e040024140000e02c2c41c0c0f902080056000346130480711035246103036a003014007420307407002c040d00003c100d50b01d0320402c040d100f95000076082d84450000c5d1038a09071103008210240c14850300421481036520840900755076200202d500f26003d026841d00015450003080903280442d50081404442505007244d902e115000840c20561150800c0c8a001030480388962500c085c6001d1061240345141c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 327250773 1250 327249523 327249551
    0xc02030613030206012c09071809050601090e070e010e0609070206160f0c02030102070c0f0b0403031409150c0a03140901090e06040605090c2d070308040213060603 72
    0x40000c240c04200e00300e4000040c00250f02251850560394040c0d80300d801500429803400b200001c05010600c2c10042600740038002200061100485009100c442500d907406141c02d8183e50034810018401c2d0f210304014003d0207880d4201040d1101d62804075100070340e0321005005980c0307003a40300e050328a030110309020a90030081a043c1c2c0c011141c1c0002d0000d420069800c201c40301035420b0400401c80100148002c080c403440600c501140c00400079905c46203541420300c100d031914032600c0c540e00003884001031400b4203541542c0459805860b486071235800d112400b030190303000101c6c50b580801d59519a02070130300c154001d0320900c1d0f202c4009022407034461030302816910710342c2c00f160300605051041800907070b8000b0803c420f84904008020894588502040c083c0c4080d0f00300c1031740b011100301040b030101d2000001c0d121003040b16034030300360121004068117402c2c4d012240000000700108100008a8040d13500103411a1010b022400d44082041440040385e880742c01400000380c8905c4101e0340c0d05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 327252023 1250 327250773 327250783
    0x50d2105010602060403202a030d050313060204030f0f0606061e050d140903071101090501090e1816050f09060d2013051618060c0609080a0c0203 64
    0x100028000304990350414401940c2c0b40c0b0010701c002c0800c00d200c1d01d0007000d8142d4520160050250500b100c480c0901c12562011128410b46a21028404001411021f260014403502c002d0100e865807451611019040d125811490000b5580141c0070440007000510b44a0b403107000f41d0089403cae80080c401c0d8903051099070305540c000001c00035075031149442c03c08840e8150740b850440c1c1c10059a28200581100301425082c680244842d02110411216220110003025000c0c81130f40501b1910000e0001911190458040d0b903000940c0b00205000d910b540742d40d401d802105a080c102441342c0c21741c20740d034a00034880320705001011705042e0800803401c290386d881003400304c00c403004001880d10301c000c19840310b1140d0010f00444001140c4038201400014003078120725001e00105e40008803110440d018100960b420415200e20608100e000ca100c3e440051604a0800490100a00d06401103408408405003900c14903541e0f0700030341c001003002004200756200ca8482c50106042c80c01054245 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 327253273 1250 327252023 327252077
    0x50307031205090604050304090b040b09150a090c0507060f1514030f0102090303031302010c080327012a050d1503050606010c0b010e070c0f0b06030c0303040609050f0d050d 76
    0x542d2080c4e0070300c40022008010307a4269241c500c4001105e003640c00000c0d0140c040e030341c90180c0101d050b1003030208048010311010b10410094448a295079a80d000010840e950a00c103500010004c0c031040d000204541c21020070480d4060300821460711030300c0c22022041c099070160603c00f00e40b41b003a450b0707400c0c140000c12141311280e000b141041c48500100380c4901c0014401d050408030070701a0411603004004144e08941c01002c0907850f0320782950405800e03007900003e080740c40c560768403203012a074050041c150076039400f001d01c4416a081c015182a417100c200003a0b020b221003440a803007414500d218071085030907200d0025035180d1460034901c2c14210040c00f03082c1081201c0b19408080b4156a079154111413200c2201e80b00d540d1032040071078481c88040781c01030802c01d140b1104400d0000400100e80251411000e0714111455181090350303d2181e40b140c00046043c04204000d075280058881a044402403c40a0480b0180d5959420088948942d0f400300d0450101c072190491408080904 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 327254523 1250 327253273 327253291
    0x12020a03051b04051e240d0605120307150f0c020a021309080301150201111b010507050406021e07090e0a06110403020603011206090b09011406030109030822050307031205 75
    0xb401e4240380105259039000d60f00030404026410200440da02c406c0880ba000b0004600307510007101c003121012034241e00c118050103810303040000100e1107240071401c4c29080b00c0d1110003185018003580e41c5040d400840e036400b1001c541d031003050100e80c0c000c40c02480d4600c06150b0140100d0307a034503c10400307003c3ca4284892601413034112400006014041141c0c103680c001411030080e03180303620f0201d001d85801d0500450b07011021070588610f4100300074142d050046040240002e54461078101d4160141e84a80d000691006110400c001009112040000b00003810348104945580801041d00d641c07807400300d1180c1c41f12850109110a520514440e61849401903180c940b96070000703041c50106002e075501d11074180c2da4150800c62281d200a01c130941c4034581030528900701202030b0003060204003102e0300702c110000151084c81c0622400a00e668542c580503c5501c4810011190003040c0890240003990500200089001000a040c0d041d200341d9882910402010f44201a03a4000d001155 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 327255773 1250 327254523 327254527
    0x3070803040905090615211605030f12090d0f020324070e010909020904180809030d020a2001110f0d1d0919061802090301050c0301030c1512020a03051b 67
    0x19414036200300701c0e002c0071401c031085402100104040500001850f04000d41032013030780081d0018010b410740b65000c41c0c2045081d5044548520405a19a05990003070103330b0302420071252406150425080440501820141700c20002c5540400d18201042151035080903000921140d2410019050b550001944ca02240803681200c0042c08041e058011071101540100d000300260f125588403030900492801a0200c0c554242026452a400a031100d4000e0048034400048940000390740c440d06035011500da01001080d942c10100c2a1181046a04012201e40056007644041000b210030600e80030141001c41c90201004e00702e6090f8412020b0a034001641181c51551440e8006505c15008007441400c01034207000b07d00103040c42d0308040e04100041c1c41682501c40158094411030005400804c034030349503140310040c0c030301007448020f28042401c1d0f405d00450103440208a917881041c203050b60322040d030301c1e80c6409a801c203a00560000341d9802c108400007c40807515000700c005200e4842c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 327257023 1250 327255773 327255781
    0x605090d020a02010c2109090609060b1602040b1002010c08060907021b04060f0303030b0a0611060c0901020c06041e0608100e0603030904050f07030e0303070801030b15030708030409050906 83
    0xa5281c2c0d104101c080e05100401c04007609101141d80494204007850304941d0340151803500181103942680501e51507181341c030502291081d100d204441c01e03558009546c0c0d0a2445000718000014070040c030407600b264a40000081c1030f00c80045600b02811107800115540c110044000d14822004001c01d100e007610000b40089150003040c00b2a80380320ba21780303110b4500307000f602143c050301603036104400c032409540d0300000f419455031007641303031400c22101c0c006081c0d907451044411414813035440760580c20520105002416041c01040c81d40811f005030350b5410701c044006a80c0d030304550700581d080741c080360b00740c501c00c004c05030280b028100508000e000350420100565000000d4081c203000304100c0c10101d00150b60403c20344101130740040080c402440c1424503800700c8201a200500424106140d004288030702209a074413858081d80e47d00d40310381c650b480f40b0a800703030090f001d104824255501d950b0a03460034041d07031018000240064ae035462410000c041200e80041c14200a50401000c0c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 327258273 1250 327257023 327257027
    0xb040b070b0c0a0c0813080d02010609050c031e1009020403060b03060601020a030504120201110d111b06030c07030c060614010e0a031e170c07140906030a03031109060c03070605090d 80
    0x1c4c200c2030b400108450b02e070403405103100d0b1100210741000764035105030b403403055030140d05400000940304656000e012984441d0401d1406000a8a0145844444141411144c100c88080c940c1c0103007000b88901140d55103088250880c1c3c0700c2d800541d04d05407544000c40c0982020805c05400240c28401003900d00780300c0c0c82c000c206003c1c1c0d0158500c9810329440d00025a84a6021801290201d0068844a000000e00030b8007041185e0b051101c0b90048018451940b0f60440001000101c0035200d28610764851400c4081c542c000070048050080783c1e440d11000c56444c1c850300d806001e2070524038031304c129454005071289020425551082d65440000c1c000180c0e0302c9031060040845040302070180c582454207691800e0707079211000c030b041d8012440003a07456000410908558100f415030705442c4010341881540201100e109405512041380340d40020710a601ca0103240d04444070b03c50500391214002030480c1c0c0301e20000310043d400441d0303101c1408801d10030281c1041e824401851300d20021100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 327259523 1250 327258273 327258287
    0x130315060b0a210b0303120106080c1903020a03020d0c08010305010f0204030c030b0705090d120e0105030411091b160c0506090306070f0909050c0a1706010e060706060b040b070b0c0a 80
    0x5003d0a0049186030140030705250382092001c10030083c160ba46078684a0041c4229800c03d10034031001400c404049454010700d84200c48c2081c0c3d0815080a1402241d5401e4000e544010304500130190f003004064822101442002c031900710075540c1100951641c2846403c0d00c840c0031001e100e440c8100000c1000500080451040703a6200320000c42964800d40706a07024020b9002c0c443d005090001c0c0d05040240803401420741c0c038100d44400010340034400044445010494000f8140031080d1680010b91410000c0c17a940310240c6500c03010f400c403001568450301e0301705c99408408040d032440107071b003040050728140740540020303124241480d140d800040d90b104000b920100a02120700360211029200e15000d40251660078420301060401d40c1902c0c16a52040d50b07440000313000d220328060b03250018001c89015000581d542c5500d40c0d018010400e071584040c1e07045034019901e020010304002c0d40c10103000240340c0c070701d111ba8075602c035420f02d80c0311000002c29480051108004882c0c904ea00942 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 327260773 1250 327259523 327259547
    0x18060603100906090605011d0906062809020c15131101050304030306080613020405070e0a0611010e0f0d0f0509090c070f05100509011d07060c0305130315060b0a 71
    0x2004140c01d0700c40d050143c010181c890b0041c1803242842c001182c078204080d03080109002e01483c0c800039940b4100c00c60b460703200541d111a4442030000c51078804a210b90400360340c401111a10f10646a69041f600040703078004000100c150300203040b051604980c14040a40c009110a900c060909040d5590045421100f070803906000020010609041c801d52040f8060450282210b40d5402d00c00c54890342ca1700c4108007284501d04250000da580780c8501d010321814003000c1d012201507400d0481c180d80c2035480b00c0e0600c080d50760f0750024010340340040003050006100d2078082c11088144210007001003510020000a02100f04642c01494a039044900d83c04074556560540321386140c5046d922401c074884000e4014881c034680d50710100c90983c0f10030b010381e84000080115420840394024500b80c00f81c0101d22a030001c5c4002c0104c140914405480d2600c80d19000b440c0c03070702c442d0b0780c00030010568005484080002b4040400b0394194443c41d0042c01e10083c02504104220b130000b030a2890f124 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 327262023 1250 327260773 327260803
    0x20712030503072606130b0f04020c030705060f09070608040309120c0305030307031401050d080f0f090d110117060609040906180305030406061a030a0c2618060603 72
    0x400a500184544c42d0044103107625407640755a4182c502030403103120810b0b2600b030720070407945100c0d030b444030702c00d118410103c1c00150003403818036a04400c2000a4008081c01111030004119413000100140800b603c00c52510a021110b4140341110b24a13201e131a030440da06219000082c440401e401c900b4180441c0c61600303c11460003468a88043c184160f5403008216100100034419059003680000d4440a41c41c540c401d850b0781e03104100107203054103802c050010f07075041141c2c01e0038545800044c890b103031034540c1003840c044807030340460f004c2000783c0400d8400500102035602d4669001080308042d100003018440c031411b05400041107449000f041903c45d035901e541034001c1103a40d030060341d0030312020442000c0e1490107040150482e801200c04540c0c003850100301041500740030701c02181e0100100200c5096540d501030300310090419180100c00d10284002d200c0c862075030550001010b0415416540445c00e107040d403100f2580071006500700d140c01040070401151400210b1580c054004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 327263273 1250 327262023 327262027
    0xc050d0506060f0307050a1d01090306050c16050d030e070302150a030608030a09090b09040f14030d06120201110a0201022509020f0a122306040e060708070f0207120305 74
    0x6000050240c4600c02c60040c02d0f41021041000442e0014003402241416448803848a90007000c1d0780c0c1d058001c0b804136804034150820074004242d5a5000c240c0c01011348200ca46002c8003007020310b20359400040c00b240c103a407103101c000c0303080b41d414042c403401d0f20f034501d005011050440c0c0c002000499844182000c01d030b0013080e00608030b48a42c0168008003580c0b002c0c1e9035941482d4500a0000c074081c0214815035007000070002c000d04221000c01e20440c1c122592030320f007407415a5038035203030901c03040b803164144030500150a200c24a481a84c00034500965540c4020310302e40300140c500302c04483c05ca1400d41200309090701507600824501001c5450001c80500034403d4401500884113640062640b0352000c2019802d444101c0300400410350f0036111003ca0303909120591003641d0301c0c1800440c0f400d406010220b030401c040041e290308510300074400b0074064003220125117060000c40d83c032000a0540024003801070b40080c070760341c20040700b0701c0980482414038580303041603814420018208000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 327264523 1250 327263273 327263281
    0xe150307020c0406080c01410c010f06090506040209010f031e1a01171b0a0908010504030c0c060525030c080a0c110f100e01020c0409150506040c050d05 67
    0x700784800d102035000208100007407a11a041e1503520f500307490300980800c52108052414800c45a50600384c2e0040014040d21642400b201c440140d8000c0600d56500310103200d040c2240d24203002e41d0115986401b0000744951400e01084c0a507980034107247c0c0528810002d8204e144d0340056551603980481c180411107011144031085118039080019240038545402c0395501001c140f040540c0c030400b66100480e980c00703043e500d14070704020b807a80c002d01c2c100070040090b03599009020381240c0c402414924a06943c5081560075075604031421400505012412020803640c1807010002d01303000d25003203003012400440014000019a00e1980040d90719801e541010f00c41c0b1031a6a259520140a9464010340480074120702e02c00001110254400102803142e8107002071740300c400b0700b002803000810000d503a0701030b1410b480e5040043c1c11405640c0308103101d034440d40a802c2219124010120300c2007203131a1303a41c086482c050101d0703100f0b50410380d6031811994464182c681c201c5000a000a503611 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 327265773 1250 327264523 327264527
    0x6050d0507121109030f06061008040302010f0606030b180105031f0603020d032a12120b28050306040305030f101809140601030b0117010e0f06160e150307 68
    0x1e1940242c8280a0421400707010402500c8054050658107604403400701c034144c044140c5840c0300321917498016100d1000c0e41c544030300c140e41c56500a4020300000403500c1c010f0740c40c007040d90305a170000c1010903146c82c400552402d1403807a0280d80c0c03a04441f01449941000002034540324407142c01140000c0002d10048800450740c488401103034024100d0010007100e10f00545410000f0301c0d591807080800c1c0d080201000c0044000d03444540c070616925211000c50750546168018010200344190703110629055030300d6000f00803c80380c030f080c00d1641850a03080031000089a0540000d4000d822030f84c14000083d4100047e2600106618030001443c0e4076000074040741001580000c10010091550210070491680000c02e00d81c0110400c0c3ea049090416040e6146000c1c44010460b00040c0300411015203c2411441450303003071400421840440c07801d80d850070b041c040c0312a11036042034050019440710040030702643e070703820704040d81c0302d8866400040c08501c9402e20650b40ca60000000780403d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 327267023 1250 327265773 327265787
    0x80f011a041a06071b0e07020c2206060509120304121e120302120603010203040f1407170601150c030c060b06070605040507051c0b0417070c0305060a06060906050d0507 74
    0xc083e201035142c1c1c540d41000b81c0310840020400b10042d050520205001c1c81e14004a07109030020b400070043d255080d400e001c1484e00e81d505035092007816403044188941c8a002d83c100401a9640c0e058595000804008001100e01c441c58a9641704100400c07508407011a941903090b004200b40b004595610300d00c2c0003503030f2140d8008024181c0441c050006541541c054003e0a202c2e0520321103603540c0e0300c2030500301d2200356809060302c044280090000783c081c010328112108560203a5281d155078140c60b00c3c80c0725004180300d02d25001080180103000c001480c0c841c0e601d45070b02c0e0a410b81c100320f03200500000113981d0040e0129450f0b4111038095200c060445014136071000c0200104e03e064100780340c0340c018a0080721b2195190340300401000d00039940e0819401e4000e10b42d52450389640d80c4a040f860801c4034030340c41501d010310031000415202c1000200031400380c000340c00b082c60807004910884200d600158144004c564051200d00e9001d800d07211102e13089400082c440c0c070748003420340b140b07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 327268273 1250 327267023 327267071
    0x140f0a061508010f0b0c100e1e0a0b0a110f0d06170307110303250203071a030403020c150301030303020d06091127060304030c140610080f011a04 64
    0x5804042a15014250311140d098126000852840321341a00c0380b0103611544544100410f40d0f071710011000a80070a10b03400b42028926030011142c0102c405603c1c080c1c1c0307400308900000a40c000e00c0c0224140402c044c00b243c0d001041102c1040740016032a00c0c20703010f01901100c0075808002080c0074201c5161988000042c144c4400c1d900800c121060082e40c2e2a808200b08030f90380403045103404040d007000007d0350f40e9680d0511800b03c1440074003002020580c291070007030ba49071050711000690345440003045111160074041c11a82da181900b0064501408009854040e507204404110348104c00070560b815a68503150250741e4402c0c1103082c4001d080d160b00000041842e00c5030754409290400000c02d80f80d88880c6451604400424003100c401e280c01d000c0c90f400c4a000c00006000030710481c04040298402c01206412800d28111949005070071291139084440c000c03020f010324442080341450001c1040001d009407801802407e4518600d01001400359403120210100013055045c0c3e4052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 327269523 1250 327268273 327268289
    0x10061107031a0610031a04020903150406090209100e040605090a02190f050103020403110909070f03080327070311010c0803190615020606190302190303030f140f0a06 73
    0x1488944588152802c0303050b00e00c0780c407510b9554081d110300b0340a8080c552501608000003000300d0b02c0745007440040d600c00060140c0c98003c1c2c640c282c00038244040f07038034003d0380164400500c0c00211304c1030001c0c0883c050940f00c0840fa030800c042007001800c02d62542d115070b200b4404a078035100c0041d902e180003200352000790f001c10401d000e50079003941180c25a00300d8090700e6507115580e40d44c4d00103400706d100d43e00024285400c0118821784c80c0c01c0160085401603422000c40d085c01d030390b500030882020381c0c5400446840c0c100009012400c01c0d01d460000c00e000c100310540e14001310241c48c0c20358600152000411071b24030050f41d07401c6607000d25040c04015801c562040c0d9245400c1d052400c0002100c0000d50001e4035000c0085541d140814107903400040d030b83c0080000c0d4032420f042025100d00c80c026a0100858a4800310060300e900510340c0b440019040100801c500f14030700a0240c2c0c0300d41c242d0080303151a01e880341620052400080d03420200f2107003003c80f280c40e400d0960010b00000c0d00100d032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 327270773 1250 327269523 327269543
    0x905030703120609150b0315031c1805010c14030f1308070e071211070c06050703020105280f0f2c0d0f0e1f021b091006110703 56
    0x5160b000300c1c89800e07403070000344100441c64072600036100700c40108200d8125146500340a00c824502d200007190008000d20b204074400141d04002407801c0e01040d1001d1202205407400342600d600070100400c004035032641410243d081000080c10f07081480d001400801c0d411401c00103510b011300854010480c3d01208a41d5140300340c07040340c1444054420005039214002c00052806881c80200303000d003138142d440308078110316025a03502802820f1421200080c04100a03070002d4401941c01008007511b444040e00c0e040c06040280c2101c0005001c5000d041070040b820041403401b030549041b52240c21000189420541c0d8024001c102e007041c94020f4a2500c0440c3c41c43d2490380d0442c015050351142060242aa1440159200c4607a0032100000c2260074031074448481c090201c03210100c4000e0804004600e070351040c000c40c040005105805038012141d0175060342404000003400341c500b590302040e24208201c5070041100316226040400005022001c175920742801030740019030308248100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 327272023 1250 327270773 327270787
    0xf020405010e0609010c120c110d050309010f0e0d030c110d0312021e0c0c0a06050c1902030c041401260303070318080310060e010e0307031b09020408010609061e18090503 75
    0x1d0288035036980107481ca01244030741070340303549011011020318ac0d5002004c0c6007001d51503001565004101e90600040c0098202c00d0015a240c0c0b03041170000394003960300e01c1110f41d070303a04003e080b240c8184411409100c1852250010907046150382d0202100f401005a440c00c103414030442038604a043c2c66201140069001d41c0c01c04009125a07100c0710442f82c1c803440d141e4503042644c03144940d00b00040c09420018201c50044050b01640b030400d8000340a684840c1c21460005d400ca41c0c018800b08942d00b100801400400d8009000808040315451500f030000c814254075035881c0001801c0310101a181c04207100079070041550110300f0303640213080907140d040120125a40c0011402200700044d0035403280380303803984594145180b000c1e010700541141c50941e102e2084d0020440c41c0407501902d950760000d20205030f07200600040850600018041303050419840540c0d015074803034002d010076407003841b004140b914400021106c1c2e49103000c420036014000613024002911029003140030118441c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 327273273 1250 327272023 327272027
    0x5030106080c0907050a120911040c080a1a090103060c090305030f040303020610120204090302010e0f0705100c050316060605060c1509030313020922150f020405010e0609010c12 78
    0x1c500b4030700c022289241c040d82da5101c229028007954202a001800e550a5140c02c5040740c2e019414560091060088001800000c14281c443c9155401c00144882c0c007008000300440c460060603503d022035840142613070b00b001510000d0b060001501d241d50b9800402070f014080c440010040d03130311005480e19485810320042c040d030810311041d030140c00b410700003840310040000201c0a5650560755024400da040d000e100c004c00505104400755940c450219400c0c190070400e12031122500d9000b05806414001803011554121184100340503640e002e03080000c0c00031054034250380b1554003130180811107041542c09042280e03c19078010341d00042910740c100d008929402c0b00030181308281c01c50b81321076009036030360712044844d0711003d48010303007440051414082998005441400940602d5229420a900440f0350007040718940d25001016245030118000c121005014180450400e80341c000003800d00641c04a0980c841d08000503000f15581c003610441d04610b0300284001c0386038028000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 327274523 1250 327273273 327273283
    0x1d100f0303020304090f060605071401060f09090c08030c1507120213381308030f0301030215040609061b0506070e01140712111908090108090f071a040503010608 71
    0x144030800f41040001c6c8442c1d0399a020392411a200c50744c07524903001c00d9846581c100c2041c810f0503840c55483e041c00003480440f44400d10040e0040000005001c03440d032504440c00421175101f80c017940c20a01c40400c10007008103400c403640800b0451080d082d40e07000811078007016910991110107101007400070754540c0381035050054561035940440f04140c040c0d030082d041180b22a100e00003000d8490360f8030104504901800118800014448000c5e46071001581540c02444510f800c6000110041040d4504051400810300d529030046203024140100203104a0040c091071045c051003414501451002c2c1900c90302242d040720a80300d00b41404a001882043c0c010000b034006800303001c80d141c5001000781251081980a000000c4401001c18260384405005820110a000d40c51045641201161410203018403444410b59261090350014002810142c065180c0c0e502060101401c03120008081c0141c42400c4002c400314a5440050429440345170080e90f003650900034001500407000332 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 327275773 1250 327274523 327274529
    0x506151b0607020a14030310090b06090a030b0709050a0b030c0a1e020a0308061e040506040e030f12011401080a090c0f0f080f01020a020601150c12050304051005011d100f0303020304 80
    0x40c5c1c0069582e41c61480360b40d0b8041525000c01da846903c1d810003188289070b01071140d80002820352402c140c550360000d030140c042d80d4002e552025201c1c0c10014066440410f42e0007402003103d40d100d40c5400d119901030079010040c09564a000d0000f403100300c550041c0d400303c0061441100c00111914a040001c0d10745003a08000c5011582801c042083c07403400201d05a804032a00d402e904c1c0b201c0314902040007519000d02240d0300241c0c1d03007030354030540c41062000700002c1042c0c5403000c1d560601d112013503465000580c00840b407038880d008074191980e4050900c603000b4600f004041400f00850405010000c1e07240d00482a060590000144c1c0001800e411f00442d02903209540b0114103000342c0071700b40c1c45a50520401600080018811340341a030b030340c0d601010310602d00084440320543d01c4011948240308030710089076000c000c12081140400040c61090703032a1a00f132045500d0614000400c248030381508903a1100351000580081d108060000185610114000b41d5070383c3e414040d403240e010340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 327277023 1250 327275773 327275783
    0x140f07050318010206090c09040c030b0408270607061a0603070c0b092407020312010b0415140405010c020d06052503051504050a020c0601150f030506151b0607020a 72
    0x142c95800030681c81d2241164502500070603443c14204185e101000300111020001000c02101151004003017902c158030905803070f9039031444004030042240b0b225818204030103c00707050f10140d480e0882030728419684000080f610210071f07060480329218101100345c11400c04810401d150703604c80004d11540c0e000300c3d611612529448a0151910005400d0000000812051601440d040212940d0107403039881964202028251a943e0790502a03010800d02c46c804242809502c01509101c4900700b4a42071031403031440d4030305454550303018500c1014144502c5404c98070654860300520713121141d101344104201d00e0000980b22880417040780c603170201c1018030b8000c01168080c1c13084038000c035450708100710301261640800010380070050810084940034400ba040d403060810109000c1c12001c2070742c2c980a0714401c2c2c002c14054061413100d0826042105100c16511036031241800d0320030401003103990f8003035202c65802c89000b103803861b00c981c4501304c200900785601207a016101d078410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 327278273 1250 327277023 327277057
    0xf0d0e04021201060f0512150109060f020d0806060903100c0806030a031715090f0906070f21060b030a0b15090108151207030501060e0c0316140f070503 67
    0x150090100301d0045408001c140b15480c0011311209015016101e1081443d2070041d140807544803c140d1921416203050b0078411085080044a60304440024041d149601c0c08045841c83c9000c000e40e038544110b02d100512270100c3c00303c9d2454940c0c80481c1d25020000c2c0444400b0b030302880d480d40041c003094440800042c2c42d9230101d0442d14011038110b44194055403400542e0800143d841749080c40039100550420003442d90340c0345500c2c4c540095205410800c4944a24a0992881401c4c2400145000c00b040400e0324010010740e0403592801800c0e190065004c0d034480180741200003450a60000b410003c008810040b0b0b030b2140760801d20b0070042c240c80c69a080e5200380f01e50b0302d00e40202012540454117140005005006110114101c1d013001458503a00d0010100c1e0300e070a00701d0325001a202651a41c00030300c4003420038440a9044a1102940d43ca513203403403480c100e07101d00411b5070003040000c5400c44010307081002058170805080162295510405071800c4d0ba0b503540298142c0c03844e5044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 327279523 1250 327278273 327278297
    0x10504060b120f060f090a090201030507091a03040f1e0302010c020a02180a0605120d02011401080a080a021005100e0f010b0d0b060717030106110313090c02010e0f0d 73
    0x21015140c00018009041c20182c41e48036100c0701103c0c0090405802c5120f5580303003001556a03600301d41c0542044540002c0d1451680001419141c0003844142030012a08007000450144030108805492460f05582c4a40b502c0c034240c50450284500900800f50000d5902c20140103000d2084203940b094008000f04800d03045c1c02e81e01ca45690002943c42004141180062000502043e62000340c048000034600d4079840002c105845a0303005600551265900320186902485021910b40796a01c00f402c8640c0f40010b00e59071611a1328008128440120b00044041e000b0000740c240815030300d105009c54680703007c1c91003039240e081c0b00382c0000d0815a03022441410300045540d040e203810741142c501d0a070705c41e544200a000030418243c2c02c54002c0010b0808106009180319003003003049034060303903549002001011100c40803d4070000b40c01c2007160a01c400c40c10b480c00000c071014500c022940d00c0040c1c20070382c01481280c1c018016802502e5203445140300105001000c40080d403503020390300071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 327280773 1250 327279523 327279539
    0xf040305010507080f101a0702120607180e07030e030706050c0d050c0c0601060e0d0c091b0f020c040f0e030a02010e061803040909050106031403130e06090708150303040b0301050406 80
    0x546d024103036158130b90000e0101d03407030209002c1d45e401c500065003450300d11280d002c01c900503107007000c040c10b58020405000040303138440c2c0418407290102c0d03000110103082c03a41104aa0300b02902e441c00b0303d0360f14405007820f00b10038415150751a800000400070381c90001a621081d50092003041211464000040e115800c1d5206480b800d098070401899140e081520998000a801c0d0303843d64065008420705000514041402000d020b0040020689404102604142c00160460102440003c030f0324441500d0340001c2d560301940041702c001c0340b6000110307803d00082440c100ba00c503081c0000105c0c2007074150150845528800c12900f2120542c3d2014510b00d0340c0c1f0b0410980d51602d4200700f00400c4241e126400c40c003017280c011400090b101d41d6070f030364400e10a24449450017907608003149001c0845400c1d21040018941170011019a1402c000082c0320800001d0030441405140f0000c60a041c90141c010b288046001e000c80360380f6a182c42ca1110f07070340c00911840740b14038200000462645 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 327282023 1250 327280773 327280801
    0x111160306051e15040608030c010b040b04022b0f050405010209010f030c0906140f040f1505090609120a1b0504060503030702031c0219060c08060f0a06030207080f04030501050708 79
    0x5070384034460f40603c0d1650501d56002e004600225035105480d4200031900301e40c280012704d074801011000048176600c03d028402900d605881c40e41c49a4410310821185509202e014003541e040302010f41c58518100f444507004010360350848021a141c5000c110400a0550040c03481490903203845107890148001202034480c901e000c3c6c00080c0e00e10030108001c46c061004100035102861a180c10405140385641c103070781056000c0120f20a10120420010749025080d8115a10344c2c9005480c1040040110f020741c828031000c02e0088190b41404041140c00f80300b10005584d1210030900d03c54500310442da481d40302e038000e1601c16403a01100203458a0001b08642d80184c0c0500686101c004103042c408080c032900407103600354011030b404d4030b0580c407020f1058034403644220000280b1120071580100000c000400b42802992195009103441d03070b98000d04402c980c800d150250365a1030300d10b811045401004000030800501003004810084103401540c0315101680e030324119551100b2400c2244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 327283273 1250 327282023 327282061
    0x120f05010207030806131b0509040617070e0705090604181e0506040605030102160803040f0c060302030709080a051c02030708071202010e03070f20030a1b06030902150702011116030605 81
    0x40c1070802072908003801040034180841006000040301c8ce034400900d030230054207004078042900011810f008c01d0701b51400311078000c509441c0072810b01032820040f4000c1c3c4204d000c4d003a4105803454404100316680d0308142001c00140c0382e13204041190321a1040a0101076690500c128140310011070182414801e4412101051155004c041c03d0b503120301d0140e600180003030300c0c6c00514982ea040400e01241849000340255603006070703245440c0348005e021a0454215940a402c00646600410300006030820041c580c032510b449190001d01d400e9186200788c4030002e180c43c070041110310500c0503c1d42440c0d442e840b507070005e00003440001d11064891060074001000c414034a03098001040342e502c12004010fa1203030300a40c280940b10006403031b003500070318100c82000507009070500c1d0020110000000301018141031001c0300441c1d0008400c0380c2c07000b000e80d0b40c2c0b000c0444e5031401c1da0310500f40c40c080d58000f00c0950350039410746002c14400c0010b078002561002d04210126812801c02c105003036070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 327284523 1250 327283273 327283301
    0x24050d02010c0b09030f0f07050613080a1808010609020702090f0c1206010e090a0b030c09010503030d02030c040f1d011d04062c1b04050f01120f0501020703080613 72
    0x10b0040c01c0d0351024010304001d00101d036103210912080640e0420354009041c0c8462500c1c001d070710340a00749410f62821200400468101d03281d6270720900000c3c2c0600c250b500c2a03001d402d0a00d1141d0407100104880c2040d0783c40b402042d801c006000880a085070300074610b01d07000741c6021905030340f18104440801004e440b0290035001c1009500c21f0280054901e9411240500d015941044020001510050151044012259180c140088500e01040f91540080c8143d500504561615000039124022a4011150580c00200041070b590b415001c441c060301204240d0b1414070340305d00c1040a005400c902c0a8912038140001183d1791a0f004116039640c244403d201c80160358594566004e80410418460124512200c0d10500c4030840b10303100260422070b00030041c00000c020301c030395281e200e40c0031240900c1c581002c2c40380041450203840c4c10348034040e00050444076286170900740b0024184e0050441c1d407011a9070f44c101980560b00c40d003c3c2c2021030350030f0852075050941ca4101d81a204403000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 327285773 1250 327284523 327284537
    0x111308070b190c060f050a0e06061c06200304030206070302032202040b0a150e12030703080714040303021c0e0109031203090803190c090f0b130924050d0201 69
    0x1044180010300307415082518035002d00040c0403a59444c0543e040c40403d00300194503842008200080c2c0e10804c42c11000c004010f15a500f001804611810120504a0b1021fa901000c0d002032081c0394011f0000252a0f03001d402c4d40c4100002500c029800a0b50f044005010351400310707084a209001b83c170300844944510054440020651004180400004a8109440d01001540d580d0381040e01c0c0300504155298181039a0041c500405515030a0300701c0f40701c3c60b8030080c050040e0307400009950318540d0608151030303592160b100984000c030300c4000d1107401900026000c0201580421071b0380c449a11040e142e0410040113600380d4007070894001c0e050014201075403c0000c2500c5404092042019080004502c0303455141c507680750740704030b616000a001e00300f0f40482c0b002d010b100d00700000090303240c900031071410041c0b1001103a0040c80782c00e82814000c01d100c035018000d201000b0003401c0f001400c104290321501c070202c0304003c110040d003c41200000005141c207007030520700b041079416940c41e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 327287023 1250 327285773 327285787
    0x7080a0506130c080a0309150f08040602090117180111090105180f030304031a0a15140117010e0402030c030f15040609060c09090608010b0d0308150301111308070b 72
    0x808030007000030081d0ba43e403100503400150080300344010400036001c1ea4030b10380d285007450144841c241c0c0d8101c0c06030400900b6801ca06450b54010110340d0402d03071100002d42d0301d9041900494103d00c0001001590280800512035041c008a0380c02d0400b50400d402400503212400074030351140105003945001c520100884190ba1041c400060300d070381c1000f4107107002e6440000100c1c2c6181c0003500704865503d500c4401080303011815200540c0074411030000d120810480841c044c0d050708900c1910049102000b0591041c3c0c0030305800d80a40d18000ca44180d5983c1d80c280d0740725400ba003074038240d01034094680046420305010541a070404000320040501a01a50318110003c0c0b0042c4240c90003079840200c0c000084035401408002c0700c003580c0c1e42c50414201601c50307049a086600c04a138580c034080802c42c00340c4410030b13108a09500b506010b0519962034565501440d803a198250380b42d468510a43c0f040e003880000f80079000980d04506840d01d0311158100c0d42ea0b01b0074050315000180c24001e070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 327288273 1250 327287023 327287041
    0xa0c0206070201031e1a100c02060a0201020904090c03060515010f0c021c060507090807060207050d1b06120e030405030c0f030a0b070906031a01090506033607080a0506 74
    0xc041442c0b0603d400940d200000c0c000f404811483c81994200c1519900f1400024034803200500c1030341002c0b1404d59001301c26000150500c0c0c0d0b0050020f01406002c104014403e0007907041c0c40800300061b00c01d2001d0000d61400340b2000c6d4450004440551a04020529400402101d490202b1041c0c450000105d049402520f80482140040380c1c403448124190071520003d0074618001c030303c140408641070070000380c040c01026142d041502198001201044803590000c3c5a404450050361500c1110886003400310442c0c444001080c1304000034180001c00e10f5000c8182c0c00e80200811040000d8115418159124402d0744116641607002886030304207031030b0040d403514901710f0081c1261403500c01c960b00d1494810044941201190301c81e5410043c080e01405110002c1c0400a1482c009038401e034006071291406000b9207000358000700003d81d0141e1039003428040c0324403c50000c1c94803501d062451a440c8a084041e2801c4d01400384009055200002e021003190b038414058291a0707245466 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 327289523 1250 327288273 327288277
    0x80714030a0e2b050a0c080a030527061b190b0402090702012a20061303020309122a090412021507020607020d1d0409020607060c05030411060a0c0206 66
    0x7120180c0c0d0340e01e41000c480008690007a2640f51044000e00340034a124200408403200c0d40e44402410b0b040341c061880000e6101d011950070020078140b100700c1c20300450345e00403d0240440810341202000501c00c0b200b00d103034000d0030ba010442e2012103d41800402e100000b85040440c024960103c6401040051030600d040307035070040c3c9904c00040c014030304107661003210242e01c2200a0501410381002107003640145a4100c140141c2c0d8006e543c0071460f098999113100c01481000f4010a4040d003000301031003442140d00385203008103081c0140d0f80d090b119688a81c0c80900f51380c0740e1141020b400e2010301e40e0340400012410003e15188480d5595140e111095111000340c0085000f0b00e44a107003d60228803046015029a03030040c096440c0c4104044e14004101001c0d0081c40340140c680006c0e05031818000584560030340f00481d00195a10105030140910f8000a0555040160841009a102019502c200e010707034009103004000d034040c014140300f0004000001405403140380c0143c145000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 327290773 1250 327289523 327289549
    0xf021602090c28021c0f0c0f02060c0f0601050a0b0a0c030332070309050c0d060f05010909020109090c080a0221090f1b091f0909080714030a0e 63
    0x1500a01d8408080150400c42d640f00d00450b940786800154040c049604000060100c0502c0c40c0303440c101e500b6028041d00c41c100c0c220700101040719074401202082280240300c042e1590203401651038800280103a038860181d402040b80c0e0b4441d280001803036252240004c802c0b40d46a0501e00d20b4a4010070045030305e580c4406040e41890b4841102201d059000c0b4085039400540040d0230b41004a4202102400c0c00040c00c028200350902c0242408070300013080e034101b0008100c0c1c10b004007009503d0070030042c0c03803802800c4000610300303000001c030140340e504030314035103407007660342c0301c0c080340c45200d10421103158130148400a0600c40000764143c01030350060604c000a1520160200c2c40c03030b41401800d40044886198940141880508182081210040142485000346005e4161401140b119413008007200300c1d02d2120f864410b500c9585960140140007a800107211011560500d0481d90348410070482e0001e103a800000300c00100481a02c001151660b24484200f104c002003084c0c51040788 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 327292023 1250 327290773 327290791
    0x924040803041512150506180d0c0f0b0c0607050a1b0c0f1a030604020d06050d0305070b07030e0c010f0908160e09031608070c120302100f02160209 65
    0x4408200d0100c00c0014000401500711120101d01e88141d00404054071403411021460900807205030341d808840b44030060b2101500e441d600c40640c2d04481c0c11040c00c0b201441d42111040741c40c0c2062010341c091034006e440582c6861403e0039550513524003a8800c010b10406241c100c18081030309240f043c002850203104600d41018031144802403c1c2440300381440c11200048494801c110f201c40f0900c2242c01064580d105492426103c0400c413101e100060070181b0660740000c2059218546600c000701500300502001c426038054503029205030301c500d038150740140c4203d0009110750700c280a03424000c0c050a001d000509030f00740056a05100700580302040c0000c1403004109860108800c0d000c40041d41e98040c02141381245500b80150003900d422441e0b0000c026824151001c160744d10841a400401d45643d080303142000403002c24541c201e6416034a02d40a00c1092550025080138140440c003c20001100303810147c804912500c2c25240812545d100c00801604d02404642d901c40c0d41c072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 327293273 1250 327292023 327292027
    0x6070c0507092415020d140f0408060f0603160612060e0c07150501081e012a020607080f0a02180415030311191e0f030809010b0102030924 61
    0x98001c54050f6400c0303019150303844a0300300102a186100b40d90101c001d00918002518661010038004d4aa292104468060103054001d441d458000c0e40100d50140503032200107515103840d01e0840da01c80030305650411002892102140300c506d00400c030103016600307000c2081180c84c03500e40d050341c41c081051034044e9002c0d6a140c0004040302e0024000e44503d2000301c21940e034141c2440e0403403443c003660760004030fa1072a0100510038481b00081003548214540b414694414681e41101c0c05003684840302f80f0481803a250b00704d10f02c00d0207010207002900c940c080c1d43e500d550300030f0f080b02e851400301e422240942a01c404201217900581c002d0020a5808205194460054010500350f406500414200388408041041410b5001d41d1074005500c4000151094890a1600d144038012241e00500038003502c5005803c00c45d00701f80048880d60348410b643c06c3d14280d030b0401801039081107482100950074104091680d62012040326400078006200314a50400c101c088003444181c01c80030f81c100a01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 327294523 1250 327293273 327293279
    0x90307020409060c110304030507051504080d030c1215030209070e0405040f170f0406030c050c0610090f0905030f070201030b0a0b031e061c060f3b06070c0507 70
    0x280b8014545094001c16011481d1450742038024810004404140e0154000b4001400001d0f40400c0c1c5804440303007124049151001081c0f00003803441254462000340c4101038084081035059044070400014545650b5004c44103500c11300143c54083c094a800360381041401d10040c503000c44c105412a9640c644001610440004182112400e950a47c0d0901c03410419000704000f00d881c0130301102c8002c03011402e04410000302da0341c60042d40201c1d41415200d5030117405036031084054480181e026070440b030241c20701d102549042c0005000e9000c8060134410602d035200500e0056035992079000300154940781100c007802d0281d41200ca000c070304264039a1001042a9103107003060016101d0152a95601d08000c1d021004115200014807414a142c0c41009507540c0d441c510201210b415000103025044903140c81402010b00501643c0b9251034030302d40003212109921f401a040b01c041c824900b039241e0241010102e042032443c90300160f40700700009450f0354421904600345612410440c0d1019403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 327295773 1250 327294523 327294529
    0x50a0209030f0601150e031203060d080a08060102100507050715200a08071d060d0e030406020a0c0b040b030402100504030501021b16030309090c0207030501060e061806090a0509030702 81
    0x14a441d450b02480d0f0100005000a00001190380d00001890500c1c003088050200420745450a032044858810342c0070001407026152041038003c1c19a10880e4940d50700e800c1a0003800072042034860300d0040c0b007448103540081090b48505070083d07503207440361810220305544002c11324444801c0c1e40c03107a41d21503024001c411070164044064003440c0740710a4036003114840003810894010004420041202e5072006588010100060021025582260f84560045496001d0040d11410040d540b100080005607954041804001148121803d020140c1d0350b140c612014083c50007050145401000070900510346881c0206089400342480c41c1816a641c441c0703803ca8201840140c2c1d40b806410500d6007205042c402640c11303083e030200f5865181d0645d100108804814090006420365039440841c00500070032280c8011903201009120f8103449605210f03602c0340c1950080d01840e0f06524281c0b69140c00e1000c28464280542903075450340d0b400207114007514000e400c0244500040141c680940c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 327297023 1250 327295773 327295783
    0x3041a0705010501060e1503010b04060f1106190c11030a0f0c05010609020909060d0b0604022a01060305061b1608070f0b010f0902070f060e03090901080c190b0d050a020903 76
    0x70240f5240c10070020b80040a00c1187c3ca45940043d0308580100010320224410905440941d4041d10b070029840d5480e090079105101c01008200d014401c1008100e01c82500c0043d00741d001c2c242d03c82c1400400002202a1005084d000084c4015002404036000c050321030301031400085028a806179850003151255400c540403031300079501050300018120883e00700b24103e5500a07800f40c5400102d000d19803500800d151014000390301c169000108242d001c403441d0340384d2100901503040d81d105010740c41c0c142402880c0a02c8100d61900640d40050740103c0003200da00c0d00100761180080c03802022148003207005004820441e14000e00f80080004919820113030741c0c40c14800e0911140c0781d4105454494410351940c02518060b004102c00000149100d0072001990342c000ca001c2004120754203014218000c0c040a550044080c40000031442c5000507610f085d40c5042d221018108a007006851100f540c030302421b914288104020007401140c1e5004950142c4106d400508141e04c100002c1d041c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 327298273 1250 327297023 327297029
    0x21b18010e090c120a0b1009480f03060b0309010b010225050d0212060408071208010f0311040e030a030c09120c05060c010e07170d080903041a0705010501 68
    0x2080c0c1c901c1004142c0b00200b091480c40182224034039410340a07401003581d43e40e00340c90014400342001d00405d6909010840e224040d1200841c284501c2c40580c0001403400c403840840c81001540040d02d4030440d02d044090aa06e06100c0ca500000b92402c1c80c06403a1120b14070121801c050303076000005184c2c04020007560040070020b0022031410059000249001c81240e5440784140c001740c4d2007459102e00426103001c0b41c8003a2516208079090b0f00018002e00f80c040c10314401e5005010400040090f21001001c0045c0b203002c00c0d000521039588200c450b480c0900079401c1071204240140041040d8250309211004020b0001c102d0b80441414207003590001034090300401d0300c40c02a030801d0764001c81c4003005040034250043d50701c81141c55058401103030b403160074000c540c0000e45020306c803007e40140115007121001c42e850295590b800850f0015441d05e81001c80c002c0c210383c040118410701c90305000d108840c005506007424040d840d00c04000d98003042c44080c2c0200254400540f0a004d11802 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 327299523 1250 327298273 327298289
    0x20a060c05010c0327020301090506130b0c0a020307030c02120a24023c040b0904180b01030b06060c0111040602120f07060b0a031e21021b1801 63
    0x80415500d41070342900da03400c0c0032030145400c0614a01d4080801d04858440803034500c014401c00c1020b0000c00d005025801001e020350154900300600b5002d01d000d1880c000744680030321041076503000520113040c0107000e080f00c010b800800c08100444e100380110002c0900040c803041e00d052030186100e1914410400440c0c101d240700030006a4081d62800c520035841c2440d00c01d51a00300d03822130240c001c45800d070070b451000c0300c60b41800021125960340e0303081e40030750090304555561302e41c0c549203501d400410410707106502300071154801d0030903050040040c99104081c600c051b400c581c0c074600401402054990032071004d20440840302001d005200803085c040c089a035a0b54203218000b070400290345c8100c070118034108a15441d40c0c0d0758030111a4120f4001c1d50014000c07412100060414503e5413001e000c20784004a480c46507242d811034409041d106038401a48000125805002070383c030840004007581041c400d003c1d240400300a070200030f460080401c80341c0440622400c011403c02e80000308 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 327300773 1250 327299523 327299537
    0xb12070305090c0306060603070504230a150e2e0507020307080d021513060603060212180705040e010e0106060c1a01030c170c13020a0905060304020a120f020a06 71
    0x5480c0c05214440d00031504801a05808034903501203692003d003e07040328000d01d0004001041684648103440181c05000d07103259201603000c5040031401d54101d500d502c62010b03d4000600310b0060905588011071540340c1354800c200020401801d0140b182c001c00300705106080240156011807100c54060403991074050302d4103058010b1526011f059080450181d00002c10b0300045500000c0c1d213038040d1b4030104d044407170340d4a032a100308080b1142c090050049050800210400603150064451000001141c5066076200c24070441052014070359010030340c00520041c4560300341600101c409240080c00441c1050080895508480242e8401e100082c0b0342d803401010003180a0102c8011359000354050701d19411030322241c0b8403440364420194500344810f0211040350041c083c508255000500140360b0140e8913203480c000e9844515644005050603034049054513001c4142d078041c50b00034041c0c10501d400c0164520b841c0002030303000d5480000e406480030040c2d8902e103082c006081c1036a910f203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 327302023 1250 327300773 327300781
    0xa0b0d050a050c25021903120e13090615030b0402010906021203161b030e01020d0309050c09100315020418230a090605150a080a05060103030c06060b12 67
    0x110031a040580110001801c10003404440400381d016a02c0615601c00c2c54100601c4110500c1c04134005494002d40102c1244158401c0351407940300d010859001d84131820301c8a480345030407070b800d4030070981c0550b101e00c0c0e81c201000001001e5004c0d25070b061065100040c40303207000a45002c0c0103453341c0100da216621408000455a0110401c0d000388290700040c070584860b100003021a000040c106444042d00504081d840c2d4803404a100340e9801d100c2a0403011303000b90500410400380781c01c44a000d44120381c0e9850110b03109118080b030280d0400b01800001210504000c2400406030079103070304144411020000c50003213001c821a60100302001070ba10751900794818540540014041611807070084100000705902401403100100001a4000c5a65003202d00b401003080d003802504040c0f81404010304800f51902e081e8074050100c9109a585a5074204542c0c0c8101d00038008040390044001007001a01911700702540b00c1c820100410500c0d06c4150b4a00950425030000100c41c070f01c00180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 327303273 1250 327302023 327302047
    0xe040503040503010605150904112b0e0708030d020a090f060306080d050306130507050f04170601080d0512040809090403031515020a02011d0a0305060106030e011401230a0b 76
    0x49004090541d402860b00b0712801f20540760f8000c14820a020300c2c0c603113640300c2460600c1002c451005481144aa05020511a032100081e12810080310028a0156084450640018414100c403400d500652501940e0a64000603410510715401030103c1c0f140c1c00310ba0043c5480950000d0305055a0002d00189024802490041000700910520808105102080c0c540040095510443c4000070a043d142e1001c00c492600c50f44038a041c212401090114000d102e001c000341e800d104040486520307980b5244604e0710744203084070f80004a007081291500050810101543c0240115681820085000049600408111001c400081e910300381c0000c007020950384040602403032200701e401c140414501075516041004064148400c0c2e250000d03e1300c44480760b00d00a038001904030f8110560b03901d0155683c3c038081c09200d011a080146407040c0040500c00d4420810004d420f840f842d9192249501841101d080b80003001109400d40d4202a12102c0640004000c0380c80d0b03181d540c1500c0f80f54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 327304523 1250 327303273 327303281
    0x512030d0209030c060307021f05040f120c0c0803090909300409020a0305010816030206041e080106030b040b0a1a0906040f0e0706030b01050304020d030e030a062415080106180e04050304050301 85
    0x27200c0000c9240c1000d0102143c064842c14484030350260502e080f40d00004003c0d01c3c8410f41c100024150001c25001060091021015203103552080e502d00180340c40d5250640c0e120030b0f400021a91070100080c202e141c650f8080d45a0600c00d0340b0004051400c0d13200d101d014240d0348050880c04c04a0b403202c0040103206010400b800b29003000fa004242071500b1075000a1181c41745100c0d01607203400c010340b11419040c800b80310070020318503503008000c0d196132850450490302c0c0403102079600c011100000f50424000b4012040300c00481920b000c42d035610081009aa0000500030a41090381d07106080c20344003da125070404844500c0080c2000c525090004003582e003001d09650400c4414024400140c403401c4d074070401e00b80c0c50b0400d80c0c1c500707455001007407a204035003001400c12418220030f0040107420b410b003e04040680100310724010b07160300d4422040006010081c000400d841d0041001a1203410303028607000001c04180328990380d174592131880c4901600e0584041d080005c00b0801d601d02403003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 327305773 1250 327304523 327304573
    0xf1a15030c090a0f1508100c05192d020604020306060d0308190b09041119030f0201210e0c10080601020a0f05010b0a1e0512030d0209030c06030702 65
    0x100501d9018440004908850b4025021800d119100c8410061401e8107402003443d502c1c400d441e500c1050b80e2100d145a032000740b4120400d5652914038101003140c030443c119140d205200c5540008262500022155007980c0b0780e0b00c0100c6131001d4142510a0940f00c207001552005034000d0145090500416007050009130009124207c0d400729040003a40010f02941d00c6a0041c42a0403050082020f201c0684884012a6845030031102000100314000c9140128000140c400c90700b82c0104481060106841d8000601100d442d01d230310000661090007045102c12400c086070001d00b400411113800c3e42c400302010b4140f50004944010b050501f9252041038030b030305103807460050400740c0010b900c41c42003034009003002c0c010031032010600c0009d4000e2401e406001c0c2ca130580003591003104003401c195000600c5600d0381c08a800040c20315007162800c4047c03e0b01001703146080320260810b0011d60000a2854050081c0500081340d982c4500c055445903440703801034481001418800801829155 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 327307023 1250 327305773 327305779
    0x5010506100909090c1203020d0f020307020906090402010c05030a0903110316150c050601060804110909070603150f03030c02032503030804150608030a11280f1a15 72
    0x2400101040b64800c10032001c90b5600000003c04150078280303010820680d4014038401420500c0d40c0040540c001b903042d10400d96550750941c00c1c1c002074012038607482103607c0a98000c00d02c001150003403804010140c0c2103031050400440c11900d0b40d54860840c1c1201042c0000314074a200100b003807141800d0380c055956000c502074000300305660b844590020340c500844201e03030242070404e40c000d401662072030790b072a402c182115420369540100034010b840455044555034500500003203c4e041584015000e00f010601421341030341030000032002090392345101445861a05000203500703c1c8400c02ca4041c50003a81d451481c03c0c0e150042c18a841901c404081c1c2c03084400b0001c04100e881c4010305000e5039898a080f081d241c6542c24400e40300c103e8541d41d00b40c035514060000076030040000081040200c01c1d240c220700c40010780345103501c0e0302e00200820010401c1c5802950854090000d000711030303201c0c03244c66600c0c2c004d0303480e20405524207845000c41c0c1c40341c40d018401c1d5080324403500d030640d200c11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 327308273 1250 327307023 327307039
    0x5040501080312060303120103110a0b030403140901030b330a08130204090506070906020d140f070f08030f01090b04020f27030307050109120302040807210c1205010506 74
    0x2010300e8641d80d00c80c211607059000f160401151155030107008079658001c1101e5046801d5840e0709009000d064940e803030310302c00c10041d078000454042d08800e0300c0c41150103072905007081c0c0009040c4c4d10b02e44d100303800b29410550340d940c0070030607603440044070b80d44444000314424a105041d0b8071000c21075a8106d8503550180305101e1080c0e220340c0540710326880b0a0901c25100301868030320200c3d000e0841c01000400b1801243d00300285540d000101f10708403110f5908a400e4909152000c3d10848140200303410743c12820042074490110650081030083d00c2516051205c100c81e840700c00381901309032004080d942e8600d0040103180898008c2c084890011603045290142010065000e0320464038048901c4441207021065480d036110811261400a401d13241e442c01c1600c1e01c94001d00b4031020444141e40351526a4001134840e109503015682224010310b607440c140750b0311076071440c1403090401011490000800024888100c5000140072623044086036101624201c0d003074540040c80b840c007078084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 327309523 1250 327308273 327308279
    0x5090a06031d0307020a0b07031202040303030e28031808030f07060b04050705120910110a120603170309010b0d03050c01050a0908030105130e060906040201020f06010302180a02071b0f05040501 85
    0x2084c89110454840c07c00f45540c3d001c441c038003503440c240114042e8040d544042000401c0c15015004404007000d500d003900c0703c40f20f00440300b0004503181110f504111035140003000c0024020754607110301000e190038030705405544c0c0c0300c010328561081c14103030480400414a0001c000ac0e50091001c0080c045600b07220510345803100600320b020399001900d4004800d00030803078035038051210119100302c0103c14808110340301c038038a43d40d90040d10b145000489004d07910300110114480e40c42580e42c0010204040c2d030854849500e15040640f007517040303550320005009035036903025110120034800c0c2c58203a15a040031442c1400c46500411180300f560402e00d240d00021000b0044a042d01c404503132813620b14040b1440031004006000d801040ea101e54418014515800034a0350f100368803d0b4221090f4004200805031511401e2000039040a07001000908c0c5409115030342c0e6104a07204001030400f1000e440310f10001c04840c000c2e10f4814000706c010700a410100e1003240240c6000e03507090240d545 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 327310773 1250 327309523 327309529
    0xc0711060d06060f2d11010f021b03030603060f070504080a0b01030b01080105090706301a0117040809040b03190b09010b010c0b0402030c0a0b04050102100c0f030c05090a06031d030702 81
    0xb00324801c92001640c405103681210380160050307906c21030040020007002641c3d0306d01a00035881075180604c800312070b4407110409180002204c0c49484081c01800a03030700d0751840418461406071010702408000d10001c5001c80e4100b04850a03140944032804072075140d420000e01d1500180c2000c40d840c0d040004010b510480000c0700780444123280703013418060006d0003450600c40303182880100381c00c42c983c264048444880c0c20800203080080304502a040140005403106203840c8103404110f59103500103000704240002a083d4480c02410100e09a5000c03400030f1309114809084240c104203080800060040304211182d10580c1c20000300108012180080c0c030800d4400f40c003c000001d0100040c045403002d2090710b020b2600a0034801072543c9541d1600000c1d00207008041c01880380030b0040b224140a4000c00c420440b10f07454880120a0110040b07025005a41400d424050f0400c0001c5858451110314802850300e44d8002a0002048148920a201952800205510500030700005da5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 327312023 1250 327310773 327310817
    0x7140d060e061c020f0a0b0a030b0f01180306050c0904020d0f14070527030d02031c1406040209010306030803090a0501150e28020a09030b0601080f0c0711060d06060f 73
    0x1640448080f000381305c1030000620114010b80241c0041c42020a5040c1d0752034054102c224140c43c102c844040451104c401103a641c8060001060740441c15401040030802550007203400a403000340c04d62134040300c0c60100b016a4020404510441d503200c91000da041154465140c80d00b8480d0610b8580f81081d29004147d0f002e1300c1d1049540402c1124036040b00c155124100c0d030b82c54009000d80f20260282e60300a0348070b400c43c44400c0c194200d803501c50710729103143d8801d110310308880940b1a00c10740c030f8030000e00c0025008200c05605140c0c0e54100030000c2641c0c640590310030b018180051034480820300e40729081d20b10184c240c030050509a80d007801400c01810100c2e0348440f00e0b20a208087c03181a11501c604102d0702d1244040e10300c005903070324019038081c0d400c4050b00e000f015101036584510004407442201140d4040328030310f034080403c888542d00c600412401d1302981d050341401240900082070383c0e10010f601c4010594442003001065008010f141d1799440c01d00301200d407041c081d006c5003514 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 327313273 1250 327312023 327312079
    0x8030f060f030705041104050d0525050a060c02040e10020d060f0e040210091206091a100506030c07060501120209070206070c030825080a0b0d0c0e07140d060e06 71
    0x5961200e45200c50303031b01c4000c20342c3c0050200506a0203000c144d42081078440c2d042e00e1340400c0645000c41c4155480548945100c1102c10149c645e4000c1d61510800716041d1600d80030490740661194180c014039034003008180150049031400581e1030704514419411203d50b51701040e000380844a04020038070800600b260b200c1c4d01500c000012141c014421925001c0d05d8001c0c0b078501b081c0100020502c0a07591098000c18403031052542c03c05d18440d00c0c034643d02021954500d2000004109101c24140f400182d900291184102d6042c01460b42c0c3d01c9003994402d0700b019819071442800b40044d45458010150484e00d14005000b803403c0c003030f00c010062003c400000c0c0901c000c08021500301201090440d1a1a41548800a500b078004100806003401907a1112085050000c07885040c039000700000b00540e032080c1c003020407501e40294500945402010700c81070141422225914544a9009000c481c150320710006411741001c060442200000d0402800340c080003505009000a0158032940 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 327314523 1250 327313273 327313279
    0x10c09030b22020d0f02040f05010b03040f050304080304171009081e120903090102010c11030406080901020705071d0c1213050c130b030f0120030703060503060408030f060f030705 79
    0x3202e0300841904120302141a0300039000035a15155809004020742610b014910848091251000103001002030380c03000c0c000c880c10f006007003000c10700280c2c0b0502042e1441c1c0c442c1c0d09503810036640c1c600e0942560440e41c0000b501c2d40d0290000c02d03034181c0c18010601800310364a400c0001859540f6a42903e002e040d0922641200f10082c000b03003030300b250342038a102000481344a001807406502e8241c5a4008840441c0950b00300082030741d00703601031056010f1f85280c440041d0305091408500701c542c40c2000d40001d0b40c555007001810f0215900703000e090701070308200c8c0001c01c032007442c1c165012100c10001c040130342e100d100380303c00515400000c40154001146c08108001e50849042580c108003c802409a12085c0003800b20215000c64010700d6105608400b50740d00040d224010900740c0d4500b001d03081c40e16a45030742004401a0000281d03400001a140014440d40c42d8408a4949003060b5410f80310100c020042009043d580c40c043d560009040d02c0008071000440c0110303a4408241c01901d00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 327315773 1250 327314523 327314551
    0x270b030103080a0306030f140f0705010509040b040e060907080d0504050d030c02031924020c0307021c061a100507020306010306021b030d021e0a09060503040f0605070e03010c09030b 80
    0x20303404c1c844d4001001843d0000b811900c404100c0c60100101c40124038407a00e14020244010619000441d401003265010f0b101d0310304d01400402040020400c100c02c0b240c0c0140d840410329101c40d0700304601c0384181130388002000d01c20b040c8000b040c9810484403180003007280400c400d000b961030b90004c50b00e50390780c1801e1194850043d440000e00b0902401200c0140c19110b94241c0d09010561600007180041120006400852002c00e601640b24814240c40158030401914005040070039188807100d002980251050641d40d540307000b920000e0f07510340c182910541d40ba04135441c140009113801c1e20b440c00c0162500c03850f503000c6a110b140500c000741c40d80340c0c080386c0049044125205504924051800e480c3d6900e600c5030488000e4110100c580e0017007008502030f280060084007218450314207900c41440c402d00d020022903066200500c1280e0725103582c0001000105030f0f00402c7d0155040d80c0350302d007148600c0420305d42124503110b241c1c81003010644081000c0744815015a40107014809884 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 327317023 1250 327315773 327315787
    0x312050a02190c0b01091802091e07030203090106050d050a11150a0203040914040b0406090318030501090b070216060806180906180714040b0a0f06270b03010308 71
    0x3402805050002c5510104402d0100502e55114448409a80c410f03602e00e26240d80710f22000003107070281c50146107540050800b0701c001d45800c1c03409030792050758003c46010103c0318512218505c2003c2d540240884d4001c402e0000c01c40c4213004001c0903020a440d00c0c0c1c51440d242c0c9642c0e50f034800005001d4001003c2291010883c0c4a00d502042c0c41c011240c20260f44031070800009640f030380580700f0710040b04d00d0651510602c0203182c02442c050b98000c94070307150b5038032140c407108010400340c4001c03403d2120050000d8100042411000025030081e0000214402141046550b602e80100040c0031500160103040703d5000c2501440141d03202d0b8540000fa41d503c0601041c0741d0702c0701c1081c44c800c1400840401040600000c0c81500c191244500c034600c051031072000d11f6482c0d640b8040c80901044070615000346082680c044031300003100804141441d59075880c43c042c2e2240507041035000440313010150740703c01c100c1800300910040361010044502c1c580010300c01140418040245400c400107030b42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 327318273 1250 327317023 327317041
    0x10e06151306150f17040201050702060a0521040b0f092d06091e01090c140607060504050606030d0203120103031b06020d0207020f121b030106030818090112031205 72
    0x9014040d0f0701c01c00007090741203030005050001c0a01c030300000241d9146045854150044805000d41c2d41a1116412300401c1d0303007084840d811640700c1c9810058148164916540d03158008e1003030195400110040341402d0801c81c410b4200202045c1e10f19a8180c2408042c440000c0d0300340c040300d00042111100e601011461400e114814100320f40c600c121030501c511501c0201e51684e031041c0400c0d0350808811451401c0e13007031f03034500700025041161848d810410288040b005112625006001600e400328903a42d610403034a059070191160b500c600e0401c03405081c00c00c08006c1c0094035000550a190040190800c01d100502005003040030520341c2c000d40c0030008114081a5030b00800642d2505003c1204100039081840e051b1301c00d02003146001000c0c1450004210f111103d000074042601c900042d81c0c0321a0f4444500715003540d43c036079000000c120040b02500c00c4803691035048440300308800400085a006801c0800816101e00c29000000e8000074819140b800201020400759500e03860 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 327319523 1250 327318273 327318281
    0x2313061a04090605060406080f0d0f031811010806010c02090103060e0111120603060c0a1b05030906040e0a0e070518041a1603060b04060c061505030a14010e061513 72
    0x301600581411600d80c104401500024400d50058904015155841000507501e4003c90180e81490704420303140303d601c510411800c02d40c1902d9080104080800e220310640000c0030201c103851b01c00c0f0722070380c826a969200191981000c02480d0900c19900380d60005038440c141880010162550b4458002d4060000e4012520440342c110701c4948444814031480c04500c2d00b01e40c2e01d07100e80180e200055034001e9070010b59224441e5503540c5c030421035007549044590720410400b43c41620040c000ca91403683d42200a001500802c40e60b075160f41407101c608410f40703021380744104058020210902031601e5444580c1c0a4486420102e40c03a070311541002200392400503810264000b0050410500d003214882a040755540d035502005040c0d910340791091540164090715002900d200d0600c4086440340d0420005032014600c6450b10b12340e01e0000a180000c1140b080f10603950300071414131801c40a201d1071a101c445400941400c4c0f4201001c02040103c46144520032014120540b000b01140d43c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 327320773 1250 327319523 327319571
    0x302040501051605011409211228020d0b030601090e0a12030b090f070806090108060c071406070e12030a0c1e060f1a010c0b13030203120a231306 64
    0x18681b440c500388043c5180d00c40c104010b483d031101c80009014807070001124100c0b00c11155950105c8029221040c05000c0315070410700c040d10740d4903105507542829aa903c000c0482c165007110016842e00c12106040c1049030583c00206080c0c50403110b4021100e0201d800d071811a40402c18003040c9142d87d00507002481c0c0d04146640007400c034002c101aa030030490000e40500c046817298440c3e40d403503504002c22901c0900840d0001d4125101180e000094200600b808a1044410821241150071010f28111003280e42500040006c10f0300115828a1641984060603200185107000c15110020380b030b505040000800540c40f94000004a00164981c074500c160300c00e00601164040c00002006081034540c0c11a0b000c0c010039103124a5030250001c3d1750030707660100d03501002e5603503004942d1903070842c04c900b9000d500041000290b082405900188030740c098400024040f11230b09210340d02c0303400380304650640910020500400200001194103669440140401c81d02281d50784a244441c200c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 327322023 1250 327320773 327320801
    0xc251401050409090506011a070c0501140c1501030b0105120606130e0a060b040509030a0e0d080408060c070c06030614150d0f0e010b0103060b07031b02100f080601030204050105160501 81
    0x70300c944c401c1007004181c0c00d041300d0010b041c560440700c11603447e41c0684207400c0000d0200c82010b40400095000d64020082c0b81c403840096400c0000900025083c40b0303001da48404040010b40050040004071b4480070701428082e130700c664140d011012140da0b42c580c00b030b0480740b140d200881409480c440982000c03210358042015640c100c7e82c10300e03003080600b0301c4d109003d219070305010001303111001c00010786601a41d540d40d80e000002034107040c0403015541c050195100c0710200000f14150741c0030442d090003403031900d0074a50780b281d49040c00c10786454513405c01020141013020800004d0284107070b00d40c0c1c0c0c10044529041001d01c101c00e254091090784407500b103503808c2031030140d1030203643d40c8803682c41035801c4024840b0803103000c01101211447c1c00754410119040c0310034004240b0450405880040c00c8480b14042c42158000034400c4560800e4000004c0c502e030302c0404800e03442112940c200c482800c0a5007400d0420300080c1490144204c0c01c6c82070443c0581810902009402054401c4248 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 327323273 1250 327322023 327322031
    0x20f0a1b030f121409150d0f02070b0108251403100c09080f010504020d03120605030304030f05011503210203040f03060b0a0803040501050f0d0b090c0c251401050409 73
    0x3d203405821004001c1d40e4070089a440d10030210b60100900407100421002018504442c1e006810090243c01c4805610885a91030404000030100b03840101030307541c0180e103160000d41c9400d50310381c07401c0c004001c490800040e00440601801e851040202a10481c46503100300c5401d00d400b0a04c1d0041e28901c0110f814280900480d04c00d801444207020b5645a00a80d400302e500204102d00341c440680e4000d400442c56010071010a104100f441d065951140c00400c9055a030400207140d5002604103030717191505400303400d0401500f4844d1411110b500940901007514549070240e0120714000440120005214640b04040c403d00c11600070b0001003000442568407820b01400900e226905503000303454070903022032200710010030b40d0211039059585910307002040c40c175000140c21429000641c0c50b02c0306003440d01c50b90b80706070581c80703003c084201a46691140c94860715091a000c000c03c0d00c2e84d00c003040030503192034980c080700a80311401c04200101c01488012151841668446c00449140c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 327324523 1250 327323273 327323303
    0x3030b0105091e0f04051603020306011b05102301030809010e0d0b0f0714040b1803060a09061a0906040b180915060616030f021006080102030412020f0a1b03 69
    0x50f5110718000c0340300341c4000320001c03068401e00040710010f84000c505110040310b40d58110f40700350011640540103160019091071030070188840404942811110385d003290303c4001c0122658450300d02c007100c0d0300800c070920b502000885c5003070401c10300014046600003c0c000c05503900070720109222400140070003c154500303007401801040243c40a2030100000c01c0464200307486001c40004541c24403020701e14092030710500040313952200301030041c00901103000d80400d650034040356100e40341c451070125646510303140590450f804002c500102200030b8202c10700588034410b00355482207081d0340c0081c005118100242031680da03e031490118039000c2e13041294401010410400020782d84902031078a03200c140410600b4010a180c40031310b007000da19000003080c402e9107520b03040071050042d52a80c9840035080c0e02940e4940e003206800f40c0d0000b06120801c245032480d1310b160a91440030b480e00d40e80110300c0720707220881048040c0540d5004002c2c092200c910310b041600440d80003c148106881d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 327325773 1250 327324523 327324559
    0xd060b0a080604060b01020a2d170304050106080304140111071502160906030209040803150306100303090b0306061b030d05161106010303230c19170906030403030b010509 75
    0x41c044070300b26401800d05c9403503409940001a02e10703040d91f20206040400341a864400070b038036800c0c00030464004541c144034000c10b00d0300c540014101c201c0c1c26a1a5a841c06081407800e50b11583d08c0000c40e94070800080040940c40c000481074103109292803c403900c66440031500c1c0c4007084c1c0100311a510a00d031104420fa4001403102e0700c0488076000000e07516668204041210000d10004c0d4000082500050010703111000a6074041740d001040700e01e02121001080c03a00400f10b802400030b02e0b0342c1c5000c1c0240354200c01c00000405140414a2843c540500412280d0103a008104240c001d001421045000144290381d66418040760400c10761501c0d00c0851020b103580700c040c101050002985c01000d82003c00c0c414144c0b40c1544030682640c42912984a09038064034102040040910030b0708014903041c4440301c220350744803042e56000d600c107003440715142d1991011444d100700200004d00c00c50703d4100aa9a000343c1604000451014a00c011f844920407444095844245c41084007182c007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 327327023 1250 327325773 327325783
    0x1c15020d090501150f0b03070905040203130507030c0501030f020c0a030309020a091103010906080123070207030503030108070f050904030f050a030204050607150c0c02031c05071203060503010c0c0807020d060b0a08 94
    0x601c505c1520060259981c0440c03170b183c40181c03403035000181e201a0601540c10641c0045800405064a17141c50281d01d03100d140c01d042c801e8008031078007804141d0070001580d06000d058101c40801204500e000003c4840c03032760382d500e406001400d05071910022811743d40e580762000003d01441c0c006200c0c2d00900103180803654030134000d540c02341e8a05440410802070521562460200d0503852150b0500550062100400300034408000c512403030074044006841400a1802450320a000702446030804460303214245041d0821806206201c0c2000301096001c0a1041c403c880350134001ea840160400840291146412450700b1210000d0b40008000e00c0d02e011a480000300c4008001d0f243c01c5d420225242c00000c3c901950527440715001c050040d600180001c400605420002c0c640422a95540034150a1880400c04030355204000c211505003030040042c4030a551800c040910b140c0d80c0c0380c00050044100190180c2c112590040c2000610340c8131600e091401010061226a6050b0169440b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 327328273 1250 327327023 327327029
    0x1a0d03051209070810020f1c06080a060e0f0606010c08180a080d030b06160b190c110607020303040206070b07121806111e181e1c15020d09050115 64
    0x54445c04030f402d0b03410b01a07442652802e00d800f1412615100c0c280048200c1a41c3c0101c109004550b20140040d113007c040050458292040d00c010070142c84045009003401e080e2542c1d110329030800d10400030103a0740120400ca080b54040c0c05a5121010b0340c0002112655094286030010f40300c01c4042908c00700041c000c000300c0c0065905000108048040c802c1500810650b00011a0340801c12000182d17200515540400c100d03c906280300501c0003407000355294a02840c011030384d0201c5c01d590780d070002c0c008540e02032481e00056165040503400f0410310312031028060802d0f00c04002243d62244503d80368114075100d6102071084802d03900340800e0000b554101116118580108180c00085203416182d548080340c018061050305a1544800c03603114010f5500107091249501813565901000c00400c041260034000202c560305050000c507102e000301441c1038000b00741c0c0d440c0c0041d14005400f40300f5241c5000252311055102d1020001e0903240c04020055401d10380398034040006a10f540c2c0803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 327329523 1250 327328273 327328289
    0x10c061b050c1014070c05010b0604240f05030f0624041401090807060f0512010e040c061d0114120c031609030b060415051c030809011a0d0305120907 66
    0x1443c418034032a9000c41c0e6501201804d00200b0340000340c9038500401e456004540210000701d82000c0f5034001440f40d52140d04074040f200903948949040400b03a002c5c01c4030400c002e0034895041600003001600501008101008410216000550949854510d904001006114110043d135500403131005500f15025404000700e41a00c8503086600c160a42022036000034040c04030241441c0d001c840900d50b2442c803034240641048800071481c401d500302e900a05044807a113800303003454584401100350a501150401c00841030107208104458900b041070142420003c240d40c42910301366200d8016807a1038108248400f0400154040060045101300e0b080344200541d150724400603101d01e005800064204060480011501c1c20180c0c032111070311500d0766042440765901d00c0000c2045825000440c10007504081c4d02007015004203505402070341040003480304081039501d6415031400100410720549416455a06050060044441100840310140302034508043c1103a80c80d00e81d8411640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 327330773 1250 327329523 327329533
    0x30305090105090c09060909070b040906060e01082205070801090804030506060d030807120623130e0d030b060d02040608070909050103080a0809070e1009050109020c060105010c061b050c 82
    0x3c6610085503004000b0380080c011251511940309025800000070a041d015218030400443c1d103048441c00307000100001800490094281140200345483d10003920381848030b0f003414800b41101030501c0b441f1200c1c59071460620503c42d414900d1400c50395520290ad554600750340b000c1800000ca0050040e00d0103201119070b99281c11041c031100e0120341a001e40080e901c1d10210300524450003811401101000d03000c10096250024010f0f402241c0c0625600700004034a40012801c01a504032401d1100da802001a041c41d014202d89408001071500f04059841c1071f249020743c2c494096410390100c042c030441d00d90ba212500504494402c0e40e041d0702041d03807030b100010104d54a0003964166648845402d050040d12201561039450152803480c0d1401404d0010640c0f030307015100144103820640341c60140340c0c544001c2d98212030068000c1d50100b40104075004e501d06c8001110342c1161001c0ca07214440c0c1580f41441c4000300064040080516003c200d0003040503030003009441c100c0c4000e42664 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 327332023 1250 327330773 327330781
    0x20f03071517090a02030d0807030b09070f030b01020106030c0b0a021e1e03030c0711120a151a030312041410020a0318050c242802071202060313050307030305090105 73
    0xf640e60201110020740c194070840c1064491440ba0351041e400c4010b038240840c000343c402b400101c62a10072a0490000755807140190070307a580c140a400000d010030b000070051300c2d00f140c99050041c40039014001c0303240000070f80031a145200300940d420b9485091040140350544488650711aa020415990340803100010b0502e00040481240e005070040c810f03441c905000ca40d21508000d84401243d5805281030450404020041c00110391f2984607000302d4241d8500b014406040390800000d0307042245400c2c0c00300c8a036403400000c9403040c0381480308007001503a5502d44210010b060b201d0a20460041078115039061030140c0140202d20801d0314180b2590907010201040f9500c1030034007400650020042c02142d0072f01c41120180c2c103003104442c40c5034519034804c010595002d400607000324003092001200e212000405000280d14600c090300180b03142004c1c1c850001e5480d10040d200d4031002001c20005400900e90110540d0f105094035124034103400c019004100444951465500301000a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 327333273 1250 327332023 327332041
    0x405090a020c060c0301120f020609040e0c0405070e0901030b0901091401090303050606071104320108070b0c1c020a0209011d010503070b1b0304031b060f050a0c020f03071517 77
    0x20705e040c7d500d62441d003003070f421403134968070002c1c0120801640c000001700444082a100c60040b40e10741e10082d002070260170400707414842210300041020040040070222101d072659132500060450390070642d2000580c483c45030260040200c840001c024402d01d51120314028819004540883d000ea2404c0205507603503402d00c00079119810004240960f01c409000c900c1c13600e41d01584a09003555022811240d9907a028a98034200c0083d03030f050b10900a0040010070300030032004000d40500b039030071b50030040d241e020545d44455a03007100c04100d4018040e145c8846c401c0007225815a0000d01400302960350790301c030803103015003000c004c411000790700001300d054100025000308665206805d240f400d8100761202600c0c001801340f41d100b5000801001000c916156150b00d180311500c03a800c4500ea140900c05002e00d403c100e20403040c404240440c0040300c0c0c001800d0102550141c5d66804566201e000290034100d194211144502d40c08070810466544400712107502c059006200714203403100700710 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 327334523 1250 327333273 327333277
    0x801030c080613290c040e010801090c05101803060f050601032016050f0309030d030b010804020621090304050a0b121f0f0b090a1508041202030405090a020c060c 71
    0x7071003480f2050740d00440015001d00d4005515020182c0401100750202e030401c480c680056a0320302030104040b6040c070141c419034440900610031000200030003070241c0d459409403e6103214080c4140340c84183c040d162405070500b00c08100900c0003925005481c0c3c50070708024021a4004901b06180000042c803d501134840d0303040a41031b1450185400d818174406c0d200703e80c4500900b040e400820a0410300280c010844c40e03000b010880c0180d40c8035640c150a061502a00c9500401098146066000c7c00d903004046a5040f98041d01d050b5a20310706080061b4240d103021280414408a1908111b566a0017002800c10349600b100e0f00ca02269560502107101c1c050030345c480740381c503104d00003145070841e414848103c100100041042400c0d5682400a000010380c1d01c042d00c40c1d500080c0300d804034540034403480082c10125008900344c1d0807030100101b14000091006081100c580c1e415a144ad000704150307801040d00400d5583d0b1480c0c03c1c0544e00294001107a44080c0d0f116000114121400448c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 327335773 1250 327334523 327334531
    0xc010f0b01051204112106090d05031302010f0311070311070b0414040903031b0f030b0402030c0d051807030318090c0c17090a060e090703020316030e120a0801030c0806 74
    0x5255a0903141c80e143c4440062285c10f001c0c0c0d101c1d0a00f07040100a0607081c245069014541000d000076141107403001d0b041088000d00c00c03040210030400c005042d0203600e0500303811502840c20446099510005400a000100301d406004801150034001c05602c8915001104414001d82d04240da403148075030700b50300444c015140b00c5410710030032013003508180d400080c1a50003445c000c0b80c0034952030384007001802800c1e141c40000d01810401c1180c2c9415004a0384e8060041d107046103980703007400d0708102c140100403501908944840205101d048a000c0c10500500e0420650701c56959034900a4030007400c0900d000c1c190000c2050005818031140301e0042d9106a544414104207159070f6200e120b000c1250000012142c1030001000c0c0c4e40711803001c440984030a80314140501e1220080000180000b030460b010540104100070042c040c2040b0040c003202c160401180c40301020f681b40c0e05241425909010381030f000300304110406c7d8000007450480340036044040000d07869032492621807400b11 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 327337023 1250 327335773 327335797
    0x90a1707090902150a180b0a0c0602182112282309011b03021002130302091f0609030506011701020d050c09040b03010911041805030c010f0b0105 64
    0x48810032881c0c0890b08a001c880b88010488000290945540c107025080140c101d400922081c254141183d1303a488000050107800c10301d1030800c00c03035000080c600740303807401e005005a402042241e061710070380801c0b01001d0070050005040101541c49040311240303a402c029510305c40c4041d82d420304012001190350301020742c85144030180b41c520442400c00010744040c010030211014040041c440c2829020705000ca6a071101e64803042c00300010200c0d0315001c0904070030716803900725000198001406040c038410600000d41c52344516100039131b900f03c450f480650000520030070044280f141c0c0b040060706140300322029400b9500d510381100c0d1100c05000003030807640b00703100600c05003526900c10506800340e04009468110080b9241c41560420740d901141168082000401458603014041048405070001c00c01951a9142c544030350300000002400b40d0303034804100c0300b03000016107400300b203030b0b00403089990b100e1500303e02c18001c1c10301a500402c41480c00b5007160140d03200f5411500b0003c400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 327338129 1106 327337023 327337033
    0x21c03031b05030709061d040203010801060e130b0708040f051b040e0f1c02070e040f200603041b0f060305040b1005060414060d02040b090a17 63
    0x204a0070602c0400d20401088170350189083c411038210746401004120701e52996052503460ba601a504140008008641c03040150045000c603484054460150354441000c0e02608040c840d00a100e08401070110b4401803240b100290400d009004800c103001c5143d54003858001d00c0c3d1040780e44221401d0300032015243c07134842c2c6540d0703100d000040c042c40070b040d083e41911500c40240b14100d280ca0304010900d00c600c2081140060510404501c8160074281000b08001541c40b5084a07040108a00200c1c010030103040210400d03c040c00302400c546031a641c5480700881940d4040e81204100700009452015000313030340042429840001d042e0619092042d80160000e1140c091421000000c2141d5102c1ba8115030803079000d4140d000e420342020001130b04d1031164054500d44140080f5010513058807841c01081d0120080b110310882d00c1c0e5800305030402c0d40c1c81e8180c0c01c2840d006 = true := by decide +kernel

theorem cover : BRFrame.Cov 327158273 327338129 := by
  have h0 := BRFrame.cov_init 327158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 327158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 327158273 ≤ n) (h2 : n < 327338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
