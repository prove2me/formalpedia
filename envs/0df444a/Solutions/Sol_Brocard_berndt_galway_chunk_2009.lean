-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:26:16.390821+00:00
-- url     : https://prove2.me/submissions/f067196c-5003-43ee-8ea0-745c02af4d5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 361151079 ≤ n < 361330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 361152329 1250 361151079 361151081
    0xa020102060c0702090f1305012406110604060e0f06150f0d0b0105010e19090221010308121314060a0507020d141e0a030501031502040602100e0f031606 67
    0x1d0001d00e444006100500050f180c0001c2c1c55006441400c08501070341e10b4070040c7c1d070a122440d038090619070805070402e801c5194502c1c848008a10340c02903c081d03540318a4162400301140203544020b40c460030001d800301d10701c0c0e44040c0007440604145d814402c0c414130014904036054448002c0d5510004840000f85040d41c00ba9552610076540c4200100300c649030400c90200c140b040c14140050a07034060034903520044440060f500b030b08015016162140d07210002500b120020003034034006008402080c00d09401c80e40c0c1240d6111454510707058140d006e07040d64900251540046070243d681b60700004801a03914420644004024245842d064170140280c54001e0704841c10b541140214013402a0f0085018008040e02c994403640c7c0c80c0d405001640301c080d5150b22400d11100410300d00d00c030300e9040c0c0243d412203008000303030b412107a0249903010072071040c0e204100159201d000b10188480c41a04020352081d2140156026102c82803d0982140d1221005500c41402d40751548208022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 361153579 1250 361152329 361152331
    0x15060409051509060108060d0302070801060b0d0b030c0d060f02130b12070e0a17030c0312010f05040b090118060f0603020703110118170d0906021c1103060d02030304050607050a02010206 82
    0x4a66000311818041300107401004c02908880c06030055120303060505001300050740092241900800c01d40355078481e40e442c0c0c0d81011001250035418004030902e2803400183d0b030910800010303c03040c82200f031951410000d1240c00480c000c42d5809006948401c7c2e0350002d13060041c10010035141e076480105116480000000340b60500303102110b00b581415455030070740d800c01da8074600c0c0321050300002104928510301422850001c03d1000003034440003200400003284c100d603c00007842c241c00e91100c0400007520b10203180f1541085001d40100070600c2d111018041000700c44400203041d0340c852920030100c90312a089040030a40015400042640c00302540c00c040b658000204040100a145408034030380e650f8000c1c1540040400d80381d1900c10f8071003100c01d1002e20090410580e9114500304000c1d401403040614010720301610404058918050310004140500340645907540364000c0000e0100b5481c000d80c3c0600c8140404600d03525020001c0222601034401001d802c081440024a4820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 361154829 1250 361153579 361153621
    0x12030405010c110304260319140a080f04030c0204090c05130902100e01182402010507021e0c13060504050c16060518031303061d070b031506040905 65
    0xb401e258000c3c10f18040706881c1540c82072184024294030588603004a000d0661006003140000a89400844c0e466000d60300310840c03e483e00b04081031041e0480c03500380074040246e00807481d007038000340f03210320303c5c102e000d520078442d00f0440c400f40c6441c0c021608841b1041c004564021205000340401e2a04860140c0780548105040c44500416404164240306949596080c4170502e500f9242a80c00b4292603022026070f10301c07260b08943c0c1d800c0c61041155080b022202075400c084103121a091040c0030751031060313245800030144071503003200080c26000e10b25a0240c0b00e0091a11110aa96800300c80504e000740800010231040d08050030081150300107003072040080d004004411500c074a21043c50742060708280f001403103a4840744078a103208084000c031091400b0000d000c2d20440030305c07054107040d24005c0d4820000c2c90002611f101e42d5100b143c400c90130a900c840340c1000340e50107010007580d120079089001203220204c50003041894010fa00311604090300c0303208200e2210300900341a80003407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 361156079 1250 361154829 361154837
    0x604060b180907141012020717070b071b0b0f06130606030603110d0f080c0c0d06020d060e01271104330504051c02121b09012d030512030405010c 64
    0x10f41c1c2900542854000c00c880300301150003003040014003101d4002714044100540240341d0700c00e0309140901001204451340e1020503003040d145580c1c0b00400e00c00f00700711584801c040300c250b2120030a140840c04000c04244e440342c0940344c61003030201b0760300031507004180c40d0700c6c0442d4041c214540b241c0c0c0580406100b45c0100f07041c04625000c2181c0c4034040240640005034160b4a005461416080200c0c1c00c2190303400c162800608010031000354010800d0316441601040201d1f01d0782000000000300b0b210304c100380d80c2e0000c018242d90104050850342c40c0004040054070681c418086040741d042503101b00018420810540344d01c64213821030990045440b104400000c0041a002c3c180780618000e041c0146814005642c044841210205201d900100b2603c1d410711a05146943c40c0c1482c45081c00c0d1642041d070303c90841c01d044110074181c2e008400452120f03607080070000807803560003091070308800c5002c40000100340240f040e040008194458581c2e60720301800c02d1030a40300d8040d42c0c50100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 361157329 1250 361156079 361156099
    0x10605030606042310051906111b01110309040614010f02010b030316020f03010603080c3009180906041a070c110301060302040623030d020604060b18090714 69
    0x8048030501d070711301113903c000450700c0c03d44450032144420740d0650446a040303002d118241001504003100b202c1290307441d0ba0f90808011072020200e450780d101c017078070007031101741c8180c100c0e819802a40444040840c080443c1d04040d4410005001d0b00e400e50300c8040c200c41800128061540d00c001069003d480d0b50000313128044010340031964a10410582254070aa0b10148000315aa113124040d00c1c400010000e201d440c2d140c0c01c2002e6540d1041c8208600c0d8816103121002c401c020740c03e80050048a0700c0882d01d441e1160340300c58900d030300141c54994049a012803039400c5c0002c48218500681200c0024045032800d46004201c005603181040503040854040203c1e1552121035400704c981d0000b01d4041410b24070f00402e004d01100c0d00000c4d44103041c100007043c44003c0605624800802041c0340100f20428802c0c55110124040241c005800880c002401700c1d071a43c101c03440119000d0003039150540b1900566404a000b0758550301c507900500000c07c2101900c0c07007400d05607202203c1c0b03140c107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 361158579 1250 361157329 361157351
    0x60e0c060c0703022e0f0f09050a0512240f010e010e0a0c03291003020a081f0317070c080303071215051804030201060e01030c03230f01060503060604 66
    0x42c070030080c44000e00c0307510400305030b5810700710a54001101140034648110b01c812410f00141c4000020b0640100140b0512003443c8083d2040c18000200e41d4054100c5464078140014054419042c41c0900c4607407240e900b1a9020814030504050703401061082c40300d1038240142080d03d821b00680c0b09603250009000188152001c0c111982c0e0060f69031070000444041c4c40b0020783c0545220700e80b02c0a181120344518807c415585901007120008031404c05244600100a404a0144242c0d03500011018000580340310000c0c41817074020100e1000c4550310036a80d60b01c3c5031a05000340d540042c444c1010070002c0c100a10043d580028084081c044d50a40c0b411000090951980032003d0303003451b444403201c0c580c513901c0b0b1405602034000a00085451641d01440802c000000c1d40c0c00c800541c601400042c11001d28601d59058991165403a0441451503c4c0e1110303203d42c032014124880744040041198080400c108420031036002c001046280c5000101810a0001403030980128209255182 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 361159829 1250 361158579 361158583
    0x30906030f06031703100e090c131404170d09080702030d021b0f0103090f0305040f060906120b03030909040606090b060f030711070306060e0f250f030e030403060e0c060c 75
    0x2998200c2200541d103d1b52000010207014038558442c41d81c4800a03001d110030454003054944103807406a0700c030000128040010000c50380070080780740303e00c0c1804001c5400965180c0804420000c1031861504106410b404101200c082410031100764000090b844218281840103048000c0c00e40083c1208024164000440d0742006240f503100b500400001c0c000d42c0e01a5001817810303034100e0301c03510170b0300b05078900505142c0c4640103001c4000018100010794512a09070305065544594907c1c04003c01b004a290181c542c0214440c2d241c00180161900c644542d501588128043c540110743c1c907151031021400c407100a507450340900d908128012580c000711013203a42100716841c040c41c0e0040708040321030038620250401000541424000240c41c021441200e01403810001c02180c140c503003d64424503484800d03c184039188045400c0f02e03a00d40107007000c0c00c1c1505241000703d411003031740a491382164843c0e082110529a40e2a00c09510001001100f1940307030242c40315450800e002a04613 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 361161079 1250 361159829 361159853
    0x11090901050f0604080a081201050a1805071106160f0e0a0b09010306180222050d1401020409060803041d060d0b040215030103030e010e150f0c0a020607030906030f0603 74
    0x1401514075040ba01d442c2c0e118141224020041d9006a0f1200c201c81c0c40c04000729801044011000b0441c040041440e241ca20800c200b11107945018040d83c45003480c80d0405004020b0074407060001c0c05a0442030b105041c0000b602c00c80503410301012080030024080d0008905003120000c000450460300090b4039104011400e60f0083c00c5031030b0b100c9201c5d8004030058811900141032120060540300c044010700d4025003092804209820500344006400b00685003152051591011041c2d034081b0102e0385c121001d1100c0d0804130005440d00d41c90700c850600f65281640a8602035000090800104024a90440040c0b480301d0320703509142050400039000200c2e8080c0a4080e44600d4085401c550324281c000802900c2c041c01c158403581d60707090140468030640e0400740803942d4068408128507054825951341444545810b00300401e1905015031034000b2230b400d420b01e100b20000440540d907910003034014180302c1d99500001606100c40207007a100300c0c442052105082c1001440001e060071001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 361162329 1250 361161079 361161089
    0x709060e010516060c050309010b0402121f0b0c1e0d0e010f091a040303030509060c16081b0705120a02060306040c210e280f231011090901 61
    0x200d900c03242641d68894001180c0c0d04010200342c40c12208105d240c1d00940554425400c940c001c1100000c85c80510040e48a820300c0300ca598008800014842400c01c02035600b201050381c2249905903e546403158a0740c0146440e055587c40356400c4904200210383e0b9840c601444005050341400320310b030140c114030000c90503505100a00b51070110862086a01100901540c42c041183c440c07090715504580e40103002c103400190420380000c5404900084060107192100d05062130700d100b05031440e0381d03402580011a1038600030840940e00c00400c400441401182c100900a554944000c004940041420200300b54100c140c941000d41d071210700352503101074151404502c0390f0b14408c0440e107080405a695040c031010308152110340e009070f0301200300140030a04035501d402d01200b903100c802140c0240010511844030490300005c80d080d000b6800e5a103c0c040d0f403c40e07001700c07044410380910500b4810607140e12001c00054003500354024a00d0045038007010314a004982004203980c04014020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 361163579 1250 361162329 361162337
    0x6050a0e0c07051c0c02040c020d0c20090907090506030a0c0306020d0b040e07050102100204241e020604030206060d03020d0c0c0801090302030418020301080714180c0a03050709060e01 81
    0x8800303008080c01411000c0c107001514a0032045014405000044d041740141d00951030705184054a5000003142c5100d034019846058945c5100e50345c40f0120440e8124014100c3c5002805485641310080d0f000e0245039040082d12529082628403412030382c00500f13062003a40140507002c0030984002804c41620b801110150365040039541060280a00664a5070001c0c50107504148400001c5406000d4035001d90a480031750039441024010b9018030b001d00350403168007800c0c0202050412008014814280c1041c0c10b601e01d105500c0411050344861200c0540c00c00320401040540c10303c0400c0c1d100e0300844559581c00d0194400135030303554003055090148040706000009000f500f1142d8002060840c0080c044603000386802922500305202d0070005c20b14802860144209900940e0b050b9144000205030052a01c04152503500b100c00f8610340100f007042c1c1401c03000c038241d0311444c403406d2084440f90b510b24080300010101d0b41c2c000c1100d010880000420300c201c4d94440200d171500d0500b407070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 361164829 1250 361163579 361163587
    0x1020c061602040603140105150103060b09010e0a0b030108160509240a0f09150b120f0a02090303070303090201080603010501290c03130305070608010e01050405150901061206050a0e0c 81
    0x2003c01c0042c5415080070302591085101c41c0d0000c041500998483d1611107110600c0c50f44000041d03042c2d489900904040000911000e900c4d94468110f001030010021311031120103913540c480006591003a080700e440f542010580010300901ea503200d900601050714800c09130300d005402c82c0e400305001414049400d850083e9a002d070781c2c0d81030384080078008151600b0400b5030780d40704580042090b82c68024442d111942d00290154650041d82c10946540c030660381d40365104100700f90790410080c00000403d0b0309000408080d00d0800c040c001035446a14000f420301400e00001d00940f600030080380c440e2303042070018000850301180c200d008555004107980109410740c80d49200380145000f95410f84004500d585090b01501c886a080724007075020740d40101c0d1110021103c001003409000410210300c0c2c0100305504080c0c2c80290701900c104c602d410078a8001c000500c5225007a8000800034089000d0300600320f82511403c001800b0450389215998500082c0184621009000034603011000ca = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 361166079 1250 361164829 361164833
    0x81e0702010e21010f0e3003060321070201032f091201020d050402150703020c0d0602090306041b12030e100e0a0e0403091406071202010209030304170c01020c0616 72
    0x5944040200e009022501c03444240200a005c00e0880558520456840750004446001c2d1f010f4000181507111905010001c08910580d1016141ca50148070f1006021a142c1ca80052011804200340c070035903461000c4d0000500340d80001c20786900700444000c0c282d0300c0346051200f41d419900b480300c006444010746400500006a2000482403030750000403103441f0101c1130380c4081d124500c211014004c20740203024031700352030007100304c0200903a009030012009171800e0340307a0044181c40b9040261911541c14003280c10600c0c1603030b0484400c00c016801d4513343d41511540c030301900c541901030034030200689000380f00d92000d58805000301d00800154000c588221500c8000b1200900240099990f994495514a40440301139000a04003403022640511050392031290306001400c450404440752220a000040907179058207641d4200011065500c00744003403c001d0124151040c240400640c54038104110a003049045402504e034a0310dc5603100b10680b00d1403241c14210752550b030124 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 361167329 1250 361166079 361166119
    0x11090a0203040506160f11011112060310050402010c030311040f0e0631180b07081b0a2001090c090606180614031b07060203091b0307050d06110304081e0702010e 71
    0xb80040444ca09d0000b01e44600241c04540f503405960150200d4100003aa403a02004450742954004c1c0001c90421900010038480e802012400360031360741c290b00d0203566080064000e12903130310005403441e6410400482c0e28001044011900e400c16548070303189404403281c6039083c80090070f02200c070ba4890301445201c0c50740c0e41070b80045921003d21601420201c0c4040e049480c02c84818201c1101c500c83d400c15400c03240c040d200c030107100e6111170300e600c0015007419501182d5900c209200f9982d501000001c07903090f0001e44001e120310f03040026043c1c00c0c404010510a41c9200b8031115031a200b00803c22958000c2450001402c10b040d0a516034071105260024074a518001c51540f03200820144107100c0e05074011800362003c07400f200c1619540e802002c03180200049007551641045c041000142450a90b0701c180501c280c10010b6a64810130240640360001e40d0256070003080410b04000703d0780303201030342e00c9151009010310f030034051141d000a01c040d00c0900414012140c4400c494900504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 361168579 1250 361167329 361167341
    0x3011707150201020c1207020a0e192d05040b0f0603121c061e15021510050901080f03040303390c12050a02090411090a0203040506160f1101 62
    0x10000c41d074040c40344a00720090107900855500d0300c080c020603000c2c18540c0c440038100c51100c1d40c047c0502240529080341d040e000800202804544100241d560803040e0007407280e40859441c885c1c00030050341164820101d507100000d51071903520300d080300b40700114601061565000c840700341040300d80c1d50756038042818000604408c40c0720780000f08041800000b01807000e112031106401c2048155aa00704480c0b8007800810aaa121001c1d8541403100c01c0b0508400e25007840d080c011911050000003101240e92000c0703071140103002102c1c5042c0305600e0820300b0a030040402e2401881031100d0091900d0322131286206c01002c1c03200c3c128403c040c800881c0d190302401e450091011212809038010301d00d20b1503a40400300c030a140d58410208060410030040300d4030f103801000421300000c09a0a024545401800c2611169001d2a00903981d60740d1048061040e51710610158581c141881c0851800310007801424540b0b21440b5280c10301d55000036501404e010514040704074441c41d805503401000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 361169829 1250 361168579 361168589
    0xa12170103060614060f070605060a0f0906051305012103020120030412020d020a0807060e0d050c150412050a0e04050108030a080105040911132d050f040803011707 72
    0x10600000305000c2c59510034812100301c03081800a003040c3c0c2003005028850304010700d014020030320540300822040e88c8841d6104601501c08034004d0f880324007114405034a40d1281c1085519039506020030700b0a50001d40a0303001501c0b090145504000000c0354404000c002c3d00d074109024103010080c5407007504460303240c800d800241a801075070038016800960041760251001002502500200c51000a105c1c0680c41c040e8042d08044009503a0080154410341c0140d442d15229070b200d04181400b406101030340da90b59201c0b96030302d82c00c0b1042c442c1010114100b0030901c5400d80201b2000c02c44039007043d11070f2802854001d99803e0015006d84980300da81d150a60001c2c6060008107600c84000010301901e0b045456000c05607a07141e080100303488022900a0040e0400d05071a100c40c148400c0c00640443c409802041001d4510741da400c202d040c0541e140d5844000042142186046100300c0f9004181c0d991180d1292030030352907078007840c03006208500c2494914824900d505d81d00703000801c0900 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 361171079 1250 361169829 361169867
    0x308150618031c0206070c080c07121403070308011a130b0405030f060c0702010c2906101106040327180c051e0a090315051008010c020a12 61
    0x5000408541e180d018409031402445651140c054201c400d15002000048a07402402c0507079451504442e0310240701c1d000c6650150038041060041001d00c141000b40140726030168079110541001d10407002104402d200d150420041c480220f5404007005056070416034070505214040c02850382c09201c3c1e100c001840003400100803c640000300700400c101c0d1411000c90303142c0700d2401c0307103103448000607201c511884a08200c00c800550207420740d88a2903008a003828480c1540010000e014039105800d080c0c010030b40c600b0003620340b421100e0880b08541918280488000d41c0402c15618171010344050203024003551081c007805505649004130003003041c51950200d030340b186d16880c10805020301039103e60404035410300c91881a42961100c00680380305e04049030400318034180d558070150200c000c200041e076010010071080a480c60003600c0000d0006203078a0400189920b203102900710009503410600106161940090041c0031a07400a00c4421041d2500c0001d031021898080400c4070301c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 361172329 1250 361171079 361171087
    0x11062403031c0f0216140102070c080d180e0a0f020c0f060405100509060106050a03060b030c1306020601180203090316030c0b07050a050a112e06090603050a03081506 73
    0x603107040091044200340c0440b003484141c10743c0208000303130302075012540130200d03800590318045119506004206913005000500c3c284180d00e408500080e00c1e0824500341d81700905043c426540b01000303540401082c03c0c803070541420924064002200600b402468946401d00030045034103540c12900781078001000c0713500c2b400c0304040c2c00c0d4840b2001c88065a007030164000c1e088440c0203c0c040c0358070031003089002c0d02c803603030814205070f801d900700480403800c140e681c040208480f01e001c40114000c411000705151a40f8000e24201034020301900134a085410403070041020b800814807080801c4442c220142c0c49603503d06490740317076008140c45101c588480e22030f242c007850f411003420012580517251006c80744d40c60700f2043d10a40705141648000441c100003802059126118001801d1918401e48191018002c4500f8801d031443c00500300c00b10700702040581c10310307461086a000b8100b18805210303080c034685800307071504010310001d014411860000b0302d8030503040d20300707000f00701c001403a20340c40f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 361173579 1250 361172329 361172347
    0x910050a090b09070803040b07060e0111030f1602030d180605010626040201020606060304020d05150a0c02071406160b01080c011202031006030e030409061401080105011106240303 79
    0x54003581c0402e5804a2030038011511500010809800b40c80320a80194035041c03400b40c10b80007507807005030113440c1240d990380c609015200a015088420103422040354480c18044100c500d515000350811000d24803545403c100301d0340100540c1c2d07000e504041300240c104e103030a445a029180c5041d0089c03002d4034040c004581c040d0407071088040b0300b6035410310742c546000004951014003410344020740583e2100c80000c000f4038124000b140d00502c05041030f0612440740c0c2d580c42c5000801c0e0310350340b440c070f0000081110b503010034401c0000d03100042c801052214a0311202c40c2402040102c620b0140301c0001e50801d4004103914056820703688030000b00142c0d03a5401c291921520194403840c0000d0810030340c00614400c900a890060307900a030320111040c6060b10607002881d0ba88484003180c04217000c0015039415030300ca00e40c01804880011314a10f0443c030001031912005800803418004401e01e90080e03414005900c580c003800c0110213000c02004150300c080c0f5007500080a903458400050300b440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 361174829 1250 361173579 361173581
    0x30c0f030a0c030e03030415050a061805180712080a1b050c040b0d020f041e020c1b06040803030114010905130e2a0405150405100303020f070b0d02030910050a 70
    0x4030208941e6400c0140c004100790417a1a480180d03005081089080c1c2c8080031005141c0c0600e1700038080c000d000420030760720345410006030301404550800b16034031001c1003007400055a00d0f0b0a10601c2d1006030001c1c908125100303c0e001b04003240605091000324455007240e000740561140d1100b0070303101200600f00d0f4580140e032041e4400c00240298280b01c0800e05904120100b005160b42c0100100c0503500d051090000800c01d00b00030000e01d98001c3c140140d44002ca02c0104104005030b80031740718007000504803c0c04011510350039030241008100400c11044080103990541d030000700b01075250340500700121060031180d08002e502c5540780801103290b030000d03407000d4140c015002c260b540c2051000c1e042d0728880121040340714400001c0705201c5c55441c10758880d41d8007141f00c4480185202456001c10120390045852115410041800740145134042151034130020001004180b003034140041400e2a0103400382901c5003503004804a00e60070400c1c0146100b00c04d095030100564980700c08118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 361176079 1250 361174829 361174841
    0x110706141b030c03160201060b0f0403020f060403050c06070c0503030f030108101a010c02150d141b0703080405030702100234030b0c13030501140601050a09030206030c0f030a 77
    0x884918207581404210074a2105481c420101c06103203505651396880311000e0000b040c0c00d4082103542e191300101e004420071002c0c1c0042c200400320b00d9280c0d801c500c1804080180542664850794003804100001400011098411074081d41c916407140320701c1ca8849441ca010760040d40c3d145c0004034515203103c090002a60488103c00300320f840c4002c0d020b1100040f43e484c0214882010306110003c0c09650007081c440340503901c098170303018140d100c00340401155004014591107442c0c558415a41c4041c100e20a0707608152a98400b50384d107444c00054030018802c004006081c0500300c400141030050034011b91b04201c0d0007421051508272403400094440044003020b60b4040d0300350f60920350303c00d0161820b02000400e98814800e46007580c0354028000e0004041500c0c40704200400480c072004411a0707801944034000204510340311201c010b00d61780f001032400c4d0420005015004050764800c0290088139015580540e80f615000c032481400c2c8902049071680000000a101e40741c44030350310070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 361177329 1250 361176079 361176091
    0xd02071a07020a06180c0b0307181202010f0f12050402010509030118060515061b21091003050c090907110f1509070f18140703091a010602030d11070614 67
    0x1c00c021a880005c00c3c207001e42d00e000c0500142c0d4503d50603c03404146c03100454210001c0e003410103046103c918601c6220a943d08441240e044124500c2c0440d40c022424802d07030f071101c1c03c19000100c2c0c03a000040143c030503d40400c4819440b48082029640100300f11918024040d000380200c0000388800c0382070318030746038084814a2800c1e0000744007100c010303d41c0c0030002000300b015241a0030232500c02080500f001c403c41160294541450382c010f0920f041810880703842c84216101d126803001c00c0742c8415220420340a1500389020406062409030489000d64001c4500600c1605c4031b480844201e66070310541d203594442d24505500d040d00000b00c03100c0ea80034485420119a840122071903c401903441010704101100b2030900c8001e8084134096120043c01400042320f44400441c9151054165600d001107990f441d0200280309007410080702c2ca40d008901c810f02541b40140c000d550744501c2c00101c02c070640e40d2070140d80301c05420382100d84490700030400340b0521074050213240c400c103011b80d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 361178579 1250 361177329 361177331
    0x3180e041103120702011d061c0606050405010504060c06060b0c0304030b31031803060b030f0c010e060906040306061412010501080d0c1a0106020d1409060d02071a07020a06 76
    0x1c2a026840c0000748545070702c0c0025402030420050b580103560843c99110220400c05007076139001c1d16501c0b80405400d11044010303100c884041d66180300340889010f40c00603410001c00b004244a503907046811601141c10601e040340c607034003103800d02500820700d5401c11035003044000b0368a0102c0e0800005070007505d002d402d54510f1a00c2c0c0080740e0700405404680c3c120f1f059200811f00c08500c00c40d0002d042c54a00174208500400c1003009002c1b22060a50002c584071542e46980b00c056003001c0018124401464000300410010400080e00e03088450b0303200780c0304181c001016030441d00d45c2c600355001183c0c0803009000f0142c40b405000741c41044d150a5030300400e6018034880c120801409050304071640304000e41111051180e080b5128000081c2c240d40d1210b007a40746008000c604007100d8000d10340c0380d0150181301580300000703000000000c910201c3c00303018400c4a0783c1e90780d100c048a0b9001045c00b0b005a60300164600304111100421124076510030440c00c1096680e00411951001c9100b810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 361179829 1250 361178579 361178603
    0xc040513020301031509051e1c300204030c0f060314040803010605070809090a0e0c54040605060a081c02012004031b2103180e04 57
    0x500c50100d0109101c050440c4020405000f0b82d036031290b00c1581082d000f83c0503200c40c8100340721030b007240a0b075154650301d0962010b5421a00808200c42200007203c6500c0e040c1c5618221480f0900c1c4002c1c2c2d41e5400c403601c4041c401c1d140d407500103641110001c6a000c041c00c0120b036503070003140d1020040343c0b040b080441d0400c0542c00c1110708002049104a511807071003800c5900b45002203801e5005814101c406040c20001381c409a074540c40d800d031044d009240b011410075a200101030404106800050040595201003602500000c8400501c42c41407502d00013450040c068150072010205c13280714400e0000e071070750303004082003104051045004006c144404d841360000d10000c8a0188504411078101030702030803401c03280701007803480e804451001050f0781e0041ca103104141e8406603540a65078900150070020403403458165980213951303500300841603240031003080d100100c01545d400c4441ca096501000c060265005040504c0b20302d40c22a011038641420b28200d01080e00c3c2a650315107628 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 361181079 1250 361179829 361179859
    0x10e0105100603050406180f05010605060a05041406130305060f070207050f0904020d05030a0e03190c0b0c10020a0e1c02010e010e030a060c020a150902090c03040602120c0405 77
    0x10264500407004210240442071500e0801c9000f0200600100d403a69142c1c4001500140741010031482c06015500500601c1c0c2c451801c40d0031110355a100c5401000c0600081d181580c000d401d9400b242c1144050090031034211002071114450100c03000c488001c0e40d8030120510400190300d44c40f5426280c1c5c4403030940c581c1030041c4c0e0341c0c1300c40d441210b030f01030112107101c0c0550401d0b03505950000d101a26141302452980d40b00d50658000590315000214155a081d031180360420a07902c0e12194544d8a01070105a621986041080c80c02051040c41700050000045001080300f240350301c0d481c41c0304540750300380c40c900142800c85203009248540002c50f030000c95203500443e031107502d070381c140c4500011114004c01034407691003040682d45d01d400354a6140d80401c0c0d141c011000da060203540030342400601440c105840f0340526500180700303840c09046c0001a01c40307002c003581041e148201545c4a42e9907140c484040d100d001008120002e8045c10300c018452800050029210210f44181250b0307118 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 361182329 1250 361181079 361181081
    0x302010215010f0303050903012c0d03020705030d020a14040e01060806030615010e040b0a03110a1715180d2001020909040213022203151404030305180f010608010e01 73
    0xf03001d200e08034400ca403410000680943c1c0180700569028001242040140300c1125041004181e0001000c0c070261503001e44500a201101e480034050038114105103075034071900d903a0f028400404182650000e0180015030003030401d500c94a01c1e0003a11503442c1d0302c0d008145401c280c2803080e100402c0c6000c0102e9810f10700850843d100c2c0501d201e240b009a160780c80115a600c65103101e90760056600c1648801903110303070042c1e60255010702e500b6402003240b20284032180e400c1d41d00003151081c40d091075142038000815912500c1210820a240c0d54890344030f803510070744002019455134441e5144002c1d4882d0003400d052031501c08160320103a8031941e42c003860300780d200e0000d555038012005d200060040c0740c846c4510a813142051001401c05101c10080b00b5141071300d00c458100c1041c00c0208004005052042ca000d000002030300b4400300020322001c007071008000e4001014542c0b01c8000030304200031142091400c801181c05c4404a00c2c1c002580c60080216002c1c0014950a00d01e004001c0581 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 361183579 1250 361182329 361182331
    0xa06050a0b070218041e110a03060510061404060815060a020c040e07120206030c1b1b0102031602040f0b060301090c0933170c04061706090a09020a08030d02040302010215 75
    0x102028646041203006c0360030501d40781c06c0445145405240c58034807074541c030740c0a5001d5881503000103014200403044d500d920003e640400d042124402c24004541403040030f6070212882820301c10700036221000e500700c14441d01084590003c1002c240301090550000d801154090180c4080002d185000348080e16441d1038010004c452024907404001410200000d41c0c0c00000c01d4901400c1c40d101600b003411812072140c2c00707481c40d400b041c03010840030f0104103415544002400194030344684039005041c1080ac0ea80080d00c501e50302c0c02c602001d546c40790041d482040300213000540c2c0390784450031030006202925020001035420800407a0010071500d01442280003a200e180382c0414020340180811b8218010004012920303190f810812040688035010f40c0d500c1a80a807614242000206a040c2c2009524101e11400c010304c07909484402c81e17a40c00c40c4454102090300c940f1070003c03035542032003548880054880040d40a0100305282e000d80190ba00c01d80c01d540c7c0d058581d0700d4626100c10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 361184829 1250 361183579 361183583
    0xa080a2304050d02010509090406050f0703140a0203061804030302180a0503030304060b0310090c061e09050f0f06030c0d050f04080913091b0f090204030f0b0a06050a0b07021804 78
    0x300030401840b80c1c1c50b04644000d003403403051400a00c4d107641d1101041950006a90884030a03455005100074103540d031108940c040031910701080210068003203c4900c8138040d16618981d940000803d04580724481d00700384420141038000794034202490b00038004d604c580d40316020409208081025860480c84103c00ca43c4010021402c680b00c6880d00c000800c01c450101e5414802e001018210351054010031400502508581d00ba0b24540080505000c100e01074030f040700001c100400710215040550407041d1282600d107000e4000603600401c1c9850031864107039a104074013208200c12550f030761000340301e0003030301c007100f4409612040c20801104100303480c01802030f00107000c0c404050410049041e04c42052242c0440c860030a0f0701c03151994241c0507021000600f40c2c04c000d100604402c01200d00606002108600c0c0501d16141c01442052a607002040c415142000c07031005045e54004102410000700742d80b42d915907c05420b00380d5032044108a020300310f1281807804c4920000039503807083d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 361186079 1250 361184829 361184897
    0x80a0807080f07020307080d080601030506011b0311150a0608011103010902070503040504181a07020a030507080f0310030c05030a1703040f050609010b010305090d1e0c02030a080a 79
    0x600300d540701e00103034000c0c5500c05902002030040c07001680e0304004803001880400003030514690a000000c00c543d1009011505044c189410f1144990740600000078000c0c4410f03003401d5482641c64102d44d40340c5513a042c0e5040e4402c00c0d1132000961746403c0c85600441602400708038a650360b100780317130a8a0181e0019a0400018401001080e00a40050104070710032004d81340380588801c0040d04640f44501145040e41c0030500a100f0840d4a0040040410f10842815000d15000b00000d60b01d101903140281040001300d454000c20000c80f0646800b50106100310741c5915080080c032000740d00900c02602d00e0300d6100c000160505006c41c2d1291101d4100030140409907102080c40100d500181c82141d5800c14a10761801240701803140314050f011b00b41c00804c0d00407401c00014155240a46a051142c00c6240c407140800d0700091100c2c4a501078803a85500310350b20030070a9960b090001c3c07029415005150204041040000c0109200000d03a21000b00608080400d0202c2201a41c03c1408403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 361187329 1250 361186079 361186087
    0x3080906030a06050406060503041103073002030f0f100506130e0f071e060e030a1b180504060606230d062c071d010e3106080a08 57
    0x1030a11000466202112003004200c01e5542d402080c02c0318060b50105001030408410700c07041001c004070092000c2c03000c0b0014500c0d48c0c14030018090f5041c6003008080a141007111071601c119050402c0403006800606885081060840c2c050319034420b902408010f0107401c1507152004014452640244000303800d4411004017040c802000700f20a41c030b0442d076845250b00e400c810140070003510000d0100030300031112208540060104a8095802510601801517864401070320009010310286402c04907030f0203c01c10030b8144c3d89040036140c0041141c100743c8c1c040c1c562a03e0390764100c9409103106600400c82c80e0340d149402c4a100c1d1421071403e002d00d0520140b05058100c01000d04110b400c0c1500010741135035103a101780c0c0c401000c2d0403c054400c02e8110081444603001074590350164035424071140012455182c416690114203046050002100c40b44401d074407508841e0803003074401030400b00605150303c0d041155285450341154841d0401c2000300b696030700402c0071001254826071540c14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 361188579 1250 361187329 361187347
    0x30308060f12030a020703020f330c07030303140f0408030f1b07050106050405070504030f26030a0e0d0219110d05010c050301080607031b0819020c250308 68
    0x40e241d1810940c03030384030401002c00308880340244020011000117400410320a4654414851106c070302c41d0b030480c401c03081080303d6025810081e00541440d06200c1002d1060407032410560700d13500490341c0403081840303442e40100030160554080d070120020451000309a940d52605e2080c030b103100701e034010130301e00e42070010526032802100c1d081c3d040311b8106003100a034509410300750055000130409a81683d111441000b140c10588a0740d03070807903824a842d40ca400d0840c0c481001c5031400e000010040100210803282d4010441602c002d100003220301e9603520b0814100040241680cd211a003d038055120701d01841d03400080c3c015070710841518010456211511100f07408410418001e400642a0411000045003841207505404040c0c1340c0c15102d50501d040d245c5030080007050780040c140340101220221201840c202501001407910765aa55a803040303138491410b2800c00140750354004104100003c0020503490350741c0341030040c8541d00c04440d21200369954880c1c4000380000404100d5096 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 361189829 1250 361188579 361188589
    0x90112020d060b040c0905011409210c090c0408010f06060f0509040b13050f090a1505041118070f0503060d020d020a080a05071a070c0603020a0e03100f0e03030103030806 75
    0x95000310320010f03a00300040d020400b80c038000400d003400290442c409114540c0c0180c05290300b212001d50043c1484840d03c04145984400b04041210104507205042120020850480c2806001e0a00c402e03134180010240178541050040058550800340c0310501421071703100b02c01c101c92240c0d440d00342c1c031071901c2420303038071940000c0c03640390042d4a41c0c46448c0340d5225198900446001008002480e151020740b144455a0140620318250481800ba0b00482c1102c00c5028500001400005103515940b5005a0402592040541145c801c010f40c0041400c5c00c104c007403051002c0d40320145800002007044070944003c4030340690003101d84c90a4405802d01c1c501c41b107602c07440038209403035644c7c48842862a1182d02001101c6507480b901040c070481c44600c4041f41002e15038140282010314541e038802d0000d8441c0220000c040d8081034801d602d40c86802e030070f210303c48040e0036101c4001001e5a0310000d40200303100000c0340c505140307035960409000000c41c1d040b08d82640c0c641d401629002c0801c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 361191079 1250 361189829 361189849
    0x615050c0703140123181204061d1002010c090f060c0602070309080f03270907032c060f07080c030c0304030314090d080609070e0f060d02040b0a030b09011202 70
    0x20f1990340d80c542940c440300044148207a0800f00300c034501215450100070035184501c2100d035940450700b0401c06440d01e05003410949065400034242000c9884c800c0c111045000c02514115511100c003290514030240c041d840700e601c4035241d0b99a400d8640d1204010414013405214120005400ba1140e102066459001c0d100440c071070b10300300130700035078824a40c0c3c0303000c041d26003100841d00001001001c480b2001e08240c0701c82c4401c0500d140e8281901c002420100d8002c0000b001d054640b01c012000c410800034420b80b00000c0700300103c2500d04060381541d6810211400ea00c0004881c000c111198000c0c204039101c0c00c8407280080c0355603039140110000341c20107402102410307112942521340d219003143c072610820b513031001495a40c0030b40000420000018000c0c0d8090300490f0144050154800d401306070400c41940e9030700e2201d0040d004a00d41c0c3c0305984405501d1403020802140c084034401c014001102c2c5a9428000682c0700d904100c100380080c42001c024030100d644100050424170212 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 361192329 1250 361191079 361191113
    0x1e050903030909010b25120f0e030f070306140c1b28050105060d050c010e150406020610210b2d01050118030b010b0c0708100615050c0703 61
    0x149062000b0030020880702c100a812a50440c140810704a0070754400300c4181c0652000101820500b99154580b030b180070070000000410061200352401500340590807405289a016040750a12004c1d015501d894684602040b036505040440000c2070418855480340518807044d150303031600000d065240c00701010030000401d68054100541d803445826400b0301c406051115690f074010515240080c02c41d48004c080a214070203a8400d100820800954040c1350301b003c6c2803490301c0301e42d0f140c0020940740c00001d8020ba641800140459000d50214415004076505c0c144c103200d140d01d80f07000e40901d940761003415990030141c0e01c1400200d445112040e8100342c5129090201d000b1402c00410240011258410350701c48140c0100195607008005a00c0c22551900249000303080d50390304400b074003040c4130310b41242002042070f8120600a10a000c000e284000840d02c880501c20101070180100d88940070b4028442c1800d80030b114020812500301d00d030b14070003401525086944400700c0b1030785180342c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 361193579 1250 361192329 361192333
    0xb15120f0304090c2001020d050604090f060b040e010f0b090c070510180501021305090a0e0a0b060103150f050a0510120903110a0b040c0f030c060309030332071e050903 74
    0x3170f0851a8448400141009001c400142c0c0d140c02c040200410b641010b03040b20300992400c602e807800705484210301160540d000f40042681140c12001601401d5100205135245d440c1c603414211007181580a50b031489010f454507030050781ea07400d00e880b4600031144040c045800c074921030303120820260b02c10020002c00b01081c030151035150700c8403401c9801c03050444001a80740c083c140010b181200e403850348024082c02c00c2c000841c030000c2d002c1c3c4842d282c5500424280c001400300d40160301981011010441800844401c0c60743c2d40c80d101c12800d07041c03150601030940004c01043e40e007070031140d0062039000303925004401c0f500040300c00c00070188030009404215120000000d03018040c04181450341c0a00e2880304181402c0c205800e80311107a50004010000c01c03202000000c806884410403903a8030f040c0000c0b54003142c1010b6010b410b0f80e42614110114000e00c0558001d100125900c0c007401d1920010220b5a40d40415070b00305800504403032242026012030740306c40d827281000b0b01b42c803140941 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 361194829 1250 361193579 361193597
    0x7080408130308030910060e011a09030c061c14100311030a14010b0108160912030306080d0f030e0d090521030a0801082806180b15120f0304090c 64
    0x1240f5410750401d480756281904000e0010504456078040c81024000d90884c0ca50a0751402400446005c00c102c2d0706603043d6400f00321a051b5680c107002028600e000a841c45503540c6125120f60782405846185503080c40c600740104507420316a081c0c0d20710607240c414141a8136411a00d8614000c028880f06951502c0f03060024400648842512000b2804201c00843c81d041e549001408a0780020400d03c5561440641914029445015601254036059014a0503011800d00301c0c081d0503a5044000944034607a1f030543c68603413241c910940c3c0c400e6a503080124078940c0141c182c0301c021021403c00010980f238818840d03480c04030f155564241c80c16801c01c100c40e050b40300007070440d00a0001040840c549a00411030800c091120030f4581501400495105000d05a0b80366a000d5601000c0c00ba02d54420400f107200100d80c003052207484c0c01070b4a03450a07280080c080180d04e034030025018040c1801c000607840206000540018206d0078230065404c25041c40f0b918801000700300d5070f9030200300380c2030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 361196079 1250 361194829 361194833
    0x90409061b090501030608060907090513051b040f091112160806071709100519140103060f0204030b0c07060204051005030916050f0f0a0b0a090305060609070804081303 74
    0x1030020703403507002540c50301155245000e00243c1100d126501440d801e070800c9040007070440d004901042907541c0791000044903220700e105031840155101000740140300d20032006000001800d0f418840320021602803011407a1840000d0540d405060001d11059206020001a140100900c010513680c60116000a040405072074448516540581c0f01608002c1c180408554000020b02c8a89103040300c03284581000c414040d5100341140c0040744031665000418080c840c5005031001000c00d21030f05001400e81060282c003d40000e120440d503041c07804604912500c15402698120703900890100c1c050b5032120600b60381544640c008680d44d641c20040410a582c0d0480d0800c80e56800c2e0365600d48030720749103031001d19100d88507182d148450341180c010401603490740e50584080710182c48984030340c1e1290740412014030013604058402200402c0945000b5441702001044034050000c4032825100c81090081b40442500e2820005501c000024041000007000303004030710384000c2e41070700103540f6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 361197329 1250 361196079 361196111
    0x203180310090b060f01020309030a060b06040306020a02010e0d030614040504170f07030f031506050a020703050f10060b040510180308190f030c050307030e070506070309060f0302030c09040906 85
    0x4114103c401110707203020b01c992030411900e44414420280000c51401080c140080c4ea1080b90f8080189826101c8002400544409d000e0b240255800328066445550727600d0064082e04c0788891040841c49801c0700c00c9a203501c00e00030402140e5000040f416003120040c1440301420006200f52046514021a00c4180c040070340245801180300d1400e03500c60019203402403031407400b240d90000709400c0c501c02d1030050260100c2d2908942c118140241d540c00c116034143d080c100c4a90003d0240d0041c0440e0500305003011405416031000000208103058407010480514000e9004d0aa085002d03416031030b1032140100c1e02103194003404100101916035a5803039100c01d0703129107102c0461082c4031070221012034100c1d1100c14641d1050405020907014810001c02c1c9000040040003015140d4204640c0884c05000749409080083d040e20355400390780c1400380102d0541c2c4a260001500c0c68002c6040c60703c24800d43c0d00401c0082d4035549003103803101c00c10015050040e02517442c195a003103c0b8400000b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 361198579 1250 361197329 361197341
    0x804150516050f070e0609010e060f0d0302011e0204030c060f050c0a050325030206160309060911030d020d02060a0209043e0c03032205070303090819030203180310 72
    0x100e00002c00c003002240a50701d0826a1175800391000110358010b004542e03a58008003410b5462102200e01d07182d41e0640040c60380d80c4c020007602d40045401145805159041d0401c100044090704c019902d1448424203000f244a181b0016107041450b501c1800f81d42e06c2000c1260043d510340c40d01f942804418440b20307091860b0b68004a400c4c0d840007a54070000c1c00c00350100d10243e811182e002040c1012910043d40340c00c0d005000700d0000c01e80e0041d01d0802400395000301da440e50040401c001400b40f40c035046801c0081c061407280700740b0079103440c403110b50700c0081d01d0f9100e0b020590180a00d5100c550b00340010750400d002c0d5642c007540f01d8406c1c50810710180940700b500d0307010f02544100c4100002c04501c0c0c68050550350303011210104030b04260601d00100301c9800401c07030b100709100b485821850844043c10300000034220b000c1c0d140008149035000034030728140c949400a40380381c142c4102001d403000f50451402005a041440419941c2e000d02c0c0c102c1c42c0360741c0040d0642d078080f100007211600310f0303107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 361199829 1250 361198579 361198583
    0x1809110903061008070501091232030d0509060403140a0302120a021b03040f0e13050102040612051f0303081005190e0a06140d06020d0c03020301150c0804150516 71
    0xf40b0101000076550410003200101400c2c00c165001a0a0081c1700481140b0801c1c0580b0380150320210040324030360300c0ca50008080300d00d5218950507151010340c5840b0384c04070301c001c4842802e01d0007007055994089403190060b40c1c5512099002c840c010f01000807600030310080001c0c1a82800030400a00d14101d00d607100b9008807000680e2021102c20140d2400700c101d141621680c810f01c4140701c0200d54042c26400e41d214050300400c1c03035441c138864181411a903e00100654004180000d200c2d401c200000b07160340c944003090205980f001403048103414965000105208400c404101003070241e000786401800001040b08295110404515540e00100d040c4454503084407082060a8207900304540100c00e1040c207002d100d00c0d00c44400c14000118002c18403a0450805000070030007a40d0440d040300d405040c061015882d40000500250024031035603145260150325040b403144101c0ba12090355138014002d508041c2040d41030740740d1541001c1c80c1c100780300c0100216004090840201c0c01c8141c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 361201079 1250 361199829 361199851
    0x8040609151d040f09050709060e090a02060901031e0606080a0606020c0603041205041a04050f0f090708130b0412020c0102030c0d0f0c080304060f050106180911090306 74
    0x2031a00c1c00001c1050100303070710002040000c4142e40e111044150b0200c09071481160301288580042d0aa03600601241c02e006000d840f0303031500000d0343e0401d600542c00320b98421b038849c5415a070782d0003000e03126424204025030104080052403c04d41c0a5403180c8101c0040a1000d0301c452000c1c06884121800340d00000e0109007800201b09607490b19028050180409101601c410314411010900c1804050300003800c404201240401c440d205001390740051442e0026070341141c1d03250404e1003413030344103020f540d00506031200c03c1c01c070718200302075000c0d60380d8800341c03000c00e255448290403a08041c020340400030b0110744001e09408100c00e0602c99000714003480c00c080300e90708201000b034640111800244e041d5041404401c50380200440c911000403000d05100c08403c0100101307e4000c0040d6500030b00a15011041c0814840641d10504c100b001d900410003d503600c8144c1034600d00d080a0790788515500b40b420511000007543c0107812041d400d130070b10078200f41d0700c02c0c0000d09020017111044061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 361202329 1250 361201079 361201097
    0xd0921020612010e1302011d180c07150608150604060825060804030903030f120507120e0102090a0b0c0705150307090b031308181201020904061e05010c0f080406 71
    0x40c1c0c2c4804d40c01e98119503e0070024004080560018044a14400030540440c803200c3d510800c07a29294444002d05048411003002c43c54154503c0700d503500308601c10b41d194a4400e172049546491403150100b40d85054004100c4080340c88101c200d0712000626103900551120780025135200e0822892085903407190401c50341c001280311b29101d81d040707684080100030408080c080483c1d001700042080d65018940f00d500d80c428003906030780613242c1c81540c0d6456458401040302265200c3e054041d00e8100341c0040c45800c080c45583c03803d0380a0405080d5100002036010000c601e0044020080c40c840e8000340e4a5640d40c62000408940d480d08804400003400000c01214036032002028000e03115084045040d400c0802100144011000c0014100303040000d0f44065150440318215030160000c102d003000c0000c00c1c89440c00f270741000c50701034003c41c00c02401040c40b8071118408101c0040822500c0d000500c2c00b00111000c031000c1d030b82560f8078203000d50544046592040140f02400c090f407100c00c50 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 361203579 1250 361202329 361202339
    0x30c0307091e050f040f0602040e0f0103021809070b07020f03010f0219050307170601021c030c02100501030807020103020a0c150c090605031501031a0904150b030d092102061201 78
    0x202c6001820303200307450001000a074101400c40d95030019081003551013140e01d2444c01c44000c1c4519004040382038203001c2000100241e5000c068141e83c829038040c0c1c8080f522180303c8510050a460130b072403a401500061021000c4107000d000d445000900801945c1c5c120b101207400c403030561105050a07500020102c0604c40f012040c4d1070046e0552602920f90715100c0130091040030030300151124031450101003030260b80308100d418000c1548440c580c00c10038070840d01030014518003c0c528058000e14200380400960362080b58101d0340c1082044d45420426030044009510100581050040c2c4040300800700e0b5841c04001c481d880d08003000900b208008a026148003055403203001000030070020090319004d00307189201428028200414510444d1003e080424134001c2043e4000e45a50204010700501d071210b81c0d541e00c11481d04200010b14201410b45a178008918400403d1114008001c180711200c5070703c28449400b1a4056103501a500058941e804001c1401e10030030030000601c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 361204829 1250 361203579 361203611
    0x1401090215120109050c040e180f070506070b0903220e01090915200c07030b070507020303041403030904021204031409030a1713120c0f0f0e0402030c030709 69
    0x403150081c03211424030306120810340b201001400303600403154456010aa86496042c04d035000307008403140c1100d5600c0d00410b030b0f16904001d602210034900c51a410071402c0c0c00c0110b600c0054400180249241a05540365074050000103040301c015807108020303040c0850200a50603060121030320422166a21703290200d40c0c0010306801c00e17000c081c42c141c41c0c4000200d28502c2194400444000498003241c41182c240120416090441e0001400207200b9861440070441c4401c1e00d00c1203100030700d10344450108480c84d000f0254003d4240d44200f100384001c41083c074500c1d0300e03d4801400c80340740100c2075002c50280c0c0c00801c2110401c68024040c0070405130030048118007100b0881e41d40b030406808600003130f900d03503003040050030360214884c101c2301904103142110766000c0440750000c10f103541e80e0888451120b044805072070300c00e0000c4010800700a1a0384a804403081d07160341c900ca035814266070004942d4003900c00c0703901d0320489502c1c41d11350300c1c02c0c41071000800c03500c440003e40744c006020ba61 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 361206079 1250 361204829 361204849
    0xc210a050708160f1403160b04170106060819090f031d011806050a0203070c0e091507121e05010608190209061909080f03030601030e0a02010815010c14010902 70
    0x201e5581c01e40901031101d0704e0500c02038070031a000e58203000350a410050103e414030300d0b100683e05091400600c08071707021138148010300841d62046040204c06034426070f0705080b10384500510001a103504081642c0041866500c06008000b0000103080040ca41d0b030688901d40318407088010030f400100300c40700d40c0f07003c1650ba82100d4081c206020506050400d41d001c5440074000d28051103004103000c1d9295108000f541c02c1d455201041030b07000398a510f0754095101045078605041e10400f941959030303e540800c0b0350701074590790b12040d6409500081c0003010300003801c102224687c1890304035262000074010103009200a4441000350704182180d046550034034407a0350040e0380100000701c166210801220b001014440040c02056200e000888004043d80d00460721071051000d1740703030100e201200a60140c0c0e400d8908011aa824102043e265440214042d01088501c0300150720b40d00c0c2c0c1000000032013030500d07182c0d2104400c2c2d42d56200c00c0c074142c050740c415a0354134070390001141410322250b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 361207329 1250 361206079 361206103
    0x3041b120209070f090e0705040e0114100c03140307170a2406120b0109050307080d0306050a0e180111040603050105031005010f210f03021005180c210a050708 70
    0x204c044d0f2540b20340e000e070000c403491044031160308004000809061040303064034080d20200c1810203295a480c500d881d08541c0e22030318584205554502c1d1036040d03000303146500d84280d05880780c125240101d1030000241d00001c001c0b4041c803080100c80c2801248855025102d0600c03641c0c0001c80e008007484410252000210303103802120519818461150404a075800304410002e010404a01a200403501d491055118982601c070b0220003041001d0046030810401000d0ba5081000e1641c0e40e041006208051060034040310601b00411008514a040d220000c4440d00000c54031402c1d4200c0b000480d40161300c000d0000f0782d00d40040c401c500e002d00c244480946617907804c1c810b5506045c0d202c2c044038031170f20030440c0c0704007200c0c1462110307540605154001074101039500d650407520f0401a4540b0900c2a41564861400700001c00118080c02c4211595800d44c0c01808018080c5040c03001070703640359100080c05101500d10600010080040c0b10359144540068202c01740b0f0003542c18502504104a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 361208579 1250 361207329 361207337
    0x606030f29190504060b1507051911040e0106030b18010b0d050606010f0e0d0b060f010309050d050d020c100915090f022e05031602060411040203041b12020907 70
    0x9002c0d022250030703494004100403060004072500c2d10300c1c10300010080509001e40280c1d4400001c20b02c156941c001c1c00203180164103a800c0112180c805c88102c0281a000400003c8608101178680c00c1680c4031450b101c1c0140000141030740c82e500c0300b00c91050102d030b200b02c1c02800ca00a400d9014000c0c00381b00c0710b08805071070143c3d62200c6503a6450301d6a0380101000e042190750011046006d106901b0550030b001c01400d911030780001814100314007081198a10700601410341300c040d05510a22510340e90540050285c0b108040380d038400c0319141e00c403200043c0c1c010b4007840b011300c0110003130020074000d608980c0002000281e52800d50300030b03041940d1000070360f80380aa0160105403004105961381d0340c11105c07503010804da05090413980e580a0503280e0b400320011540400160060001d5000360f444041c80c42180755090000c03656240100c43c01030103c061a68688038030b0a06402070341d0002d104513075080c460b140c4100002a0108031780c0c042c40c02c01c003820700a601136081180880ea0440801d10b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 361209829 1250 361208579 361208581
    0x902091009120b06030304180203010306051f030b060a0b0c06010f050a0e15150304030206040519111e090a050a061d180c1206060a081c0c0606030f29 66
    0x248030390b00402d00031000c2c1c202000200000c5450b5001c0c03003140c010b826130019602c1d142c1e0585d40c410f030094000340001c40c0c0c0300380361001082003000d800e80414881200201e4140060b400d65503420030300c21b0081c0c00c9940010902002284844e20100501000c8410f0402030040d03600d0010003078220807103940082d018540c004000c1c886080f0240040b0780c4000c0d0800b101111250101c042030051035102407a181c0098044240820035602092560042d809003049a03a001c040500070301130404e64200040c80100b0000d40303040705040060075501030b0303640c0941083c03042420002003070003001d0031240c40840b19038440c1000a00d100f103114500280c0403a0b010010b03002c9414602480f04c03c0040c160312500c50040743c24816500007000b01410340c520141500703070b0002d000c10315107680b4803081e02e41c0d41c803841c90f07044003282081000826111140400b00d40c6204009020000d03070b2110090305040d13071010384404021011401054540c02c0081c824040ca008903121181400842501d07080015002d040c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 361211079 1250 361209829 361209839
    0xe0f011b110a14030d0f1b05130909080c0a03021501140604271109040e0606030c0d03022803021501061409031006030308090708010908070f080903070902091009 71
    0x6000b0005035210360240010b1a14080c00e40ca58040c03a001d0045490400c030000d462007107150040c40500d14440400130713071040360ba9020769a0703002d20804580c038000e0340541040b0201c650380021003a1801805c1251425904810890070802214015000f50b400702190f0002d58490380407060040c11102e40d1074441c0700d0b16600154683c0304501c502000c00811a4410a6602e0b405550400000105a0070003491801c00c142018a0f0003d140e0203100b245004404042c407540401c001c2e101c1c40380180942403074041c0c0b004000003490413103003d40440c460944003510400c0b81c600342a01054219078802c1c5071034001e10700203242c4843c601041e801264500010400c55030800c1c0c2030011034011030142500c07060100017091034500c880080407103440c2400f000100341500003c400d8050003408058900d819195100300742031344c400000050400c1000c1040d07401140d00c01d030f408265030b03105500c018503080100f400a86041c2e4181c00c038003041e550014010005103031041c1c00c09551700c0e080c104000424645 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 361212329 1250 361211079 361211083
    0x31a1e0601170a0f06080c0301060e040b04170706020406080103020f0301020c0c100216030c090e07080a030f03021b07050a06030c0813030e060406030f142203030e0f011b11 76
    0x8540071503046050001c50f0104960b50042d03d45850302240401070039a40340f00301992140030042e0f0314001c0d40b810030b01080d080035440000d840703907030040c1d00e40655461701ea40f0030360f20214500f20142c2005017131210400141542c00104011b018580e20000c15504500410140d00c290032840c1d031081c0e10420000f0064900030400d42c0010700101e8110142c034031440d500780d00380101007020b01d6098a51038408070411a9604d040c20685107088420442680b40104042d40c52915000300302842e40704c10040000284200140380310400140340242c00d0401810718210180b1b41604101c140b0f401810302071040d030400003071a00c0100302d02e01d010b0259000e62440500603050160003070b000d0710401184001498059108119a0040541a1a03689541e102d00900412135498000005401c3c1904401c103004a201e04034002c100b02d4000f00c0858071001d1601407955601032084051645840420708040c03402d221008020307549400114459412400c00540c899800700c003c0144210301c40c40440c02400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 361213579 1250 361212329 361212347
    0x10806060d0f030c080f0708220b1801050d1107020906010201020a1b0606030803010806160f0e060c1006260114061003020d0903050705060a11090d0606031a1e0601 72
    0x94106411a4021801c0c0041e02d07100390541b01a104e4800a142402c00011000401d100c504940180842296000c5d590740480e0262103000480d4605110354220303c0a071564a200c5048141800352803c203551581100307540f02800000f10000307000ca0300c4019801c10a05555008809100071894214a010058a51380311140b541351205000e640c00820403500790b010340c000d50380100c0f45907129030b503443c116a07503100308540000c64a250340344075030179240c020404400c018016480e608040b240f428103001d03864000c0c540030941d5210f10f81a000d0300034401c1c800c6002504140c4030003000804003115602201203880384103017142c0e142c50350590204040d0b88006802400884890b051803a60981c228042d0086120368038003545000b040074109500b000042c54058400c209550141e594800071000312341c28509074081081040040d028540361905807140342e0b500c141000502d160301c9854500d086c0407521080604811800306111708090449043d001e50003991010038050b03d4103100007092001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 361214829 1250 361213579 361213583
    0x80f0a090b01060c02030c090a060f170304060c03020c040f0606030e030c120c070312080105130c0804110114160203060f011409040201140a02152a030c070218010806060d0f 76
    0x181130708203000c40d40c0500524203c51401404207085081040c00107004100611505c4005481ca40001800c4072949400c00050310b4083c0147d803c041c6040410380d50070030144411030031400341c2d00a070503e966451280503c2ca100d007100c0002c40f103041c013102900326003803098840c0041d80180010111000c00003004c01e150744801401d0703a182d16070b50041a10b00756803504001c0201601d200f003400015030040101d0304072541221b080d9820351380b0405c1e64084032050280c10303001031603220019002c1186520243c5d0941c006140807440c42c12500010151900b0507080408668014001e1500b58a000c0005c2038221641c0003520b40d29502d02030404040303140c42c02c032003402154144006019680542101030260138005c101c0c139903c0600000007500d900440c030303004034860446070220340d541c00d1a4022500368840115810760752002801003100c103400090481e0070b552001c124150068481c00c00c0054149040410288076504098510b07040100040006000d00351040110010441c0d649480744055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 361216079 1250 361214829 361214837
    0x412030e1c08092704060c03230612120d0207020307050103050c030411061309020a030f0e150a0b0409050307170f07020d050a021903020906090105060406110c0a06080f0a090b0106 79
    0x204c144a1000a10045024500c01c0407940c807040100b880f1030354000c03050742642079404000010081e40a03000241110094400c01d20711040080d1040c1001c02001002c4407201d42161080000c1e81048107440d0f02009448540702d40201c2d500c4110b0404001e14805000242014442480e02050140c454000280080d05943c0120303110010b5480720400c4940c2d8003500594400156215603206002c1d41c460308001001034640281c21441102a10410039000c042d070000c0c002d00d00f40c4c040c06100050b000f078420034580d565100c0320741913035445100c0c000030701d84154003031038489010b400d0480b45a2402504003203900b90070040110110001c204903180c0d150f04480c802d20302c04040c106070f80f810580302002500103d01048901da650390091071441203174803c40702d00072995114410301c4a900d0084c8540791308002c00b40300134011140980851640182804100c9c0c5116584030005520001c081e4040c0000c651386c4c501344410320b107005a0f140d82c001000c00082c48411038540d280d17425039005104010803c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 361217329 1250 361216079 361216099
    0x806040b1b0f03070914041a010c02042307090e0903030a180f110415030209220f031805220f02070c0e010501021e10110412030e1c0809 60
    0x6030007410036500103407081200991607140c03880020f400c0848501440030817410108010303c1600d0940100152100c01c1075403200c1141341c400040d41c25a808100403a03011751039440c036a00c090f0000300389003410a404030105205040011f0050210359041d0400c120308811201003001c012000001c070b81d0416810100000c3c840c0da410041c160260220000070324507120f0121038024012108107410206008442c00c01140203035804c160150392040c400250094048400500040e800c40c10403982c0c01c0c14844041e8052031155141210601c400760120301007010070407404402403118803c000540000c2d20405010307984194180009500011001c1c82c4a450340c13610f8030a040e0b0f0b60180c90300e199102a986080a0f215152500d0443c0d090203201e0051062035400201800e01032001030300c4060b8540604451202c5c5904d05000e8101d04910070310080041000040b81d041524004002c54001e07030341c41000c40c1c0804100080d1a0728410301a04440001e002840440c00102c11100032003401c403000700d44 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 361218579 1250 361217329 361217371
    0x1a1015030921031a010c020f041b02062703090405090f0111120a020306060f0c01110703020d08063c040c05030709051c03050315060307090f0806040b 66
    0x500035200000b06000c50100300b0307000c05404501511081100c0c0c1c0c40a0201c020000280440d0040c07501083d40001c00025040c40941051020240f14130030142c000702d6800c0040495100110380c84125100681c020000c10840194043e00d8203451072802e040d10030fa01d2032401006640b0b0094415179440750380d48402284e90414104281c0705100c000d88000c0c8042a450b001401454010520304840b03080c2d40b100240890256200320392160f0001800d00d800c10704494841300c8940c100081c080c0040d0342e03c01c803425503625a007014000941c8282d0040c098400c00f9a0f00401c00380c0007400c400d0041c0a8134a07507600c0b1141000f940c0d109c01c0f411202400310003c00c0e0005c030409000f854600c540041c42c08600c44015580035009622a40180d201e07a600c040e48c0d50706006410b40c0f01608000d1159220860b0b0740080e03c00c500442c2c10040103041490120043ca00040356070b4001d58444011a9030b01408106104401614000a09031700e4040c200702d140035207600c4140c00009040d00d100c0c111645200300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 361219829 1250 361218579 361218581
    0x501030305030a05270c13050903031308040503010501091b09050f010e041e0c08100609030b0703140a0501090f0207020f04050c040b040305070501031a0310021608070f1a101503 78
    0x1405900481840b175140826298840c0d4560303405600400f020403442c0c40341400380c042d85002d000190000d61650741c800f50f40030300300b100c0d10004543d00e0300c0800c00002d285d0b601340642800780078292400070b0401c010b04144112062050a80d00510201c040f080040c1eaa541c800c08075494030070700741224a20705c254005401041144008142041d1081d0202c02d02055944140e1081c525070f111560142c03654000c9004440c0207204d0000000c9603180c1c140001000e403449141c2080c00c030305001c80d03014882c0d000d201404070212610304080f0347e60801000030b003407240243c40292503480e00071407402c0a26008204c0d050a1481400d01660f15200410754000d110f40840307004100c0c800308503444903100d01e0000c0c1c0b2221a8814540002c2c1002104000d880b0b42e20300360000054000d0003004000c554121010207034208600405604c2000c004010104585000070720601d440b80c401110741c244149444589102c05155080041c0800170801090080784a206010703284104040c1801c8600c418040f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 361221079 1250 361219829 361219861
    0x1101030218060f0316080103150f0209060711040b0402040308090d020111120c28060c09050d030201140c09031b04020f0c0a0201120e030a110a080a021509010501030305030a05 77
    0x1d6000680090411420001e200c00783d4002d1840300050200d140c1e01c0c4100f00e524040a000140440704541c244003004443c551003826421329000300541803114000002d40d440d00015000d0300d88100b44661803215140c1803207814641c81c001c660443c10b240c115110030629028058810f0301402e40000c0001c1568081c404c180342d040041011a50103204d90f10100580f60005844900d862041a001041c0d45001d59020495540141000c151440301ea40303a1001070b160600e450010321914410200d482c1c0c0f10701c0da03800301190081e0004a0100649103403229035401c01404001611030500c000c1c030305a0340c0800d41c1034a1640a10311011000d080d400010001e101d442c14152800d42d001500484016003c02c1440d60795000741c942c030f43c4629441c107410041d901e04940781001d5410421401c843c072402042d02562801c035103004c035030148025584020503540916080000b5034015540e46083c20720660260703a0206010000313002030351543d80c010b499400040c1c80b0300600d54079800092a0365103416044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 361222329 1250 361221079 361221127
    0x6070c0306021c15030b04030e0a08030c0708060609070c0f3e0d050c10120501061e020f0316030c0209010314010b030a051903170a020a1b11010302 65
    0xb15521504103040300708103100803100c0601e1500303105120944009110100b8111303900a4100f41050355280d40c101d501065240801e640b280c50210080384112042010300410041c41c2c00034026036040144d450f26150005105611860100e01003204843c3d12081d00c007041944612200c004e6291483d00850041c1d4541c0c8160b095000c21100303070340501c940c040301800c0a4141c80c550720140c1c1d81e8401c0c480b01c3c89203918058129800600325444504102001251482c800c0c41c01c421040304040c4180e003980c100307910110008101c0c012000007002414020b02c012181400140641c042541140e5100d000d0444015041082c03103000e042450b000c0c0100281c01c690041c26030a5540c1c503882c000380c4040c017900c0c80714843d6180064105240c2000681a902541c01000400c980550810200700540f581c4108504011042000c03810f80c0c03c0440b0001d001d221035120168442050000c02090980c1d00400c0c6169000002801c2e40868014079412160381020700e4090b036610000c20700340c594480c4c02052 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 361223579 1250 361222329 361222331
    0x2010f14030a09020109082a01030b040e0313290904061508160302040b0403140a0209010e0915071704062003041b0b0f03070903120804030314070e06070c0306 70
    0xb0051842059032002041a200b62038150340c043e20741e1310050741c0c0c1072066801c0a9003103511001c580c640c03150801d10702c01c0c0c0405250214101c0d0040f00800c0c10381386507000084050307101007a40079602443c070366014041d02a0402e0329205141c02d01c0ea02030010303400950060117a00c0024040300c0b51711142c01550203031450900fa90100281010010070102c0110303076800410400d2482001c006210340203d4048446000c01e141c04c3c5401c6440340c0d81e14a56840485c4450301c41e900e41c010050320381484007802884104212031083ca004000c0600b008000900172070300c0440d0000300324000f50000702e05601c1a40c101c12104441c2c6e110315081d001041e00091112070841c0c843c2c00702e0540200840158441c40c805d0100078084246449030034a01d101d01c0c020800c10700340622048903c00c10450145a001110380303030910380f280c0e8075100e00c0c83d54880344a0100008048038200b10905401d4010640048400c0010100340d00d0058001804036000010f900d110314000a005030620020031107880146800c100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 361224829 1250 361223579 361223581
    0x60109030819080a1a010302181203070c05010c1223220902040609030201050304060615030605040b0a03030816020f0f03071a010812031312050c01060f080a02010f1403 74
    0x40480d4000e805070720200040c1c462000101c403a403560003014926141c42043d5824005d0400041d0065000007015054681245584224035518201c90b21150356522014640e15582410310b005850003a030016414031689503192400940c594001401c1c109592510901c0c12800b415000d10814080100c10048070380429036180c0c1018000000d0600d02d948180084950b42d86c0070500240d000324032624003c140c0450080026502440c01583e100b441a500083c3c0310381c641c0002c0076440500000b44d00000d58032032083c441c070300f4a8403c10b054020301300c446540b494910f0b50300501c020001040c8503d441034078008001c000380200700103017200444100b6540521119121241d5035084000203560040303644040707035403850080d039070281600c80003030140101c80d1414031140002d900c00b502c000b2800b0394410405003c10014040c0030481c102030f54030a030340d17002960000360039a0190f400400354988419400c01284400141c14411264282012218482141015281d5600c010300040003c04004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 361226079 1250 361224829 361224847
    0x20712050a0f020f1005130c03110901061b080a030e07120309060c05150601050903010e0a03080a1512141618020313110a08030414030f010b010203030f0601090308 72
    0xe4058035155565989075442102e41c2c001c102c0e03464444454669654101500c0690441642c3d04010b0707001020045c58100c007030450b07603a000c0301e403070552040c1d0748805039251080c00c1d1300d8504441801062240740218200b22800c00701a10b5907209c0704014107011001401c01020b60003030300310700b00e042c12807425200f000f60350b40b81ca081044046002100001c0c204040850020f000d0700e80000c01c039402c2002400c0c81100751000062600001c1c14542c103100e0b0500076001140c0d001d0141c0d5100c660407a0107420b10101c0340c58098410f0502a10762115103090080510a4880b65030350f0204030f03100a141208440c5060030400360300707907402c4680d0407e4000e000d10b40f40505024110f040464040e0000703c0641c40300c600300541207000680f40e003600380300313603407407031b0b80801c10200d88607601210060149000c20781d40e501080c55a0301c03691120300c2c1c00e4003800c080b08651505110790024000b40c42c0080c0044901078000035143d00c0000c01701c100500b0001e02191981c1d2123240030002440d4001940c81c0c0e565501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 361227329 1250 361226079 361226087
    0x6180605090a0c02030301030b1b030106030b09060f24070c060207031104020901080c030601090806011e1203020a0f05070807030f060c172a181f0e1003020712 70
    0x9000345401902420040b400c00d842c144514010701c1101e502543c1540d00359605d10707440310005400002004424440003640140b514000e500a0402da03d0004114003610140080b4500003880640f140d10802c0300401a52204900390342a5450305407004104203000711101524041c1c00d030041c010a10f41d00b80820043d40010309001568001c019110f00d4550000802041e48940c03250740340002c030071708042020745541e4000741d0340042e01418220301d02600d400c500c070324200d0240d00a0b481c03440c6444000001850b070070312880c058034800c0c081f408600019280a580ca14003640010611a4603003009014030105120701c01c0500300300d20540349010350701d090a00106020100c1903c80b540390601c21070441e80608812805500752115030302e40c641d1003035000346060307840c03112800481d00c1c40c02000000711440c1001b4400e01404811b43d80700c0408900502480182c403000c1016051719140300c802c0c0003900000500240c040823170707107502400c0380044203d0182c00b800b100100f11102c0d42003c249000c0d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 361228579 1250 361227329 361227341
    0x240a0f0504080706021f021905030405010b09040b150a0803090108060312041d060f030a03031a0d0812100b07020d08160309050411041a2b0203040b06120d030f0618 72
    0x12010b640d0101c0014150740007ca01c14800010842c8410042249110740102c001e15440350013000005101504c29011444501c0105d80441c0c2072603401b0100314414040004280c00c103042030352907001306800c00361020f543e442030443c9581400f6015001a441359000c2042600384450b080b819a10341e66600c0030985050000c00c45200c03a116500006210b81c148401042050040113000309000c1d40c1e6524240d008103404400d03040700c100501c104240395242c0040fa900d5140c07147d0b09250795800100848060b00754080c0819204081403c01041540c000f4400e403082c9907011501c81072410801e10744103109204810b03070b400d402c0c24828006418144c1003200241228815030341032146950031042d41c42c603403245000c2c914030054000e41e20820144500d02a005d40c2c407004c65410840160312896103420320850706c9441d9480d400008000411104a003801d8000805860034640d8640445410340c494a403010340b0300c109030b6a01c8800e44880d006810800061092200c00082041044842809040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 361229829 1250 361228579 361228603
    0x5100f030c0603060b0c0607031a060f1c0203060102120307120e060601090e0c0d09080421050708010b0d0b070e04020c10270f06110f09240a0f050408070602 69
    0x1316056000403210720490494416103101405050b8550b98000260000e000450103100e40006100b009010341d200c14004080145101103542e031500601c8091080e000c0c140010500c0190042c818054aa60001085540402801c40c003a46a40c3c4d600c20495482002c3d0400c1a103d90500f655001c0020007c40d600d03000b10401e90314130030440d0b1560540904201c003070743d80c8502d001c010040510741c0d41d425071244454070b1103030001c0c51825944ac81c0d0362504601c50010049034101420751482000b004200040081421324001d00c00142500d002681e80c00040402801521510b400543d5461090120b02000c40c8000c00840d01c80c00c44c03c0d10556512841ca808404a03440c04c4c141d2203100b1352100c1180700160000560410001e4265145039902c0141c40d0b084aa9075107807081a420030700c9540140482c520240009030b2a12529030400040c454050340340d01e100099440c40e4501803500d40e08481c00b003545400e20301e003861400c81085400e071040d0340c08003e00303000d603200104d1244c0e07001c21554841c1c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 361231079 1250 361229829 361229831
    0x30d09061a010309150b0303090a0306060626011404090506070207060f0215060105160602030a050a0f020307020c0603100302060309060106080c03310b040f03030e0a02011205100f030c0603 83
    0x24440400550498042c030b030014000400b05c0c082d00072051916004242c00c004003038185da05100080d0017007859a40c13142c02c00c961075525003a00748520342d80003002500300509611359092481c144d601c420030301001801034000141a1501d040071507212508429100d907030080c1112460b00c1c020500030740350007680c080c0b2000580d82500501d252480007038000c41688804200105075101c0c8030042d55075a100075200d900c800c0195400310045a501c2c40998451031f04603001094500e070003100d1000b00d4005030090365a0300e10500a101c42c8035030000d03410603401c000f41c401983d6916211104074041040d03078402540104000100600c040d00410403504031001c03034803850072641b20441d10030b031a800304941c25000208602585201040802107180f20300071240c005034403a9480784c83d02d90a2030400c490943c0d10340081007542003050f6061090304101d103004800350140102e00c0d40001c04885046200d80c0c15240c1320341c00314948020501042d801003505103c10005191341e441c20408071f0b012803040c50003007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 361232329 1250 361231079 361231121
    0x70c02010e010f081504111b100c0e1210020a0507020f10050a0305040303060f080d0801060810030b0c0903030a0c050c0a1a0d06050a0f090f090b06060705030d0906 72
    0x65000d143e860052404944503e442c80e03940a8140f00c02c0c1c10400328496004d9100c4e00905907001113000100448061a052400020744811000e440e200e04980c1c003072261071030003502d5541191310090482944400310b1380c082d00000d80064041c502052034004c20342c0c030b0b4400121900026005030081030f04034420340301901003040d050200640003c0c2401c1c4c041c0420000c102c0001c00707600c203034030a6a21038828100090710a0700c8240d45002020142c00180240e80014104130030b86070483c0140c2d0042000d850f00170464500000340d11b20703440003480001c081c280400041030820701180d0949944103400340480c0c1d03c03051481030040c400055007030107803528050a104181d4034103120000e01d00b0b9500c401c12002c246500104001142d500003a000744071945e8034803001c203c99450004110080020f007003d00d61072410103d41d0400c47e92640070174001c9130326200500307000501056140d80c0c03049044a0181e2140d000d41000390841c454075807140c07400e924103648001000b0705980300d1100990b40e8842c404030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 361233579 1250 361232329 361232357
    0x305030d09021c0317130c060c0203011a1003020c1908090a060203030702060c0d090507080304170f070909260d060617160e0d140c06070c0509150306070c0201 70
    0x5083c403406010f40002d80c16240450a00c00481c0c0720703a001901c502e03411043c0d900907142d50908a640b9000800064200302e921015850240144441002c3c1308508050b200fa0701000143e40304200f504244c185500880c4c0c80d030740c0100900203c420568401b007488400d1599141989141c0c0c00039090b20b114240490340803d05070710008c04e817842540260020601600e8102c4e0400341c9811a400840c0b445403200c041d403000510070311692004103101c4000755252420107280341e610020840d400b107155408540400c000c400002120011102c2c4c5c1600040e2162050408480c4250481d851400c01d880c0f60b42c3d100c403a80c2c90708008281c441981401000700d81c1d01d07034804981f1440345040c0880a0071240d0003140340c207550442604000c020508244a00ba07841402140d18113102c0e184c240c40301c1210306420043c44e00d0602030b200400b1000c40303005207005419552418507120601030340b8040c4601c0b000190142c04010782c08100707014000c0440e895071030107190040a4036071044081b40040d107a1402404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 361234829 1250 361233579 361233619
    0x6090f0e0313030204020f041206090b070f021002030901110a0c020f0a0b0328090803100e010602060f0718141809071809060e160e0f0f0601090305030d0902 69
    0xa02e11001e006041492640d020030000c1d4005250500160b401000000b03444c64840c114808101e2040c2008a2844003509280b800c100d0014244000d106408154407062503011401c0e00203103013441c40050300d0340c0b80c44800500420b11800081841c1600180303684101c0d81095005000901c200c0d0000304505092081c090108284d1156800078403090020849070413402042e0700a0030946d000c651841d28203014200251038070000241c80c02840041401a401c80b00442c05001d8150000c801c3d0255161020003951107600412100f0800030040105200781e02c500c0c20b80c440d805003902e80f07501d903e0300e5400c44031400ea1546c242c41d00c0361400303113041c2560502c159074651081c1d010304080c00f0150318052446040e610b0701000349040e03603548ea440c4400240a4413444103890034401c01403071807181c40a4450011032494100c0b01c0400040f400300500c91055212155010b0f100c0602d92116445100c01a2580007007904000c1c203c1c080418044d0f011404c990144032968021907c5020b81c0c1040c101c0c1ea8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 361236079 1250 361234829 361234837
    0x9170d051506190c0b07030204051503061c030e06040603050a0b041b0509010c02061209190809010f05120708090d0903050a020d02060c07080703023d02030d06090f0e03 74
    0x80d070050020301c20300c3d0390b04840d848140b0002c41c00d030800c0400c5030420ba80d800b100c440f0072103505022a5011600b4004e074185600c8008404121066491460400c1c4001403190001c2c007032140424991403160808040c0704804107007060201404c00c0351200d407142005406404201c580c10507461030040ca540152030503002d845d62a14680001c1c0081005549003100c05910110a4a050222900701702c0e0040c0c503514001c10700074280d221282c4041c10076080550410700208801950004d13040e00d648041113032101114120310342420301905d0b94030400c0050314603000d580c281328031906001080000301500040c48520400300340080e5101500140d070203544031946808041e24592014081c9801803c01d0f554012103140001c042c14101600c0c000b0080c507000403604002c0b0541c001ca0020030440c1000780c00c41d025029601c60035009684a007c9040c641c40c42c0c1b0b40b040b80d09035001c84098905034024412141e251b5440c60301071003165203514803c0c1c0507103d211411315516181810321010040080142c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 361237329 1250 361236079 361236121
    0x30a030509061015020c06070501020a09081506040203070c021002060601020f0d051210050d05070905060607021c080c190c050603010303080718090c03090b06060f0d0f09170d05 78
    0x420f071906140d09900c0100d01c1d05800307810b44c03088441d0100940c0c0d03014064056180700764009660340500810042c648422a03101c0c640c02e41c000103250130250401641c096005505640040e00d95039603080c22114030034082c80c065046420b131304114840c01c1c3d000c03508921400c0280c08454134103280552150b0b9803a400030410b000034109101d6610189151520b0b02c0d000f00d42100c030b01005944600000d030104500c6101143c0552000400700f101805500603039034000011227246040030301a80210b050b22400c40c50081000d0400d0448208100260b130584907100c01c24001c5a02080364030380000002c11000710f00391151001503000142621f0700a089a0503030b51326035184d12179502d602806845040407a2044614409582c4005c80e90281a100e0102d19102c5640c0c0842e00001509040043d1180503007260b006600800504d00c90b240c01a08940058bc4450800200c25404241c03400090040882c020803184510b83c41c064800582c1c13010308001c0c5107442d01001261034105100e440081c42c4448 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 361238579 1250 361237329 361237351
    0x91d0604033014091f051b041212030c0512190f090512160201110a060207031d10050f1b0a0b0910060e060d08120f220b040b040507030c08030a03050906 67
    0x1022a21700b00c0e07001070741c028045448004c0383d40070303d02202ca00c5404ca504170308595050b00d2800d0003801400302080400001034182004010103141000f00140b0400f08110841404031021422f141c000010310255600140820012891050006000b811918034142e413144034180c0684400080c00e412240f1501c00000c0500c407034080e0b9401941c085c400392028030701c54000c070b00c44c0001040240c001411864407039134441040e01c040340c1c0075040f03414000d01043e0107142c0000302d004100d5082070450740d44007451503103682ca48144d45800001c80724106042040342c001c1c5080b010030041210152801986908142e44003070340c076141881c00700c90040c411521348070404000701e50a0b0905007040302d02d90340101d42c1e607803510810f4035002e0642001611114105550302081040035000c024001c8900d00f180c541c00032100d40aa1a00c081411018101400b0099080040f0741001020840e4900442d402414140d40b590358039821500c1f9040760b000180400d0600c40013556003a13000c50a030b44611011341da = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 361239829 1250 361238579 361238623
    0x30906031605070b0c040509070519031113231206041502070b0709171203062701090b040f05040203100b03100e07091d060403301409 59
    0x1c61410210504880140720042102d8008101d8500106206401c4103950039a100d20303113018070026050041c0f03141d040110610500f00c1c224420f10507003800c2c030280d1a002c182d4420280c0060001e1243d040170001072081040c0c0041d41021054203040c92110501580000402000c01e00c00b011802c4440490750380c1001e8000b400113600500c0e81030440e5100d110044c01c241e03031595201c072580b0090301c00c8804107403103502c200322440710840810440596000a44240422150000641d0001a0140b4441c804952400c40901d01c0c11040d1021040e50030f1000d515540d40b90202c00c01028501d10b005c0c003a5081108000c80700f03090380500c50007198040d000f80420340782c3d0354007440102080a02c4d903516008a50004807011072a029009130761070050b010b0000c0919140952048500d0310400c0300100002d20110010000c021500366809505070520507082d0200000c0e4041d951006c0310f10b6900300a151007201d000b152941d005000500140f42e9900c0b0b0b907116a0301682d036901181180109000e4030b40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 361241079 1250 361239829 361239841
    0xa0e0907090219120603060e1606030209030a030c050a020301050420060a08190e010501061218120507080d060e1909050309060f090303070f030f030e060103061d12041703090603 78
    0x40100e04c61130250382d0000e8071319107a90b1110107403503521441800d254003002c810384030340c2c0095a1030b80040c21107050451411000c140440e48500c000c240140070320124440140a1040510440701d6155008000b00802e01d01403901c4500c4c5500340700c1c944480e01c03103010340c40145d05141c1c003118541013094581510903520b541a210054040f4240310191036120b40e805002c06009006142c082d01c490f4903001c0b05c840404810390304540d00711080c1080c10403140f0008001c07801c1c19001c1c007240140c51078000c2c0e03159024200a00782c1e1081a9210044d545003c07030000d90109155281d41c05460100040000c0d41000c4600109541c0f000c440034240303030000c00481071607180101c000c04545c007602d4006401d001c9100000781c20b40e04150000d07920380000141180400d40d01c1a141d072071442c3d0508040050005078080300303a0351801400014001d80d6680000c80710711540c0d042050822221004942c0907004c510700c15803864006114400c030221444140306134500703022083d43c0d5022005861070341035958107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 361242329 1250 361241079 361241087
    0x403091715061c05010204090b090408030103020405060d1a010501080106081e06120a080a11060106020a03030213050409030f0906050a02060a181e050c2b050c0a0e0907090219 77
    0x40d100036400300341c0c000364600c001100f210320282d4602840006845515110303020041d614040c8d44944100070310010040010200301c2600c0c1503039016200041c660303891001040440c0c08a8502411046040c001103461000d000d2205050321000e07a03540f9a03990780c50f442520030700700071380d18034141481d00e101e9980d0301090344102c60340c4100000c02840c100c0d10b44804c0241003c0300d540060320366a00c002030018900f60848481340c8003140800080c5800e62600200035161044808014100750b000134900080c4c64a44040e07001806004204104083c0e0320325000e401603401c0843d10740480d60307146001500ca4042e9080c2e800310400e503009815641e40d0150408003d00140f10500600f40040e44080c1c0403c1c01005440c0403182c0000c007003000030000b0b00b465072800002d0100c151207400c11251500b60724804000403c0c0c032030144004000c4503a100d251040c100110406066001031a860300010b0403404480228050f4140109965403681c07591286010391180b03c50b82242c0313880122074001040d00c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 361243579 1250 361242329 361242331
    0xc060c08160510060905180d051806041d09060a020c0a0b19021c06050f0a1e170109060e0d05070308150307122a090e07090507080403091715 62
    0x12a9041d40e00d0b07110750107043c60031607209811a0300580d5646040180010010081c4d461122140000b8051750646420040862007411086041c00724000080d20282d22490181c60281120104041f160518031920f02e849000c11201e0702032603c9190040341005070307113108950300d01038030fa4040e191404860301e8216003480040c0030700b6516140304024200d50320340b902c0070f008040340e0f01d40d280b0300400b000d00210b41a00c4590b0050303482000100900000b030b98036a84100201c401c00c00810b158110f413141c030b03d03410f02521f500805801240c0e80f03001480d44030641c481d040c0c2c030744903040400c10315078102d980995650b200c0c090032022650802c2500c0c0072901810030640c2c880c40394581c1100c444142d4010030b003841c01c03540c0103d51500f82c0303001c0d1004110402c41d0305144000e11a02c403940903a400e10a40e070345080c0314451180595555106030065850500946016006001040c0410304100c030004101703410031a800e40008030301d02804075011a84080782c0303030604201e1004000000b84009a04a00b101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 361244829 1250 361243579 361243583
    0x15050409051204120b0109022701050c0a080a180b07030c1424010e060a0302040f060503160f0f030308061003141f08010204060c1205090910030c060c0816 68
    0x200e4120354440d52503000009001801c94003995451a100b64540b50603072007010b0704240c240500521101d0809d241f02c20780d09c181c03844101900c030104900180140c2d91881070f100309003103d002d0381c01404240041b00c3c2c000c0980d84203941c1c85080c42100b44107a14800b401a003e5102000c0c010041040482e03c12106088000d005860340345990b0350949445240240340c41c0f01c6c0500603414442c2e580c05150700e0300d4036401444900b07020501d900e000700004414080c00d0000a2041c1e0740c1e001078503444203540c1d00101c0504005000c075074107007110080e15140e5408030b118009052348900c2000c40c004900070003140841707070315032140c02080d1141c40811406280c1d8130780c3c007810165244031095103602c0d44050540a0a040d417400d5041038404480d00602215a400480050f0300402042040c02e0b0300402c140c241e55007090300c08080f405080821150b61150b0b24481d5440b0001d9801d1080c44000c0b00d0701001100c0c85900c0a001d059a148016264120407240c0500140c50610a00b40807550071a10780f0316242c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 361246079 1250 361244829 361244833
    0x20405031f060b0705070503060f0112020d08133213050a1e0507030b030d020a03050f120106090905090109150e012a1b02031c030609140403080a1505040905 69
    0x36242c1c0d406a80c40d401031303a410f0b9000e0348102010071050501b0302043e9001482201c20542c1c96040448035814078014031402801071a0441d00d010600c40c0002c00c1c2c4000d60030142d0070001265844c200c0c62007081800481140280440c1d00005102070100c2c7c100c840b100014102800c040f01140c80280100300c01003541000a45800c0c8500080000e1004101a08680580041c15040c0590300800300c402e880d5180b4000d0703001c002c0701c0c1415600020602001549880c016585000681c5004000d0081303400604a05141d0400414803e40018000e400d440d900ba10421850355940145401d86811110180c000c0f000150000301c580116005403444240b9074001140c02a803000203001c1d0082c0001144002040c9001e07441030345680051041c1c07444028804000c507145035a0000317600e03001e0f08001e54504460035000e0000c0c07640241c2041c0d00920902d41c0030400086212410304010f007003141d00f200051002c0000411400312403268003100050340ca14021014201024000181908203081c2e03814 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 361247329 1250 361246079 361246091
    0x1407050a0207091506081b090d02040626210403020111010b03060a0b1329030a08030103030f090501050c0a110604030b01150306170606100e030a060b090a020405031f 73
    0x34101501585007040c000c03011800c2da25250500c02020000043c0100d1f1103200d124840d9000e515007101501c02d145011120a000c81a003403000070004c10041c0e20079000701c48000d4045001201e5070141d6120780019a069806001141031003124800b00c081d00100c84000500091015500c21780480012071950303800010800f0000303000038a03240003164546280d98071100940b1380c44c2000d120303020340c0d002c0a1909028108034180c800c00b401940d2403558000d440703550000b4011742e80802841d910160401204d0740e82c1d585a08005000340c0c00c200300000070034402280019076511a0f0704680c81e0205440181410642d160341d204003070840881016031242d070030b10020001c24070469105000748042104e410b014140703404080c05440c400c3d070006206c18055150003070303c33450101e84140d215004681c001d0286c10326031010b40b0310446403505c80ea014130500c1a8981002081da01035a0300c42c0046030820314030f50f14001401c05034407450261325019041954106104403d14010400d503404801c000f280d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 361248579 1250 361247329 361247339
    0x21e0a090e0c120f061201090b130503070209090c0a0f0302010c03080907170c030d050f1606090b0f0403110c030a06050c04030210021c05030103111003090501150501090503011407050a0207 83
    0x1c3c40100b603500348844403480c8144000340c40d207107018040b8840c401009101192094540f0480084010003080c0d9541c2002e00759800c112080c400c40d14400e60040249001c0c1c14603802141c0e56500d2400c01a029481034031022079881101e6035003400712541655556045102a0350481d070740e020181c2100c0d098440c480c00410f20603a0b4000500c640340c5040010620200c0c0c01c01014a4002c0090483c81840004c00504030459010b608480a44201900031080f5481c40c0c9008001015505400781c035030b15115051048070b05c40e03031510502442c0070303036103001030000402401d0740c443c440500096855444103003100700040d40784d04415031021801d102c10303042613a82d4010902c9849940010070058003c034209200d142c000030a440300b204800e19101d8115815030f07071703400325a18030f8090306840749126001c12034105100c1e803c010b462302e078804000d000001440703c1030394030720b94a070013000d01191980002003143d040c14822340610440e005140e100644810b04241d55551000b504d20045004414010030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 361249829 1250 361248579 361248607
    0xa110f061912060b0a2703030f0e060403080403050d09180b030c030a060c081f0b2a10060602011e050403120e060a1b0c08250501021e0a090e0c 63
    0x2004107034145204c1d5540440400c0101241585810140e0481d110a0380718840f200e4940303424196a41402c00e480e40200c0c0e200d0039217802c000c0c542d5203a40548c2c0060301100300b100e0078000c1c008480c494400c9406112081c3d400f0b0f18105090b009050a09a07221801e0301c125110380c004000040001e400d40740352600001c08241490b40d0005e06444d002e07201d882d1113a1495201000340d034010b021180001a82010703480c0391040ac0340340c0c4a444000308010520000005040308192100340ca220b50350b58a0f40203a1001c0c07a100c0d44010182e00c00c0710328003140000d40c680180120400d43d05032400c2071603200f40c5541108014403000e04241e0800c0110840950302011a00c28103d001c43c10000a042034900448503206958000425071301880c0004a4400c4507a0880031901c0f91030303400034000d0f40300c443d010650303045c1ca07130a4080c2840f20052079407e501813010640c01080108402248004a0040d500030000705128410302400091003d0004200c1d2804c14160240c10200c2007030414900300d88802094 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 361251079 1250 361249829 361249841
    0x150212071b051203060f030604120f0e0603090d080c12040204020d060302030303090a060b150d110c100516080118180609030f0806010906050d0203040602040b03090a110f061912 78
    0x881d10000400d01c03840786004080311b19a11800c500401c0c841c030f4650355403402d080444200005000038031403002841030140150810b88200a8201c5459140c90b01d4031a9a540350070051001041c01400442c4276021550b0031100b160100001d0181e05448079400d01009510502c00b184490b69035003000300069605200460062000c103001f03001d10b80860800701d0071103800c0440349125030300c401040c0d90320003140b400f42c0d8100d85900300d0000c6c10300159122802c1c41e20800301c00ca039003401106c0c41e8001d200c407650b000d94099072082c9140c1802012000703040d291043c0a0250016002d5507944040c041074607600262488562002c5a07080f082ca84e640f56400d0700e50b265401c40105032100c020611407940140740c650301040900c2e005945510301403005c1c1162080360780d0000141d400100040c207200c4250102c030001c000341e1815a96a28103c4841e070f8a0b944c5180046447c03600c201301c601e4252034508112000d5003401800340c0d19025580040500c0424000c005005200399100c034608029003030311440b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 361252329 1250 361251079 361251103
    0x10c0f0206031806060a06081801110d02040807171507050702090c04140f0f041805030406091806080c0d021807031a030712021c0b13150212071b05 65
    0x459001011070030f00382803150007030a6034090065a1800c010349540859490303008904044201c3c42a01c0f20300c446030141c130f071142c420290480002050840a07a0940c000c01c201c2d91002d0079104000c1e1602c0b001251010194101365180d03010441c0c400c440d11311303056026000b45c8281803079490500743e030b8040341313600f14101c400c0c01c491900803c04010404182c101890381c0300d0304071407000504840800080340c603a0b82c0810a03000b1136503440c5401130986c41c0d81c1c441c0e18294200f000c0700c2d2951360f40d8800409608645c000d11410b40d21100402d950580c01d40181411b54072014041e0882c04580c0c428401c1080780e034001030360700000c0c00d01d0100c030108640c010f180c012142560041000c01054039881201e00400100d14007a9001d014108446034079882d5800c11940d049400207408150b0200c00481c0c00520100076141c2c080e03150034001a180c0c030f050500086803182d13505600040d00507008104034010240c014284050413000501240c1c416944030035900c50f494041c071800b000d01d8469901d0301500b2011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 361253579 1250 361252329 361252351
    0xc06040309090c05031e0c0c0a0b0106030612330f050610050c0c1e031b01080a2306010210110d06150504060302160b0c030402120601050a0302010c0f020603 69
    0x30610501002e0b0041110840d45818540d2541c10115040c40c0b06104281c0b0b44c0c0f050903a01340c0400c403481e0b6200c040706c410725001411100c14624909010766003e5081c031560003c240ba01b41e0020300000203a06031000e00c0e40100790a403c078a01c5900c03542a56004c02e640c07400380e51a01d01c0000403480244a03801d1403500c4020001918604076041c840ca0740c070f059070340200b404010b100102c40002c1c001943c0200b424192868042c0400d40e41070100d82602c42802c46916000e08801c00c018124611240130581c80e09a0f10140e440d103d0040103011105c100b260003500c540034461401c60810f4283c4c9081d0803c07018811103200301116640d82e801c5606100d2020005c0f040001c0703e4294a0141c0a07000141c810074000701150728800c14090303c1c80c03003544124001c0c150081880348404041c1c1c04111000368020585138042e140141401c0c07040d90045900700c0c0f0ad850b803144620310b0b440700050700c641a110003070801785032542160019559464000412511060342010610044e20b0320000340d8010341030454 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 361254829 1250 361253579 361253597
    0x62b0f0501091106041a0705010204030c0b030406051b03040201030b0d170a030b0604050307270f02030106020613050619200307020708010203040503040b0903010e0a1112070e0106050f0c060403 85
    0x18143c10707505101c018191144000307210602c030803100c841513148030000d68814142d640c032003464042d02902a590002d820300c3c500030700003e143c40802c0e00851240781328001c2040319a607041d1401030701d81502d00504d50114000d10010300194040c4e4040008120000d00c07610301c0c0000d03a510000d030000e900d01301c0b06503001c01007859081d5039018001c42280d03041c116100c03410b150504012030740da034100380b081c2c1c00c1c2c00507a00c3c1003039032011090001c8000d07450380d000309000f402408807001000e98000c0c0309120062180d40d0000d01c51a44258a44208070b50150240c00140c40d551103030314980c1d40740d0b101c5110040e03549843c082d0707072061500d041c003001258456079626032601c01170103410980319038004e200f00d9004008100002d18003000300c1c0e00f03440003802c0c400e448800613400709004201e0324048462901c01c0d075590000380b001401c949501084200e4410600b40718205119484034224401c8100007203a001c0180203150042c0081c04000c14071030031160a2100b00d9018920300b44042d9019804150303a11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 361256079 1250 361254829 361254833
    0x20d150c0f320d090c030309050402090a03082a0a030f0801030c0e0408040905090610050f01080411040216110405070305070f0c02010e1314060306062b0f050109 71
    0x682229060207075402c00781c504039484044140041c0203109011040305001c4141032000d10040c0a43c1c45400d00504108000304076891705541003c1c00d0b01041e00458841c15000130b492400307000b00c1345811406000584614030710782c0e5600143e08082c4c0844407d600c0001c0003014a814084218080d80722400140800d00e050306000e4890749940004408000780c0000500129000f081524105c03000003e40104590b941d05003100300e40925081318405070304120900c000c00900003002401103000750308548205640b00c003084404c22102d0b8555011506040014001c10103030b00e044540a003001c0c002502e40030308010040c100e41c448071011100310740c001d0010b141c01d003002d00c80c0951004150908100c00c2c2860740e000381c5121614900302c1c040001c498000c4003164131410400030390003005008031103041010000d05014260460301400c1c0c2c0795400000502614001441c54001c2c280542280e202c0c0c07800d008090b003092480468081c9402800d0030340740000d80b0000c42c11031000d009600006070700c0034074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 361257329 1250 361256079 361256087
    0x1b100501150504060f1803050d020105010b16021905030303100e070503070912060f020c1b0621041b03080307030b091b130b040303020703050607020102070b0f04020d150c 75
    0x41e084100765600084041d540c554000c0b04a030103071a0541028000a81c2070141221403100c102d0343c4450445c154000001045000a640e200d0034820340c0007072040360f0729510002503e00660803403c40495840c2040409030800f0681c0004a05c10501c01c0c610154484011134516881520062145208164100200100d10030000d0708181d0603c1e003140341d03003401500280008481e024009244003038103c074a0401000741d00901000400c140b00303645a10740006e9250703d03a4580340ca92000c85055441c001c42c68a000c60440b0740318216424446010b1100c448048003031600148221041c2c015421000545900b22416400940c0700d08451503681c0f6002c80010151400d0b051500c6c015a00c0d1000c2c040c1c0900b0820000f84240c001c406065181ca00110090f5145d481c140d0064950010029010007815400724104003500e009008540d200d440b2610100d00f01d110350701024044c0d0b0f4070700000c2040c000d44c0324070742d03508580000c0c64081d404485403514090341d41790064860116559200e40c035003050308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 361258579 1250 361257329 361257331
    0xd0203180a03050f0f150103110f121b12070b030c03130503070f02011d010804080a0203040f0e010321020c0d03030b03100f0e01140604090501091a041a090d0e061b1005 74
    0x1d50032403146d1a514555904000c0481024941d12520500c1020001c607100c55056500d81139070b000844074100000d2141080000c41607000c9402881c40015582e442200014464111400121704510390781c1d81d0307003c14030f00790406007801c407450784440ca9071004144c007040640102402280c900c2c80c1146248009030604040d0300b03040da41090445d501081a0b030700115119070054228100701ea0320080404100c1c2584566000238043c42c11075800802c05070b480140490580713100c1d01c2031085454a110001c3c1e031140101b20800016807000f6580c0b08103060142c4c1c44d150103446402c0c00700c3ca2030401e10000342803000c12141240103e0362200010341015003809040240121a0001c1051160301030b04451780f0040100281d0040c2c2e119510102040400d5115550158001d150544d041307254541a0404100c16075040d1000c2007032040804c03910104421450240d17000400418040311013844c191000840075040301d80c0288244064921004e61044030b1070804a0070300a00561003801100c60100d0304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 361259829 1250 361258579 361258603
    0x11030f060601200303360a021002060103200d0b07110106060f0c020105031003080f030906060102070e061012060b070b0f040c0b0d06051f020f0d0203180a03050f0f 72
    0x40000800d0b08440f002000f140d07003001410300c0c0171a003d450030101b0704025951000074100c4180c01d03078020500302000314001142620864003070a10922900041384d88240c203010160000780444034121120021301c4050340c460300094183c40b81802551106000e9000844a4101003445041c480c05503000a22030340c0040d1001b03040a6015500c0340f00010890710b00c920000b4148503001006c2000c80d902100094000c55004004513640d140f0354990468540043d01e0942c403503c903e8012a40b0b41d800891480159070b02c160251720700381d4428080191030801c07622100c0902103880302000704048240180e2001d00038100c0c000d903550506150030318030644024088107407041c8402c207020024003822880f01c00c40b9811103400e500d8a01c81503803040140060703800660700c03140800864014044140100030105015000e070307070104401c40341d107030740300c100c901d0302840145c01c10003c4141811594204e40103010000e0070035507e9540700d03030303a0742c1c980706905508140c0c03030780908444490700b1410400140880c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 361261079 1250 361259829 361259867
    0x20304061a011805040b040b03060106020c09010e0708040b040809211015050607021804031805010806010f050d060e0a150b0a0c030302180910030c050301110d0911030f060601 77
    0x10990410b10043c003c1c0324010b16106548403450b940066480b81c000c200180e500805540307042d691580040e542d10550071000f030240d04500000903041e071000600900c00c80854840e4a543d41d540d81d10a14003003401803040718000302c01d1000d02e80d1a1184a40c43c0c80c00c44032109941e03016540d4040c0207140010104002c2500c81c00d0081c00202208102120011a03100f9241c0f00d807100c0c054800100e650241c41e8080107200c141808000c00e150b40316109410302010ba103201100f6644800044035001c00480f0800c2c0802d65848800c840c0740c0c1f00d04014541e09002c0b0000042c05504d803c214081d0300010754032001d59503103410b4a6801c501d0590405001003800e595514a8000a40c0e000f41410b4030320381d4090b0a165001c079005105403100e442a0707510b00e40c001c040c0e034418641000341103501189404151007a0740428800300786410140300c2c450301420110034003800c1105a405e02005440b594900312074940c0c103007031585403c1d101000a1068807011001801007494943c000401114080307440384444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 361262329 1250 361261079 361261097
    0xa020c01090c091a1c03140a0509040606030513020919141602010b1f02010b06040b0a0210020301261009210804030503041101020a0c0605040305070b070b28020304061a01 75
    0xf945e0340c00340c1491346003800d02c0d0402c22420341e00b0191114501c044c22011402e000041c11200703e68001c00914520f43c3c2240c042200c0c1c2e4031280c084048a60845800810a0300114494003500e01340d0b4050b5170051074252502200c0030741c100f664094400700102e19010142c1035081c04110541040c202c041500c50344000c04c4000b00c003000094001c82c20900d207124030003050742c9403540c80303200303402a0001d001c0141c4101d9a4079901e00d9a5140390340400e2251006005919078445080c8960088904844001da0320245280180b09080000c0c0741e0801c845420303100b0000c52140600440c003c15005500a4005281021110342d002d003010024020041c100070b0301008000000b600034050301d8005030000160605a00c00e00d0050b0f2134440e440750050070031800108002a50340d8080c00400030b5a00c55000c3d6032045644104034003e03800b03039550040c80c4480c0a800101000d8030503440481040d100803644800707d0301801c08404aa100b80da0581c1c0c403d484840074449410305440d0b001242c0c0084c079080c014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 361263579 1250 361262329 361262381
    0x1020906030f0a021e030f09060115180f0e01030203100908072a0305010203180304080c1009172a03060a0c1103040906090516020709050a020c01090c09 67
    0x40d5110040020385048030b600301044101405506444d4810f140c4080800c03580390010108009810455480e0700100d200000070740300c01d401145460481d005650700c00c140e48100c43c001d4600300c0450118900894168100040351610600200700034010a44005215415801850704100c16070740c001c1c03885800c000d9403800040a44044804040d0800041101e00c140b103c0300c41b14001c0001407501902c910b03450048140081940214050031a144e00346800300d460354046600c0340102e1203800c02d42c0d00310268003022410080700c41e19900003103292040b07006844036400c01c000b400800e07048201e80c0c0301c41c05002c1d4015100c200c004140c2003104c4100c159048483c0060790b24000140404c4282e901e94042140c3c41c3d0150b0380b00060083e405081d2900e076600c171119000100850320030842c102c2d05010220303600e2840c2c01c2101c0130f008440d41c0542065410080f11501600d00900902c3d4080e90130007103154002000c0c030440070742510400e0f0149010340740688840a50f207000740c0c08880304003004204e8031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 361264829 1250 361263579 361263589
    0x9030506011a09040212070801060306050f04090503090901090f0f02091c021f020606030d0e100509130603060b031b0d0201200d0f0801150f050c011d07050108010503010209 76
    0x811654070088001516038801090b501d40d0040182d4142c000780040f40c0030302d040920000151180046694100c00d5a0340ca00c4121705450750380c424540c21440d00c140380c11711800d168205040050060044902d0103558001084240009074400c0b00410f90f0b801c2c280807070345400c5c0107126094403004410750600c05001d002840c01800c03110380b801410815800c5e07100b15103510210a0f60701d040000c4444c05241144000b0b074640000710b41e0306129006030000c20795000c0c081c09600c1107601d80502201c149a040480603505540303c1103c99500202e0a2615080f0003c10f00070a00038510030880030401d0040c0806161401c1094401c2060740c112a000500241d180d41e541005500d40900c0c1400e101800307050300319540750692105000c14000d50b040c044039943c100386030314141b103603e6407010516a40c0d140c007049100c80004c0700700d000036240356141c0d03151889100a040702412080000030842c8401c1c200e280a0081c00070030ba619900420360410240d80c008000307600405058000b58a0501641300044c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 361266079 1250 361264829 361264831
    0x24010f06050d0207050a0803010f0503012007020d030903050307080d0f05070e0f0a0e18071e0e04030e0a060f120218011808060a0912030c0903020609132a09030506 72
    0x920b102e0703000c0340500038001c0c00c0040380c003030700e401140b12662540c40f03d440300020031403409507a019600f02188580c2d6540c030300c0400a0469815a1001e0404086508102c481d00c09860250104090301c031012020072002c3c00200561881104120b51b80c0c150340e103480c0c081d03900540c0bc03d2079461404080040d030a40000b030500034140100c40b440640c2040c038001034071080c403982210902010358030030001102015001310150b00c0c4134404980c1c409036100c0220203010101000c0360072a42c591242080224003205001e50070510a0901c508101e440d800468050203c50f480040066801079403642d43c15040745107100310b0341500e801036281034000d0454a128041c40c0d0619410403110001000041d400741618034050144c8109403100c6041c4011250301801a894080d5080c00c02c59030b80180040c000c3c4200c01c1101040e40b02e07022030314a1502000a0b94102078201500880b0450300c03154440082d101d80c07011211861b4084034690a8034428808009410060b0010f00050601c2400418800200c1e5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 361267329 1250 361266079 361266097
    0xa050606060307030f05040c1406180d03110a0b01030b06030d05071103070512060103170304020915060f0d090c080d02100b030709060909150b060a05090a03020324010f0605 76
    0x710781c0e9845108003180104041c2c0900045d503490305e401c2c0700400c4a8511800100c1e1200440503405034925810010503100d118000c050300b410025910306207081c0800080b0303180e0301074104864132944a59001c1c0c1820008501120a4110b1400520410142042494120000340c2c01080190584403002c1c0c0144241c880c05000303030181c2c41b0303035454654003080440040c1001900c0c500c04410700e80300059a0b14001e02044406009851210502c0d41d13882040d24420307600206074000c1501c0b03c401e042c0942020311a103640181c070400c1031240101980e401000707221140d1100003650481c80c1000e130b40f00c1240c0e070000307010341d0400d0b00c4240d50f5607800100103000483c4005c0000300354041d200044c2c90095503070b104811042c102a400288440c4580c000c400a90080d200281889880640c1f00102c600d00215580c3c0241c003482540c0645200f6805000d21f000c01034400080640c486c0c00080c500105130068203041780c040d031061440e103441e0700c005a0040050440340041d9605228000d890b83c0658210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 361268579 1250 361267329 361267339
    0xf2a07060e33031602030a0c11010210020316110321100806160e03070b04090902010c02030f010504031d010206070c05210406110303061011071a0706050105030a050606 74
    0x419451004504100809400050240d0001155141c0c00c203026030401c0380c00000710052134900d08180e07400803040301c00c151001c0e03592101180c001d0b03803602015810811040d0451085502121400060784011070043c044012903026010042000815103c5d0740108643d0681007032000d103488121902003016141d20014158a459a52402d04a209410b545c4000f0041c8940c000b44115030b072500110b114880d40c650b4035100b40c030143d64249641c2e0381c194414882d50160810003040f4100596010403c1035105150000803402a600001e01e0020b81e0220604c580e59074105000070035400407950f0b00c060f22003980c90454007118a00103525280700510540030301210140180410405001d4100000c48002007501d02000d41e040d0301c0752a0304240280700100d40500310401d01854000203803481030b203004105c003118001c1880c045030701c10740c10b202001085c41107840200c1c0390591000440914405100c0664944050341419019254103a1145020343c00070201100842e00100c1c070640d015600ba18 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 361269829 1250 361268579 361268599
    0x1e0207030c09020a021c08160e0a0605030a0608010f06061b080a200a06090302070801022701090e0a0504020f0904030e010c0c05030a1b0603020408060a0e030f2a07060e 74
    0x10590601c2c40b0481480041549103030004100d40d000800b140c0a012300c40030034168006120029910309880041450384140c603c60100403c61041d4002e5030b02c14040c0340301203440b41e42c80e08054299041c201a9010b00d50b00e0342424000154014107650a000a4441c035052524280d126107402c0d01c508081c84003000508000c140c10444070030b03d001301100c130010845050401508016004000c00c031400c900500880d01700286452050007580e0281410082d2091101d07003035807241881000080010303040c049003940c0050705100301b00009105405c030b02d802003803d240510400442104803050b82c2d01c206040001c4c40040f0b40c7c02600c520740e005003804c0044480e903107800c108071031905690256502d440307030650742c00803c503a80c00082c044d83c03085030741c1504079910b03008103405a000b1030058401a500007000540841c01c0380c2c00c90f01a04590f0000d40c0d1a01d9110f0300c15040c035a2203880c0780c1ea071a01c0303c010310741c15001485910042c0b44002c00007501095040042c0101051008900c80740304a840e80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 361271079 1250 361269829 361269847
    0xb0708091504030f0606050f0a1712070515091603060203040318060306061b03170705040306110a110601080c010c1a0a14070e03030409051e071e0207030c0902 70
    0x65610403110000e0710a01d441e00d030b036841c2c900c0141c61448001c442041c103080c0b0015035400e00ba0503105076400010005200705007460011070803900680b2011416110b145004040d207150100282940350055001e44041c000e0740e03401a081c40c401928000b015840030150061541c0100e20034015a50f1004001da52500c6609085581500c600480001610428000100e183e0180d000f0411130700640c0703921802c83c2544039540000010007001402086034a00e403d000001c41514a0758001445e00300682019100d49400d011a1085000c0081c04000060440340c07141e003150104c1c0356106070742d000300040d60614003119103030890032540394188008100020200902c02c040f0404001400e41c100c3c3c4c4a14002048038040c5c182e04041041180c0e20340042a0f05500c56500c525480c100500218600740c43c0248940c010000200810142501105200900b042582129000ea0160b036140014440c4d40c0c10b00300200210201c0b100d0540d80001030800c00142080c29100c1101d20030800161107140d48 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 361272329 1250 361271079 361271089
    0xb01050705011122030c0b070f1203140108010207052109030105090604140724030605120d030e0313120317180105010e1920040e0a0f060b070809 64
    0x1940000c06550903c6080080d03454210040c0c808001d201103444015040f41d40255181d84080c00040d00030240b2581c113214101080b4020541c0034828500d1850310402625060b80507140c440200000070f4071284d021111640707042c0311034058140c0c00000c41c540700c80c81d62504c0da590f24549011403003416000103080703401070310011794480c0d04e00500244040e182004c0c216440b0b2a045500b02d0b90769400c0c2c001155a080005030071800c0d1246024011450301300ca05600580c20303500c00300e04082681390070010910b5100e045e00058990300050040204400f130840140035602c04a101178480da000380200301c50407000a850b070b000c6600070b03813a28100d1009401d045401d01c0000c0f81d440440710026003030001d0965030280103203215040100801041c0d8940c0e401108544040e40c0307001c4401100c02d903501c1c0c00d41c0b56500014016488141000708150b0703d07902c0c580c0b20303006a400701c640001001c0c10418001030500030f1319041d004110301000607606150f922105401075075006400d80f00c0118200c052501c0e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 361273579 1250 361272329 361272337
    0x108180a021909091a010801061206090c09020c03030603010b06090d0f020312030906010f120c0302011b0b07020c01020709050403020604080f0903030415021006050f1c0605070c050d0f0807030b0105 87
    0x283c20018040403002d41000c0c003000e82510300260074000c81500000c1c4800040c40754506a03042080300362010f2031151162400707407003449010348115414180008940d500d40c07005040d07245609010316260f117001d10405084075110002580141020080203140c0d1303070350b10408031000350303c5082c00d4600a0b040c00445d18001e10441304ca58046400403c0c41403034500024002d04071004e0000c03071240e039900c401c20030062414940005103583c014440920056000d803420000ca200011441564070700c15441300c503000e10f03041e29101e001d0703002000c400203103503814800c200180100d000244100d081c542e400941d90074000740b002c0d00784000498010442c0d1002d40880300b002e14000d045035107594454407000c540710180c801c1000584203c42e2096072030a1540100c00440e100244100400b00e411414040700030004004440c141b135040301004c0c0041c48600ca1140506041d5480c1019000249032491078a40003004030380c240310b810244441c0302544950100e80c000007610b008240740032034400690b42801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 361274829 1250 361273579 361273589
    0x13120516120804050d020d090e150409150e1f050402060c0a03050a170f071206090212090606060f0906071e0f0b150a030f170c0106050108180a0219 65
    0x1c03050000e0142036104224a0249000344151000700c08090b0341a6600c90303038000c0f840c02051a101d01040a0724280b0b0080c1c7c0c0c4892100f455452041d508000a01220041d81c1c045a04040c5012280e03080003413881216401200704009003c0b002c0b00010100080d14030034007100d80705403a4400242103458601c10786440010b82d00807120300440a14000c0c0294004624400010301c0c0d905242d83c0c1081d941c04014058886529440c101e51111034080328154120180c0686041d02e07050000303040790152005007180c80160b0071400311030411303420190606c6400f91a143c40741902307206600c0d501054500729408458100d48003035a0b80c006281690368028a14064100054800c15281c20301100c04090300b0710620400048940d44d59400303950401102c0070f25002e0304455400c03410b01c0026034480c680100580a0b0303d60f010074a040b48540309840c0e0101010440310b9446903410015942c01c040f845401c0031804080c0b21081d80c0340c1e86801d0740c0daa21004041d10030722508c62030060b80c501908896000c2c3c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 361276079 1250 361274829 361274843
    0x309030c061308070f03021306030b070c02060c10062c0a151508040b0906010f05012001111c050f16090302060a0c02090c03160f0905030313090513120516 68
    0x1079880c8820030321000b140c4000c7c0e01852154070704000c40e0320b1a02c248000c0c3d960001e1003282d6074075160012182112802400c90f00200c042020300c1d00b0003030801c914104070102900106030300c0e09003481c145c0c56403260080360704140c40542101c3c1c40032907606061035015030b951000080d1991600d10f4000c11001d290f0219a0b24201c4d941e03d10100c0368010038541c401e80c0a062400055140c4280c0303641c2e074200910503c910646020014482ca61060040b0055200080b8402560040340d143c1282180ea50350340c0d1b032001203c0040c81e00000740381c02c604204072410080d001c000900c2d24403440e07036610704020010405041441d20800f9224000c0391054059600038010a4a8008046010b0300c00d00080760264440e80742800002c2c0b14100713a9080368032501c1d25421041c400015a002074440c0e6055070042018002600000b00300d0740c40400203842c056410740c020311950341c5000010000ca44010f441c0042440070080580003092590815880079160303850202e42c0ca40110807042d0507900300040c028648 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 361277329 1250 361276079 361276093
    0xf0e0411130b040b0a030203030307030e030d060803070323031b13030308100b04080d0804031b0b180309010207140d140c01020d0203160209060d050105040c06110309030c061308 78
    0x6051960300ca4003080b003041c2c07400c000d020104401c108200030244402503040d0b10030400140024071036001064201510402c076810710764a02020410b031103e035040b4281550010943c1410b040d4000031000c0e27006094481a000d5800c0c1740c1c000e403500c0c07100030090880001488138000c0d0080c100e00459030050b4031b0102c500d261544078a4002c0010a0903243ca94080984d414081540708021007160f0498140c0b800038150302c01520350540320444010000d07018004944241922241e00001903000745200d007650561500d4030b8024040d101606c0e02c074040841d8401c1c400050300381d80010fa5001510032035050750a820305a000010040342241400404070344140318a00d00c0f00400040c03081e000f02090b002d5070115019600126502d01452000c2024518051036090150800c00c2000d50481030107410000200c00e60385825080d01d0094a0840b20341c0d89511041041a600c180c0c0044003103030007000345290002c02c00001e95500e0b1140d01103885450006100c3ca8001c404d0180000105416001c4d00d042d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 361278579 1250 361277329 361277359
    0x204150e010b2a061b0c0a0209040602071a0604061502190510020c0f0d0f12050703110318010e0d050403150209040606020d0201060603141503281109010f0e0411 71
    0x6409050705d180c64996846105645c040f00f86500b50b412807448240100308400194082016510010b041074030720942c200600c0020410a1603118411210200c00c503815080c06010b000484400c1e51241c0d50801c0411031035001c0b02d40c04690440350100c0004244c810050714140700303042614101c807600d030715840082d10040b149408207a50301c0c110410310694031084e4066005940c001c0d00c000300701c00040d4100c642016450144d600c0300d0f4100c000c3d8680020500c02c1c480c040c1403142c1c0141d51528440100309140f2101100034000c0d001d940250101401a0040a0780054640e006901004084100e036080041c1051107650540e0714501000f0010701170503944a801a440c1c07142000a40010350807e14041847d5000f401000d0314184880c2080b121039a441c06030750000390070a4040c2d90b07d801240308401002c29507a01c0840c91085640480b580b0141c40e140000307030b0303581486001c0d0050203180e00401080d150501850100c0e44030400300501c1c1d9440e031828811140c401c030f2541d648a10300c0814959 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 361279829 1250 361278579 361278583
    0xf1206090c04060e091c02010e070e090f0f030307110a17030f01060e1005160c0f090c08130209040201050c010525111b040902040204030f0204150e010b2a 68
    0x20400c1c80c151802c102070340d120b0759a040c010408545124656200303501c580c207411680c2d9106a13003644c65100006030754a04801040c1042150303884101d081801001344264004240f14032038041240303000410f010f4820620b200e4a9000082120301480a40d0554a028500034001d10761030560021602c00388070f058074000c8055810540746428182d140380c001041c030360b02400d082902c101c8014a2500e00146159086a690f4040c2e001040152040500c0030001003440c024600600702040c10510314905000c400c00481d0146406c1d0010046841d06020030700b0b0144402201c1140c064603849400c2d600c0c0c2c0010390f0b40d4031505030b486602d90b1030541000004404844002152218148010510740102e201216030589001d0394020640140da0044040812201d800c0c06840780075001094614443d00020100e8110741c2c030031f48030307180071541901c1145000c3c81540c8540d40303002d0a5000311801d200d103249100360705000780c000c400c0001070503e00281c0c02e41f000821021402c29003424081491200036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 361281079 1250 361279829 361279843
    0x71119170d02011b090911090409140f070302090a0203220f050616020607180801090b09070506030c0a1d100e010909020301060e0f040e0102030c12130804050f120609 73
    0x1c019480c10000f104440c03c0e941c00d50700000d4181e81c4150b1024200070307500005000200540800c00c000700002825600e450040d25111402400902c2180791840c00703040c1000c104040d0050f007904694418401aa45c01000c80c0c0c00ac0d607000001a02c035681c09851540e030781d074400d080880314030280c2244d00400c5040d01e48403081311320034170540e401925420003498040301b42030030010240c3c120000003400944500228400c02c3d95080c824090b09607512010342c2180d1900c101502ea4044800c204a0590b00801004c0c005060039140c1c0d919520300340913160f485002d880c0800701000792040740e802c5030700c503080d800040302180280304e004844908040a041c601452170818080741054500260b503808510a4904a83c1c032034440c2c03504e5100b0402007040403030303c0d0150710758825030718590a00101400d2001d98414642056000d607510403c90034940381c0e980c000c1410120407006003919000500c01c0d401e40302100c006a0740500b00c4100040017403000c1e40200800700b458405d0008101d4484e200003000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 361282329 1250 361281079 361281103
    0x204020310142707020c061303030219020303040b03092a131e09050708030d0e0601082b0c1703010501170f0c09270402040f0207111917 60
    0x1009035150b2005100e881483d240041d0b011007050300200e1102c10030182c01a5001c1c0e0184180c4500c0d100c803500240c1103810410a130981c0065409060040640400c072181a11140c0d0007006262411a40000d0b5244142d000d01c83c1d41c00004004508070039020801406c260b504003194491072081840c5082e172985800c1480c80c031898280c0661700d81c03c01c0c2881201030403418046801031146880e60325501415007007800b20783d10310179104000740c0740301c040c406000c5220308580081180749440300480c2c03501106812a4a0b41d812540703411520b21842c84c2070b14103021550400b0b03441c03c1c0c1c5051050340c000c3c0100e200275291100c00300070880c902c0c40f03c8000310305030b0740240c941003625000403038290501c81e01215803c4c03400350b4100100b40700807062400f400c05207400070070302e87d40341c0780f440c40b000b60b4290b602c0c100a07201c2006ea42031008616003801044070300e614040c1c045007024625110b120007503088201b0706004070079001108511075012120318001c0e06210a914004040b5014240c0da80e100b49580 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 361283579 1250 361282329 361282349
    0x2010522080a110603062d06120603010b10022107080c06060301062115020f0d060f0e071d0114041d090307020a090b010302071e1a0610030e07030204020310 69
    0x440c0b85000c2d0143c0340a520042d1120100c1f8000a082c081304012019a860030200410030486241c1e0700c24008141c182e1850048860030b083c03d070141420740c1c44c00050302e4032880102100010880e400030b4a0882507c030080321408050032b140350582d0354414190301402a52002901001c10072002800c580902c03c107070000c00c040e5a403000d5080107101004020000b110b1001d0413040455250300781020784031000d0070014a424080368070707810b055224144040c01e036034417000d0800000c090209510024840d40700c1090592034034240040c00081d541044580524009400400d641d00c1811905850005e140720555611b807518601c2c0a214034102e40e12042d600d8140004446401c04003c1d40e5000340d0203046445540d0500c2005000f520304410031038101a803d2100c100132410380300c2070074580c1030300105129600559040c61032005050540384100c1c7c0d41c900c070901ca21a200d041e000b00503040b035407400061406a208141d41000313183c0d44003a6105001000f0b00103031800d004a07170021118801c81d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 361284829 1250 361283579 361283603
    0x1b140f0106060207170304120f05100207032a021e0301180209040828111006030c0b0d090501050901021c0c020c01120b030a030201050a0e06060a0302010522080a 71
    0x842401d0740e00038019a0010381001c40d00f0480c203024100d080d0101d12000064a0a041d143c1c540762499400084081da02800f05180b210700344002406459041240b2f68425864459180c0f00030b80f814070f486248031036145c0a6036900c05400c25150b03125542a9000380950b031902400c0501408003012005000d20952800c1540d110203000541c0c1c42003581d078042c014000586d41e584580b11503170042041e0300d9030b48480b100111448894140c001110407007588411031440c00c1200921b2600350038040190301c0d1031500c90244042035100108504581c0241071171641d07010039840c42d83c007810740520014015803c1005110142c6c0301900a4000d41c0b03e2855118043d516030003142c000d8031180650745025810040240741c403548103202d20540b0382c00d130190100350304010001203403508103004401c0d80182d42d69001e020500d0603c3c0910070b1081d01c144000c0a5900700100011701203141484001d041c400005104900c0190620030041400507018029030040c3d0754651507500c41d0941e04c000c80394401c03004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 361286079 1250 361284829 361284853
    0x90c120123010e0403080c0d0606020307030e010e180903130e070807051305040b0d05030310170a020312090102070e07050c160819060f06121a071e1b14 67
    0x1081c2412160b038600c0000e52501d903600c00381d83c2080007400d6000b1740c110400607100085514014400245910360081d5580c49440c14002d040544501100c1e040013201840440d003039498508000e0a11001c040011081d104c0303170307091495442105080303000902d00c42c4001403064004401c242c400c02039900c44008945d10309004590078480d500104d00c0406e2802c905100d181860783c402c83c40d2000107040001c001d483c1c0e864062071500115034542c618500084280400c80080689412700c01107080241310140300303540000d84807648007100128031100400c2001041c0e108000c61401403500c161010320501300120000e1495000c610881c481c0d00c5038840c0c02c41510340844100d402c8488a1015281303e5003001e038845410407040700709988483d113507011018003644a1082c2c100800c040c801800e02e9071102d140109a022840b80980d040c41115802c000e0031540000b50030406c0c5400401000d984440000e0540e504040e4140d400c01882104204800f041070f2101754050804030074088070000c038001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 361287329 1250 361286079 361286141
    0x140a0f05072a0804170d0f2309041401080f030405010e0913060c022401080d08100810020322260d0c0906090806010b070b090c1201 58
    0x341c1c0e4007000902c0000101900200c40d11519251111989111146450030340b281d100641244e0064401e040c4d0190ba404801c02041050000c40785071030030840704041114402501925551a907038030f05601075980e506040c06044125071181000504c20018104180ba20003403d010034010201d0b203201d8901c08404009001080d50202c8605070745800b40100080c2c14041d446102038540342292850700ba15030f00042650041c2c10001425500410944081c0319040d8100a000281c103011241c20030014408603001040036040c81e0071a013804d118139120324014042c62800369114101a0183d05591441c0c0f02e0306800450007041401c1e090380440f180a00e99405900b48482e00801e090b034041803284c01756541142c0f0308801c034282200207041c4038041c011002900d09072080e800004102c0d80080c0196504080c03a10007030080c900c010b0210390b0420400e00c9646c0f04000d0090402ea10300000540381c0e040030041000d480402400c41c5410102a15255000c2e140d00050041c02080f6803051510079010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 361288579 1250 361287329 361287331
    0x4060207140906010c060207140616080408040b09030304030b04030305070e0f010801050f0f0a0b041e0e0a18050109061512112b03050403060609050631140a0f05 71
    0x610400b607a031100401520034844401007203a62580038070841011603c41081e00000b00510750280095142c000d80c0c00084401c2100030600b400549024040072411400c1036030190383c031130f102a59030303441d41c500060b1550040342e000511841c1060704200805038141c0026000b14032079114021a45901400c10849100300d0321020300003607a5000411251030241090000c1c82c9016161000044107480422400fa075250000160034800040801045100d80039500100d901c0200000889041035840f4a08030b0b00607003200d41c45e6480d0020704540b0072081400044255018001b0400c0344000e16040024041541840340000f2254a0016100100c40b0320550b4181e44028640351589a00c41005105d060a16104141440401c50204100f454646c0082d50601948580da210f500d9840c2c100182c2d002904980262030800f001d1240c0f50301c400601c055480104084442d0000103800d07544e1304807040724141000642070009000a0f480b0050000d03008030845034051005281200e010000c1d150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 361289829 1250 361288579 361288619
    0x703020606090c04050607050309150415110336010201020301050a0902130308040e09010608010b0a05060c12040906050103060b091c0311011b0324090b01050c030f04060207 76
    0x140c0000c8062420591403079000c40e030f254030b55040039121000700305641c00c030703603001c44440e40001342c40042d0f440c0c141108100c0c801421440781c40d1a041001a89402940c0b102a500307008a031001212803080c1401074400d09074424100b6031611852404c41115034003416981c003003108003801d2540b00d40d403060007201c1c103850020b001030400501d805854002544071501400c0880000e910110000340c40750018070090411150302000c5041406815007190690303480000168540401100c1d1074440041031400c0740c20440d0881c3e141e1100740100c03401c0189035441a800401c1c00100828403058503489082510000c2e42c041058030b0700c800980420344281150b20b45d02c140c501c8145c542003000c0001e0040454801c0c5025100c09a11151150030340e200402099512801118950340096051041100e507540c414062030b00c5010f265a8140c40107039900950790309a4564000740c1c80307a40203800f01d032100c2040301c04403035807001c07000c14080309a002805481d005005525002480034602c01c40303120710344 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 361291079 1250 361289829 361289833
    0x140904050a24030804150203070203060a14090601080a080307030b03010c0f0f050c0a110d050a0b010911031e130206030421051804050a0b06070605071b0503030402150f040612060b070302 82
    0x15080114200200e01c18461b48003c520080008000688040c0886401061514000316080c1140f21a002244500600c00d40490b071040d00100320031000081c0c1240000d8002c02c1407540ca4507900c600b240a00360400c03008d0b40541c2015003c1150541c4010180e0f03042c5071726a242c5180b1140f00341c3c12911845070820012461303012844131000700f01c2642c40d0310014103000f0064000042243e4440303007444118801565501f82c030400420215285020b0300106141d6440d085280d450035481d41c810600080c2c14089040e8030000010f0048001e0810365241950000d04040d100e18251521948550245102c04031080c1342c0c0303840301c0c1464080c405840d0102514038280d100302448005020051030020032107540c031602c5101c4c0003565155080104056402448081010b103000c4602400e01607804100e40b003021041140e04001c90400b200750381e00315030f04454201c4400c8907400401d080d8081c0b91a891001d031030006000900c103800c00081c1500e070011860078040d0503a100100d1080d4055080054003603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 361292329 1250 361291079 361291087
    0x40806130b06060a09150c050709090c1d1302060c030c0a020301060503060f0406091509030c0201031410030602030901060b0a0809010e070e0403050a090308040803040302180412140904050a240308 86
    0x174108070307600c41d155100914000e4003161f06034441c2894400243d20508419659041800074001c404c0124005450a002e080c05050050044a13582c5e0070024000e2003480039002da00c0b0110354404086507404495001102c2e21160310400d0303951100310400049102e0740c6080c81c006003904020036582c1c400c810a5200703086a5469443c4d500280481001c100e5030129819503a80b0109001c0c480c00c04014081e0350b581400318054030015084071800358100c05200b10130020000c8000c0d04902440c19241e018001584a840c2d000e40507024116070342000741031600206003040d40ca648651300c180f0461000c0028800c121654640343e45030303180c42c05074055156030100003034042401840100300d803030014601001010b646c1c0d140e035141604650080c6d81d682c1c000080070025032403c405000d50317040107800064100e00b02566903661910742030411209000b50503207106652001042910b058100140c400c0c065880c04102c00e4000b0114002c050702e95603807800b13081c2401c1950306034540990354071034611868 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 361293579 1250 361292329 361292339
    0x231e030606060d06030c0605030109241a042309220206071a09030a020d0509030703060c0516050601030b01170643020105160f1202040806130b06060a09 67
    0x564000b040c10000386891351000400a140c9201000041c14147c1e14030792294100790740030302911514100b80c2d408008988610280415082808045400c00c1c060204a441d03900c07134400303090060b6404001984074000032903422044460164641c40030860f0b0f031151564460780c0c8511f490000104900901d11104174284c0181404c0009080241c05480e040c0401460404510103a80084944410641021603c0c00c8010340401c000c2d001c0302e03043d00340300707044c403c0007004a50340b204a032002034030702070711070f1500c420341e50040040300e4070140d039025a0030040382c0c1030801c50350b20340c030a12048884c010000000902d80d036200d140841c5101c07002003c0d202d10346442e00c6d80411801c060844e1461445154078500d000040302c0c246c5410b910130000b12030000100000c01030308460000304214010540c10214840c0e071640319961001700f400a00304003a00c141c1e060140b100034000c6401030503483c810301050043c500080a034400708103100d0346c0b500c0c6040e070307484050100c0d5001d8120040c0105015280501c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 361294829 1250 361293579 361293589
    0x17030105190b0d0f090506041401050703060503030d0507140406020d02120a27170f0708060c0d0225210e0a120503130f1802040303050313020109231e030606 69
    0x40348100d8210081030045d0036407180c5007080b40588044500302c0114041c242c42e070b0380030f0042c20341c00780003030900f04040e03494080031070380740e11a00e070000311603076500d4000440030b9010341c2450b280c60500c4030050740c0fa9502d500020f0340c4c0b5200c00c14520050300ca1540e01010868000049402081081e641c0440c210b400c42074103020301003069400d407604152214049040003198282c588503804100007004030348a122041800c1400582040e8440d0300f11008012032101484111002e0301143d41006030b070f403400c2c42c80d0388000d01107548100c94101c0035141620240721000d01616841141c02e00716140808103410182d520300f10f5a0f040076041001550200314410800f850068414050b1050340d1038100502040500c0f0300c1301c0d4100e14441e008a100507c065101071040c0140682c110104601d0142180ca02400da400010440341a1503402c0d211030085903c5810100c000b0a81e030165103d03031b01c070700181c2200c045071000c0d0314a02821084080724100280020001c203d040d01401429040e02c2c1c1805100f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 361296079 1250 361294829 361294841
    0xb01050403020f0f060a1205010f080c010f230406030b030a0c06111212090d08150409050f0601080f0d09180213030b01030f1403070506010e1317030105190b0d 70
    0x10b54480085003140c4e8454403000c0040c50300c1000b965942c02049034401450702116010780101414000c01041800514000a00104844002d0030080c46480010750100c03840717204003221a000310f04c0f1503402190300d452040500300340c601c00c0d00c05008120700501855a03810031044040c00320485141d003048224000c00c0080c01c4d01000c1ca003502d0104291652180d4a0742c000740070042d03000d5000003000715203482800406030220452501c4078860408179141230710001e030310207032621440d51412008100b000810610010b85140800d0720000c0da9282409604d412059039000440d000b00c84108444034818040179040da2080300b048481c0e41d40054944000b034001c5640008261076042000c804036400c01d003043d000707500c290340800b43d000039850030030030403c003106000b6440c0c0c0c000d0250074006040814468151050410514a681c0c0c40c030107041002184080050b000403501e500d0780c0080311003100110b043c0d501c1504c8413980010829844090382c0035910491514200902c101b02c4104401e410403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 361297329 1250 361296079 361296109
    0x9040b041202250314060f010504020901031d07170307020d0b10050d11130204050607060902040f020403060b0316081c170f18030a09180609110a120b0105040302 71
    0x143d10803040002192005140e03003202040c1c19041c0300c420810001c103184080d50108041d406041d440c248182103041030785060040e01e105980120784c2403856482035010195841484a05d04a0008100c001c1e50711911a4026106a810001d03e841080d0f44004112000641e001d403070004107aa0b942c41d07180100502030103103011103148120000f030a50303a51030351121540c004c464100041420508101082d820b0780c01e000c1d1014014442003210b941c4200590f0b603c40e81003040031a002e0f10b02e00c0001d00406560b4502045288086404418031015034014503410b001582142c00007848503d8000c0040010312950140e0b40c04201c0d42d005228079524601800d071101d040070860440c82c40420ac98444c41110690400e05807881000f8800411354660848507051401440c03503e8800300d00209100340030b0007481e10f40c82c2400d03441d0810144560010004001c4224200500c00848407000b0f00c542c090003401d000102503e0003090a051944100f40d4041b9050312060b01e49450f40e82801000711509600c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 361298579 1250 361297329 361297333
    0x905061f020307320d0206060d020a0b030a0f020c0c03100203060904020d050709020a0522030503030105192309070302040f140112060f05011805030c090c1e0d0b09040b041202 77
    0x13540c00d045007030540c08403030000b00c44041c3c981002e808030005c0c500000140201e2058a40fa0101c001584500d0403100c140d8640484147e0340341e90320500352002c3d002d1003610a060600c00a40013010349000b141c1c0500340c100071020748504141c0390707884005a010646403180e000300e0401c00702e401881c00c201000440b41c82907041c1c600940e6a0704900040f40c0100c404180419400201d60303000e20000c00b811016000c0003480700030f007541507403600ca03600c3c0014004d8a0041c00c0900c03954029034151000c1000800c07818208a10620034a442c3c20243c02d4003060082c011031440303011880b254000e0003a42d05071a4074144040b4600c6c50b1001c0b202d0b0002420b0030032814045e0300c40401d0048240d9000b148042c1c13540745102421a868400014082c00d507003040308a0340c01921500713110340c0c1c0c4c0202d05d42c0c401220032074a4900750f45420446c2e00051003040e15000c80c050010f40a8280000354174046c0a486241c100e04200c245030a00c1413001d0000d044070024852906000003900086080704c003100e40c8030103441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 361299829 1250 361298579 361298633
    0xe0402180a1a010f1e020708030403050c030606090108100209010314160e0a1d0703110a02060a1d06070810080f06010e0703060501020a140c09010905061f020307 71
    0x210100108040d60303409203103600e51402280c81c001d807403405074250350b013803800f500345a2404200501600001c070712489401c40c903480034081c0382d00c20081400900141e41c00d4941e26903923851b2440d901c00340070940501034095000001c04901d0180c000300c0c101c681030740280040106402410000354440c822140c1410b0faa8042829582d0301d0784507152040e5410f5042c0078078003402c400050070303003a58200b80798850b4a82c40c90a0004200345007442c0301220305d1808500c00323900ca0f60400d038054004142c42042030754003c0341c03561401c2e50004e00c440c0904206a0104200f02c10a0300340c0c1421407408814540e15402480070072590740c400c1c151598025813219005100e982c032401c00d1400c0c05071031840c20441c1c1c0c1c040c5006000d02d8007244101038200b5000c1c02c00f006024903241c0081c0d124410f40d20301504000c061066114400e0701809407198200000300304030b0300c668441206000078081515040d0007200701c421003e003070605204101c100e00d040340d0011803d046241d585e07500164a403011802c1c04001846d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 361301079 1250 361299829 361299859
    0xc0409080d0e100218010e09060607062019030f02040e01060509010c02060d0905061003020307060c06090b070f02010c0914060702030a050f0d08160c14030c060907061b0c0e0402 78
    0x710107417901ca1a8180481e805980e19800189410b0070b0005c024850700c0244103101c440d07602c0c1011104001c1d48100041000c8103152000d280012400c081040509000640403042061000f203034400d0300b1154804003d10000c00710900308030b004030b0003840c0a01c00c0c040c0050200c14082d402504c02058145007118040041e40d011844c5600401c525020745502e0f002410108241482125482118014010303d502c0c61900001e9079802075204032800c0c825900d00d05c0c0107005190b003041c50b0164201103051384078103003d00000c15500307020002e00015403818a00b005141e1081111508880605c0b07050315940488404115881e80501c008990601c51508402c00080080c4014002c0601280141c20707010245107001d040c40d8001010304094400c0184482825034019818005843d0040a503100344078043c07500519600c205a40349005214000810804641c0001d02900366000360303807001c4071005402d07003a80c0c0302c401402c402001c2e0001c00c9000d0080b5148400b41d103501500051460403170701516 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 361302329 1250 361301079 361301081
    0x6030b061905090112020f09010f11010509070311010315060e040906060b04090518070b030a06080a0b010510050c06011701060e010308032203051602120312090c0409080d0e10 77
    0x1e034900000301e640410050399035038200f0380304000c0c0401e80344107500d07211249040118510902e450641072146001c22512020310504220744c3e2041c0d103400030050703820155240c95640085200484419083d0300c0401c90035442800b6140c4465604151084050b041940644900600345a082c0d0002c0d42c03482c07503602144503405074a00806c1000212075440d030401020801fa01c000800002618001068a03038000f040050520201c80340784401c2604d03030310f030150500e016102980c8003a4043c03042d55805000d00c03c41004a03412280c00316007401003000a401c080c3c86c0d50050707804074400b03900044010040398040305403101190600d0000040ea1546480d031b9640311203420703002912040d4000c41041070365500c1041c1081401043c09185440b60120741c2c0080041c07145296420600a240c090707030301103450b4034901d0904c00721544156034507015074580c2185201340032100c41e8020303c0340700c04a080d41c1c01c00d0f00c1105c880a070040c04140c82e0a030100d040d44040c0100886401041c800c1a12010002c405 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 361303579 1250 361302329 361302367
    0x90e01140109060e070e18070509130f0b0105070b010b22060e030d030606020a080904150f08012f07050a02120309040b0405010302011e1110090b09010507080a0b010c0b0906010806090705010906030b06 88
    0x80c488001640070133a654802c11070b402418140d062100030003071000030905103040c0030304540860010039941e40d60a120303800e0b100390101455907024800d6a000c0ba5450300545405400c1406404031103008009400c11001e9032414461035001d40c0050041c1d0300802c5004000b40800100504041491303071111034000c1004820794028140004c40b0941440881001e002d0750380400002590030f1052814400302100408544688035001311000502c40d04002e42808808009a0020b04144c9141d0f01500255121b0340b08190880c03266107010040d181c40c0c501480303058140c2c5e406075120000c000340e10b03940400002e2105028001d22541e0040c0180c03103081004a9002c103096200007140050f01880c00c94030524008c1e01100c800e9040c9000c101c101603000c002c4580c000b8030400d001c2844803d47c00103940c44903d80c40007278045051102042210040000c015040300c080300c040f5040c030394821203080e0b21406103005490001d1403500080080c18421341166141c0c900c020030b040e01d000424009000c00ca25 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 361304829 1250 361303579 361303609
    0xb040308061903050c1c0b04051608211c06080d1d130b040b06280c0f0b060f101101060807050307090e01140109060e070e18070509 58
    0x2040c00c0081a04010040e000540040c010201d8403506507a14035440b01225600d5600944010605102c10803504204e50966900181504402e0800d81001600e400b00e84810010750034107000005034030310002400c450000803001c03940c1d03a100d603960200340c481d40c02802c19800300c0891942d100115106842218001c102210044c4007000e040000644510f080b0320202c014011182045080f40d1249402d036502ca08000000090f070000e03400001c1c000b4100c12480c1a0490400300c0d041a00c40c0c0b900032209000c3e000f002100c0c1d20400f098008450308146004001c00484441c5071600c0002c1d0b04500554022400070310b00342a41c4d030b48001164480c00d02503031a038001801d180c09810300e100c080c41410060309040c406005581d0a01c00401c1d5a900644a00007185645d40e10320350000c0005c0d40140100210742a926403256918541800039066038054061088024808034503141c2c000c030035000d80c028003d000c55050702040850000d203820300a1113841440010030000c0c0c2240d403416010000e0350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 361306079 1250 361304829 361304837
    0x30917011d1612140d09060e011d0f03120c07211502090a090f020306011806090e04060b030102130305010513030c0f0203070b030c040e010e0403200708030a0f0e0411030c07020105070b0403 83
    0x6071504c18020002915450014144020b4ac2443c1c00e402921507001c40b541a8140e804600740c8182c000031900e020a652401c100d44080494160000c19010601034121072451141c14000204400c0b0311000d10302e170b000d00410396070b15151200312041480d00a045408801817901c0c594a80e11426081a2018055001072081e400010030130a983c011034211f00c1802c8c0c030000542900d044c05405002540c45021781d040d030a6011000504000305504100740b1014050001d6441c3c07919600c108180160314081200c49500f85400912451580c8000399100c94042c0d40d442840d402c1a00c2e03810f0305540c0c00006a8140c00b500034003040c0e10a2240c0210f0050700c29807542683c40345000d40296070902d040e00a90503141c2504248008a60b002070203d91101c1c00780e00c03196203043c242e00514603040c02d5a000788214080072035080c10244d0000b40841e40c41030940c51791000c40c2c402d60300300001c4134034001c14903a290100344041174404070148040c040e450300c181482480c00c4600c0d00c408210f0b48046401301c00023 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 361307329 1250 361306079 361306097
    0x1302040f02070213061827030c02090115080c1b0a03050c010b040b060a052a0a1a060d2004020408072907020d030917011d1612140d 58
    0x50070309424101500c4413100302008504d040080d24071100c1034900d82c1140c041d8071400b40a4034001c0064621508041380c1940d000c0140251a0240c13040c501c004059125440e020b0000410148042104040c008030390f8038007000782c1e1000c1c6a090160428804150a5202d29114042e04c0d0010401e64003403601a44800351a040d0f040c00c0c2500b96094402d4250056040246485071620384009a40c400c5050741030141e00c90100e4a00840308242c00b40644080c5412818002c81d81c0401003007030b2086500a0402c4c545402002010702e04081d0705560540d044101d142a00000ca40d401c039010489046442c0c00d00362002c0360000060582c3c1250704a1003040c0c1010904128664000380700c40c3c480702c00c04880d0b020021001c1d0300c2d100180102013019000d12800800c990405100b60f048074082c059500503071420158104140e0b00800c0d000e51000d6030040c581040d41e1040b180020299141d02e10044291442070601610303000481031001e0841d4000e0280e24034042114080c00803204c0c4251a40e654082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 361308579 1250 361307329 361307333
    0x319021c0b01020705060909060f030d0c051603150e070902130e062407050a15020901030605010e030a0611070804060f140f0729160e03070b0406081302040f0207 71
    0x101c0d0200110507056600c403800420542d01c2e11400d0b180580c0044a0991131070f540e400c041880d071004c100d0300540c50f000301507018500c0c58111450042d1640a54101d07001700710360441103200c0c400140005040c0c0c40c4202c3c102d080036105500101e141d0021081903500aa9032000d00b6004d0b6004009001803d10b5040010f000c9201e030145143d44c0a00105c80c0c0e40004d050720550044c00101042525545150014419040c488100201c400541e44078004c0000322a104000c40000e4001c2c004082c0000e05101000900c4c0d03200e10300c80b525001c0002c000c0d15400a543e640c010050000011450704284140312600201d520480a0704c0201600d448002d80700c20b8600c801480b0500c1c00b20484055007040c0004218481030301c0640320015030204880c2d106140348000d071070020611015071051003507400c0401c07802010505001c03d840d004d80d198410600302130380400d900c1345050b014203a00741506200402c004c5210340300d142d0b080802c032506a00182c0140e0041800d8804544044c4180c42e000614182 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 361309829 1250 361308579 361308581
    0x2208010c0e091f050d0c120818041b11070f0e0f0109020406120c05160501020a0914030c0409080c060708010e0a150902130f290412080319021c 63
    0xf0780000f440412100c0b10000c1c101c01150192a401407600486031074481d501001410464034020b0140284490000c90316858540981d6010200c00d8081644141c1c1200c0d00c3d090500841c0410214040542c02c192030008040360300d1102440150030503c40d04c4000900c85a000810401901c5165071071205882d0071008440e241a041c0c2c4424021441000100002944440103000141c1c01701c20124031000380740000c88280c014510340f0310b811000c80141d502000415401400e950304582c680d01412980c0303800035048842c824021740c4e0160081c004081039446d00c0c3e4480c21042d17100f00445e9080c800905615840d0150483e200c001254501005001800c4041840d940c4015400030500040c000802d0a440e0083c0c0ca1041c200c0b0a9004039041c07440b5400241c88002400f40c145281c00401d540b2400d81000b880101100d80d4400580070781031440000c0f9808482c16030701180c1c1000c07100240c554402c88143d000408402d810048000d8940100c1013a000604280e00ba01949001429811402c44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 361311079 1250 361309829 361309831
    0x501270b10230f090a290a030b03030a09080f07230a0305060703050f0606030606071403090310061a0408030f09040b040e0a020312030106021207150219030f0c052208010c0e09 77
    0x801c0c00f41500480481101b81d02038006000c200b60b01e1000d858401000c03040d0060189070240d00c0d07050201045c13500f40c50340d01801040840b28001c00722480c281040c60f00a48070300c0207000b6184045496200a22003003d0a541d00311540c01c00781c568064542d4a40b225030408009031181c03000070b5295414461000990886150420700c200c034a5861802c000c00080c0d0644140c100007020908048c0c2c504040100502c2985d0b89402c02505455100758001300d40c0000307204d00c1c0204001d1418021415003001451410380d01034410032402540b4100140720ba18503d80c1003440d51662094941e81507500d82c1c1c0700d074012130900302e0f86140140300000b420f104143c1850180c03003000310321f01e4080c03004000b40e80d40040d10008500350075100c01d44d0b81c02c06040c4103020103100c20003800280e000180004081d1116001c603105900107503020848201528507040130303940c3c4550b240c0002071040c0003d03074052107101416070a0000c90410109140c2e912240b03107003900c0344161600d002c92503c05405a890034880445 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 361312329 1250 361311079 361311089
    0x1602120f0403330b061b071802071e030e15090a151e050301060c050c041515020714040c030b0a180c0c050726010501270b10230f090a 59
    0x5000c030081d0640170524501603003503070041003083d1403000b074180f0800384080c501800034000361210300842e11402c3c4029500c40c0303504542000e0840d1500d0031412040340c0072200c0d5035040c0d841001d5200d840b002c00c680f8482a0710070a072500780401c41c843e195900c03180c0c0c4d44000c040c6418415540307401204060003031540c20150503054944144a190a0342d882412131307040d6611802c00060311a041e0825600c0e001c0308203031f2160814600a0304003040e40c030301c14400085401a941d000c0400031500d0040f8bc8818240c42149491010600a0304c01407a094218605141e80b03854001180c001080020744070000c10303409410b010080b141801c504c42c10380e0280485400c940d0800c240000c3d00c1d9501c0303941ea002d5030b11519001c0305100c400303507400501030111828010006002802256160110568034280000d100c09001020300d149101100460182c2144650000c10201000110000548404003080000c454880c0400e042d030f140c8285180150203243c9140020035107514040c8140030800e0319036002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 361313579 1250 361312329 361312331
    0x7080d08060315010e0703020706110903011b050d020f0d0c030b0306060406080a29010801050106020c12030306131b0306180605130207050a1a0603061602120f040333 73
    0xa8410400b8031110002d04480d08540c000305d05607940e16085000707014a89000f00f45906021a8100f904030200252404842c214001c0092041101a07201014442005840400e000748800100c0c0d0b4010b5001d440041c1c2082d540174608811241d811040b604101c1c1030340086641e0b480c280400e802c2c204200b5901031019101048080d00304210300390744402a010040035404940000158002c3d00340c00c0c2441c00c6849030484820f540c5888001f0301910090041c01b00611800181c04941c1c5401072001a62681d403001446c0b4540710101448040d4a0406040d07204c070b0f03213411020032090024041e101c0400000e035800500203042440500c10341d2201c2c0e9491a9450904100380800d0383c0e8070500a01c250854100180d441d0485e140840c241302c813200380508181020380046c18940184801244501000c600b650025030398000d40c01d15103003102d4001c6005a0002e45030007000f1030b0460051204503180f400240c2410750f699500140c6c00b80074100d40e41d8402c4071102c65120420b580b22a000b090010240c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 361314829 1250 361313579 361313593
    0xd060902030c041a160b010e070c080406030c0903050f2d06011e03050601030b06010f030510060c03031b030c090b040503031204210e030c0a03021507050f07080d080603 74
    0x200e142e03540d00403030080648450070b841103e4081d0b4030b01c4084601402d190461800e20355464105062980030921503c40c840c0300c400000340d05113218954ac0d11a03550700c852094100b50030080d08400812640100c3d109000a03820044007041c0100300303100340d2013110320040c205068040104c03020101c0401c00c10307010840e05601c6000014021508a05445100010000e8020f48903c2c088a200841d0b0001d0920b0160500110900001c0808076104000a803074014042140303c1c0c9c1102210301c12100240211a064814803040344540d41a40c3e41c01c1c02442c0110300b600c521560030701003000c1e403c0310740b000c25a43c00f004d6107000d4103c0c494600810303109203a2810940b4281c04251248503662034030545501507400101080050704da80310904560002c2c101d160a02c2450260804030240b100754420720036806000c00c140303440f001c0c046c252a405040030400490032004080715400c8038200310740c40c2c0034480030500020410000c0b440245400c43c000c3c001c42702210f0002d404917030003424150003504000d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 361316079 1250 361314829 361314841
    0x11d010b030f060a0312030605010801170718090803010905040b010605040e190912020610081b120102071403070204061d04030c052811040203070f0c0201030b060d020d06090203 78
    0x4003669804042c203120003505030b90340b80026408004a4000400790906510b44124107941544900c09403002a02d6048071640c844ca4406918061451241141d41c8016001d000820030140a0b205403500b003000400c0107450341c0d075402d030f40d50000d0b0880580340303503517008010510030075030700481c01807025003000d500e014103000c0508688a0000d0100c80070b0800489400f9150b1010f41c0b1030300115801c03ca40944a05100d10000e48901d0180c07a0f410312040c4180010500c0480450250a28030866440c500d0400341d080a200c038800c204601d072074107954240f00103000704500d14400c990002d0712102440c0c2e1400144100400c446a90f00020480045d2010701504a81583c1d5080c0d045601410111901c01c00c51030007601e4040342e43d191492495a00200c4003240004015904410348107110040114041328180412030204440c0c680004043c91b058881d501d00880700b102c4900e00626001c503903030f840300000c00c556500101412401c142d002820030100c1c0b106120b502c016040d0440d056295007005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 361317329 1250 361316079 361316099
    0x41a0c0613020915010c1205030708060604050d060b1306030c06081e04030813050d2006060108010e040503090604140907090b09060a050d0f150806041a181005011d01 73
    0x10811aa10240c04e03c4a060702e0b800340002ca40300a0740708984201d01e040c6c1c1c207001001d075082910600045140c01000c00e11510384101a2002c0d03503005015110414241c0c0c480c0700140055810046e00505070595003d80d2900e80e024102c065402240400601c40c0781c0303c8005d041c0030300101000c60102142c1541d000500030040e6180d0400e4052038445102d0f00c07007001c1401000b13203c007001010b911415042c280400c0d0840c0c0c5000c03a03203c004050380b00740d0602d0412135480da17404a038503500207180c603030041c440000c0c0f224516412500500890341480815800320b2142d900c02c1e00f0070000403110005950a0f45440c9061940c800124a0203c070760501c0c00030314144601817542c86c0c2e40301d010089078641c4c0e8684940145c54145030186000c1c0014000316096800a00030030210045501d449030020400c904001100da008650005000340b00f059040300307a2110000140c8190792000c220300d170f0b0740000c020420504050035900000007c075940340c00c4400c00f09124520b03a403070b8041e80b8403004000f80112 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 361318579 1250 361317329 361317331
    0x70506040201080f0f01140f101806050301031e050703080a050403020a081507030c0c06050c0c0105011d0109020d09050d120b04090f0602090a030507030804090501060504230402041a0c06130209 85
    0x1554003142103021f400e400040c40c4040c100070080c0c01201c01032402c0d00356580040507247c004140c16044942a480d0107044030648800d0102a0207030505240c85145078114004840940d0b0091007940e441c503403030343d0b1031920651210201800180010400313000b90304c0e105461000814102004010880c0019143c0603c42030044c401d0003419a41d1013006020782c02500d80d4845640d001000304402c1c90083e6102d43e05030491101208150310303100000c41c1802081200c001407113540108942613038645950800a036020f8540159481d807107502000c0000d000b0020b0300c10300c49150301c4500c100c00c103a0444108903000c07a03181920543c14400711101150489034250001a04800c2c0581d4070001c00700404c002c1201540004c203140701d8550000180100e280c09041501c2800c1024032442e41d1700e0f80102c607a0f00030b42c002d80c05512940e4114940000110b4940c0000d0342e8090009401c180d601d03080541c55506001d01038607403400018003c1ca14003c20712045602c4001c11001c030500c081c0702c2e00400e1217080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 361319829 1250 361318579 361318589
    0x4050f0f0d0605040204110d02030f2a030c040e0106020c011d150c0c18041e03360801060501030b03030a050313060e19060c0f052d070506040201080f0f01 68
    0x20b603c0002c40c0075501c0d01c0d040040360b22034070080d25039641c0003e40750300d000b544120b0780c80040d4228031003c582c040000c001d55441d102000081100c001051480809055002820b2040000300801c0000b0f1010759801d07105008240c9900039103c00a0107100140c001c82c8500c8100f0030300c00f0640101c40d1203555468060070844c5200035055110b0346041c03541460604140e040c16030003c01b0480f410220004079032414400c03441405031f941103800014040c00048443c400c0200812482d1078118220342c55450604843e82900020300b0f41c000403004c0541a81441d504410100d075150803082c041c0d0358050040c45c80c00101900114540344a81030f000f40301e1b00029161710149030140c250402400106e42040070500082000d40e2907034807090022540058403500c048600398102a021240d060141411866450361a21b45500d003c2e201018401c4140034074150b110603043e0000744940c19030941c00030300841031088000740f4950070540005008560300810342c0e1146650324082200031544448580c1c111a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 361321079 1250 361319829 361319831
    0x5120706021903050904181419060209010302070b0702060702011515030c022401050a06021c050a1106010305100b09040309060e0a0902030405061005123301090204050f0f0d06 77
    0x40c0e1400b21034030b104120710654054144000c00d001c440290030347c600524402c5104404190002c2c02503503c1e100404440c00300d24400c000880c0129200390000d040126051600501d8200d02e40d85a900c1e080003a502c03040142c0c4190104003400b5024451003000c002c2542c84142068509281d2414031020b061200b8101503c9545641c0294000c21901125010070005a0a170f1010883d00c81c240c0030091242a100d4030620000059040c000314060034150003091500c9040c4109040030b5500703600150000040124003003c4060894050210301d02079413041025113140f145180d168000d40321340a100c90303c42d003400d00511000035003200c4440201c1e04603042884005c020070000441e075802540c4115031450000003040200140851080e209100e15003103440c825842e60140f0030020002d04a2007042e91003440c1c00020010710320f45102c0d0004d180503210a812020603c200c0d4100002c0e440750b001c65402080902952610000307201103400709541340c00c406c100d0b01001408103a0980720181c801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 361322329 1250 361321079 361321123
    0x3050d02070828021603021f0320070c0b0406020604060905070812130e01050108040f052d0d05131710020a090e0606090a060509040b100c0c0b03161412100512070602 73
    0x80d4000e410032b5002c4d40e070200010200080c25820102c0a42c00624200c52607980b191020039100c0400b415601039807043ea004120079602c070355544000f40f501e030001380d40a1041032800070703110a00704440e0101c440000200b0341c40701c02c420043c100c400316641001d201243d800d0010300c010790340720701c1c055801038002c103881c46e80a02504045050114440e110403150111090011001c59407800002c8109600412128100f403074103801c0307031503003d440d1080c03070156144402000004030600071040820441010313a0b040c8201803120714100e91040c581c8c2000320b004200704006146d4007101d040d80c00384055034894604800b81e00010743c2d044090107054140607021412680c1078489600448054801404540845560b0340c0c0249c440d41d110f85007100d5607000e03004003244111294094a000f900003980d060300340303242ea03403042d40e0215148600d1444100c040c4400214080c45205050041996030754040c034050030310040c81442600740040401740c3d4400704040203030300d500007840d0324211140c03a02241c41c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 361323579 1250 361322329 361322389
    0x12a0803071707050703080703060503060c09130f05060a090905030f031e0718081603020906010215010905060a0602010c0e150c0a0b07031803050d0207082802160302 73
    0x1251150520381e0b108806440c2c1000102a0068010b040442c000e8482e01d809a40b11802242900c4c8203000d5550541c01140201d04210f607442e014110204005203618101225219030f8800c544200d0f8a0119054489060002d1420b00e00c4001c0e003d400c854000f80001c1043c0d4070758543e0b91241e17009006201d1400800181e03040d442000c003050880b0340c80d1a081d464100501c0003060241c40d07031407a0441d492852800030344010000740ca815803189689182001030718540070801c5444006081074158021320252541e200b0144554502030703c4c00104c0003c242c00c1c1502400030300d52140d00484d0641e0314100b9a403000c25008403101e0720000c003c030351000e0719100410100040d1300130411240f440d03100300a400000c001801010520441c0300356820450514813001007a0080c107084005008241c04009001101506400525000d802608518035000300700e1014050210280c580300c2400307103251003055015505000400c6400081d00c06005210300715000690340002441040149501440e21100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 361324829 1250 361323579 361323587
    0xc03020d080d020a0c140c0117071404030c090501052d03011d01021b0604021315030c0603020c060a02030c0f18030607021506010503040c141305010f05012a080307 72
    0x50300081c10803d548030b0020480c0608065840381048030082e48146c221445040000303004c0300d045105955254900c00d500d5110040e014000e021442080a8044510558445100184000d40c480c2904440061602109101321141a0040c1d0b10440c10b030080441800c9030341c005004080000074010011030300d00310020f4010900c540b0703040035200384070b007048420250644c0039141402020b542140040034080c0025146d440403a4001e510541c4010380401c08000c0758000700c800382d10503604109541d101d8032070b0030f410001742e80003c0c0002c3e00012030109486092001c1500404000015821400d015100c03a06900882c692000715880c00301e041e007201c80300d1912003401508042d05a901d94145070a000f522000005681c0c54040e42c51004562154420012603224540080081c0405030400c003040c02e0300c1c04206951540000301c0f0425a8403422031307100c4e2074020000105400760003031034040007500800d000ca0301e000800c20340c1c9039200622841c100380b400c082e684c0116155500e07552104d0940d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 361326079 1250 361324829 361324837
    0x6060405041a03060c0702090a0b1521040b15040606050d0c031d010c020d1b0611270f03010209030a0f020604120507053c060c0f0c1c0c03020d08 64
    0x95161213010244004d0a038410003c05849009503006401d0341d8a0702480b0b42038590038104a500061800c600c01100035180d40607011510203400d480c14420002040c02190700c5061b1401d6606910b41070034032019040024442100c2d40040c2d80c00d04c11507107811409411070007a034800000843d00c3e913580d00314180c800e905c0f82904110528200601141115145009000500920015200341200c60564501804048000c00032410720810710000c0c03030340d0742d101810391402102c0d0300c408140081d518030762101c840c203084601d541c5c01d50581240040c00f0030502c0180c03981594003991041000356225140452510314103a041070441d134003400c640c0b01103181307807040e070380300e002c2e8108003010501c2000004145102203075401c94000038507054440c0100100002040e40080300b41c1070791082800a414002000c500810042c0313064103013016a50b500c1c1c10203942d0b10318100f10390800c0c2440e4010f480c3c000c10110008880000c50421440c8035514604000242d000180c49101c1590551003000a400d040b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 361327329 1250 361326079 361326131
    0x40b0901021215040605010215060609060403060c020607020715080c0a020c06040e010807091b030519020c0106081005090316050106090f050703060b2b06030c120c0e0606040504 78
    0x240e03210f1400c9802884055507525110384180d0034520001600e600c0020b5600d2a6642c0451818440d1500810030659911000200342c000e4018070000000c96900e10400c00c4520f105d401038007031440c04c802c0003414140c45070844109504446415103d8a920644460b07004e10810501a51400150001d07440c011681361529441100010b0215850201207a80c60403902204129040c05864400c82d40030740d05444207001441841d40f0369051558032035044160001400100040c0c04058103903e41e0907a40031071403080540e0344481042080c24410001600071002c00541000303213007050101d603916882103400c2c0c106846528407001d018000c080d031001c401419a00010482c3c3c034072282c4030344050a0100c071141c01003854000c0c00a0402a480c044030040480401034808001014000c418826210700900c200c0c03d644d090b0100000c5c0100b0429000340c0791100c88503800d13050515202d0510f803001d41055030601c03408420710205e0380b03c410a9030b0035280704176008100300103a108007191150301e4041ca = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 361328579 1250 361327329 361327357
    0xf0303090714101b0c03020a1d0c0a0504030b2212081005031f0b09090307140a11310b0a0506040806042a03060f0507020c09040b090102 60
    0x40c0a99503000003214022122440c0700303203021402c00410003618400c01039820000c14846031010f403c40c0c50410207403403910b11030606441030399186c0d00824000321481d00188079155030031000b60f5841500c01821a400b841526449141101c845030080a9010300c3c800201141100400b00b2000c003441002c0c9039404500c201c0b694108000d50030070540460182801d01c0101d01000086504d20000d0321140c02500c2c0090003d041503811800c2d40040c112655071032000300d035501d89018195644241e100350080020038001c0d61104001e050003c00d0f04004400180503a000380380b01000148004015031a164044946006080301c3c02210311034403004400d0160312801c5c60b070325194a44503540c041c50fa031810944840d040e8584501c03d000c0e2a200310b00480c000e81d4400000600001c1c5c4c42681c14044c80151546401c800f01e40c1c00d00c1140d017440d260011190140c070360700c18a140c80300b240b0585612980500c002c4c0b1203a11040c0c0868410000500050103001c00311000924480094040301d8005480180c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 361329829 1250 361328579 361328581
    0x60913020313120e0102071a0d14010918111e0402030a14070908120f0403021206011a0301060e011812032616032d0f050108030309030703030902030f0303 68
    0x4020b6403203210074408484601008281c8100c5500c5030410300158941a0010300f00c0600302280540c1d090003540070306141c44810443c0707440e096102d0045865851a036901d46031994184407211003501d00c0da44d01d2540403500d02d460f00d00414001645806010010786019080220300c41090607426032940c070703a40c0c21038000018020b0959980c2e00003601903440503c1c00029440d00c1d8011a40e084261041360010307030083c10188001d660040003444030003120200c04d85820745d01d9002c620304092a04005100790481c40041107245000302d05000c941500c00181740ca1981004005010840e0500d1800c0c1003001100d000c1000030548840d1304050000340b480358501200a103001041d01e64050b1113548000d40c00303280e070008020700c0c1030403a000d075401c18002d281040721910102e00511a01d41010003005155080b01e030300100201402080049450000c10714040c840109030559030180c0c4415060380c010030030018000004015183e41030390510300822040c4032400000c0c60700694120560f01808000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 361330935 1106 361329829 361329841
    0xb0a0e060a0903110a0e010806010f080a1502090a0b0301090614030705450108011404020901051201150915090b0d03050705010f0c020f0c09040c050609130203 70
    0xa40703020700c9903a5540306e240000307000303901c009410f404c01001441884c6400c1880009041038034010f01103043d07165030f4101107072111040a502c490b800b04a044103550380300d41c94001418424811510b958403803070b50324001d001e240710f40f115803d80c80b02940c10a06001c9600411130300c004110220081c16001c00c4100990210415943c080d1940841400c15500442480740951104980c1040b036050400310b81c219000b102c0180d400c14000010800143e41c4c0e00070880c15203000ba103484191071807100c15076000d0400c2000b954192459007802103074035075a076405000c8602c41000c11918017640d410000041350700000295422482e001c0b1150007203070081c0300501c0c0a51140000045201c02c4500c8a0120381886030a11300507007000d0039802207041c00304841d0301503080444615407281084c0d07480d002d0010013449414000c203c040b0310094240c3c0c0700311458003c251943c5040d90381385006 = true := by decide +kernel

theorem cover : BRFrame.Cov 361151079 361330935 := by
  have h0 := BRFrame.cov_init 361151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 361151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 361151079 ≤ n) (h2 : n < 361330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
