-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3472
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:45:41.229695+00:00
-- url     : https://prove2.me/submissions/e7f9893e-71c0-41f5-b12b-b5803bedb233

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 624280575 ≤ n < 624460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 624281825 1250 624280575 624280577
    0xe0118050a110a180605040609020a0801151101051302091303080c16060e061b090906060d02071e0b060d1505090705030a08090301060503121b030d2906090d03 70
    0x50003004203552410f000000421040940034000c031a0104040041c00f880e02c1081d000350300f40781c40071030902c00e23a0085c1c4003034030416034400445a103071a0015010b8480c8040540900100302c41c0070700800360078091144108142143e065030a4064814071100003c0107218115485621004500181c2e115070755a80102c400e883d040e880d820503260415442d8511403008254a140c035080641c1c21a01152491003003102a0419443d65110058491544121000f186c0d21612503000508035240c01009086440124000141481255501c00070a00c21131030317410b910210202d620104101c24515850f0307209000f528668001d00c8180c1e40c01300c011101015070000035488200041003020304100340300c01000d000301100d040c08401d00f0080140c1e803048900c07030f0095003829808251400c0018580031004042d00a10f031400401c0700400016402c034101502150000300285200fa200c0da020f40c102c0141d444000c003501d1480c1040e20100502400175180c000c40d4188542d503141d5480800c48a071003170b01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 624283075 1250 624281825 624281843
    0x30c0409051509070c030f031505010503040804090213090f0b0a09020901110d1106180a020607080403050a03081608040b07030902010905030601090e06010b0f090607030e040905010e0118050a 84
    0x503448190020040782c000c240d0300544a04208900c03294801c07882c01c28140a40c680c3d52a07090380031802c0f41079a03481c0c0500328500300681000c0046501c00e00043d64040d0003446031505040c0c503004030b603069030300c10750200382c4110b1290014002007029102d41d110850007100b007000080846008030700c107622913100301410960f01044c0740740580d010302c03403002240c0c81d01c5083d180120f60380702e0f015100042c001f400c1d1085104032000a004150134052003e0300c5d12584006140d40510356081003102c0c1d01c41a070454846405004c00030001d00c0420680c0c0d145480b030340b110100c40c6040e1b007400100358609186401000400350601011070740d1034074001c0c1c020601e4500802d040c0c51900041c1e60860b01c6034002a0984146070000076104102d5000d500c0055440003030b01c0445c1d071b03900341d010454010301c107641c0ea00d000100412869890000300070715003688242840781b8440c42d250002011242d00b410250349036511961464280c6c4801c0c072900075411851024190305000b603860f0076940708400d010060003000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 624284325 1250 624283075 624283081
    0x120705030606070c090e0c0f03060c0c120310090e034b03061008010605040e071707030c0305100303080402040509030712230a082e0803041505030c040905 68
    0xc0b40e40859100a4021030707554130240d681c5500100501000710b00401e140196200422036160400c5c0703054010000400070442522440c12022607640300f02503c4040f0700c20084581ea141d600c14000d10b00c28043c1d20301d1810540d01c0d0131451303404d0740c0c1e1302441a12180c004220390000c00c211110500210f070401c0c2c603059040c05015041c00c800c0c4103100501032044e503040c0110601105604011803040f141610410604030200764242c0b080750007030141c0c5011038400c0c0801d11803c038001c0d0b0516400800d42c40c08850100d40041c0c8803a00c0c106c2500c100d000030303840314030a041c050b03018000c1c19048210140629112480c6840c0180368507005007009200e00d0b110000b0400c80102001544c3c030542c0c01c22200c914640c50034001405200b00703030046102100d0304001c2d00b203e204980d803d40f05170302d00c0340c1c071034603c10b54900111111000061100880845031030000245c1600c1d90002d2001030402100115580c5042442e01c0d200001c502e00c0d50810060100100451846550160f4044403030141011900307071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 624285575 1250 624284325 624284329
    0xc090a0e3012040c1401090b0703030204090612020102010c020d050d181a0f13020607030309050127110f031e010b1801062003030106111908041701021207050306 71
    0x2105211080015030010074440e840c080c0b0210100d004500c101003040c0c10550359024400c5034046990940d01040680c50b08000d08001480248800f900c20b1800616003500c0da05008100c4400760071415480850810300011940c091080402c1e1400b50300007010300001c1030340003d0482c8180255100c420703445605841c108030120030283c0e00703075070302c950754049a942e8100b0880c2072140440d00c401d201c140103030108800c0c556954021090503005030040340740c142d45407030581c041d0007129803c440c80d40d43c4004101c01d03d00d84007080c110a406409031040000c60178100401d1024520808510980c10001000125640041c420009082c0c9611307a2851480209500d070060200c9080642c004190010b800e40a000d07440e0060b042e0340d1103440d4800f500081c000788004565140c2e4686080781d0040005201c00d90003644085007038451b074804c0312802c45002000700c6143c03050f10022120403001003001d000440b20400b40c0e083c1111218001c600782b0301c800310389912042001c0c0c80b00003030140010109501d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 624286825 1250 624285575 624285643
    0x902101407080f1306030221090a02120606100e0a0e09120304080a030e03130317040815062403070e0f0301090308040b13020a0b25050c090a0e 63
    0x25940041041d0744500ea443c0207954541c0c414103031925403000311000402d940340248241c134010765808803030034420142d00780525070301a4041c0000740f0714803a040c0741e24010b0b91210150800d1040f810043c10003410031708240114511050801c105220b5040f642d142c00342c0302c12110804a40d010081d820098680704031050a00c0c92045c4c0110143e60008100000d01500e400100340d81ca102c0d0f0707801c00c09007100070364071178407070050a80d41c0400700c072025000c1012425045003504074440480b0702e50314180d65600c42ea845c010403910440110701b1040200862071400051603e900242c13040700013a02040030500902902c0010001000c0c80300c1940b450b059500c50f0201071207000360160003005008200c0c107014181c030100311801c544803a45600088c08912805131001700059018284807812030400c0b00300210364000c20942c042c02c3c429800f1411929922045481682c1d0141d00a41400c1c104001445442a00101070f041720304d04106295144240000d1459101d05500c20b0480d00001c03c0f008013101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 624288075 1250 624286825 624286837
    0x2040c0c0218101a09011206050301021303060b01080106020a080307020c060721050901050a0518090f0907061e0f11010515040b030c0904080a1704030302030105040f09021014 77
    0x100129050742009902030a800a014901941090a8041d82d40340409004807032104c00d000110424072a02006500800e05851031f00352002e408101c2c6603c500100b422038000c43c44207203ca040d10b407010424010988111303450210f00786020001c560420700c000e5a9105c840200034400b00c0e000000409451090003c104c91070700042140c1d9480364241040c450900304214124009401c03081c10550040c001e1040300c14030072041e140d01d41440c11824007501c0c903030000c0d82e905551560700c05240240e0756504503810301ca20215460080e4500f0180c209a1408549420940070700c803880b001407820018904148113840d80c1c503e0204035201d08500125101401e02621050382d43c00c100602c104045180d004e6070040b601540c003003000020710300416a036001700b502c4180e000011000407901040549005108070b4001e0308048100c4d809140c00302c6400700d004c8134180c00007036010005001030310b0703c0c1c090701c061046209000d12408020b500041c5050703807459580d40070f00140709120104000c4420950703807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 624289325 1250 624288075 624288079
    0x2a0c0c270106030e0f010621030909020304030c0515010b0711041d030a2706030507180315060b0702030c0103020a020a140d090501020715031503050610061e0203030402040c0c02 78
    0x4465a41d444090040d2803c244ca00e04d541c0910241600a003105104070401c44044401d5186414a000340301102c80c4400d103001c0d0100a140b10001c5422903090008600481c420760300c0011988450034011704008140c1031007112510304400402020690405a41481360850340c446801402d01d40090002c1141844003208a80d81d810303406100b1401101409650f000d545800c140b14405001711003001403205000894406500424400c0130700c0795000302e40c012840d04020b0410100030b08000440301e00f40d401102c408410a440d0b8003074145c14040c60004006040400b403e01c203c560001c0d4650385034180060405902150f240305440c4200700c00a5010f070030068824900d00b10340140c40c2c80310200410346c4041001c0090020305540b0025410301105c20030107001c00752010810303080f030251036072040c85070480e00d4228020010807410301440b8059404040c4d0340310300603d8104003405084201340603402405116404c002c03d250040201da50140d812a40050145a120401e4509030550000a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 624290575 1250 624289325 624289399
    0x50a03090e10090f0b04090c080f0a170c070b07080a1704031b02010909111e0307200c0a0b09090114030a0305160803040b07021902010f12060306052a0c0c 68
    0x602484442c10004041d40c0a070424ac1d9004800c03000e0343c03aaa20020030000b410b441181f12889010341c1c04902600c040364444041c0c1c3e1007982e80e07048101c0c140d0026031040d100d0400010782074250070380201a40d042e40502100c019101c2c605a100601801620f4141001031240e645090045a00c0f5070200000f40c00c004504106c001d500840200309034000351686801e940131504615280902441560311461059880d054854211079a8132882180e15000e40e0301072194107840c1800d0359032001c034030001c4e01010083c01e4854690604016400f503041c0d0051814601c040214041900e0103c3d0b00004140c03d03080c80c0740c0d2081e682e0101512481c00c141c000c0c01041c408002e00c010003603140e80362400307508107508540360b0405580c860007207000d85400080c041415100351115481c0102c04c907a2110100340e000003a20b559075200d000c02d96104403881c80e01d0050501800c0c86141c1e1080c01d501083d800640001d041c039109400c81540c03609403d03402c6110380c4d1104403843e200190380c0c00c02d080d1100703248405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 624291825 1250 624290575 624290591
    0x31207032303101e05280302030a0311010506010c0209150334061110240303080601230f03130602070b0604060905040c0317040f03050a03090e10090f0b04 68
    0xc000119628042c604c24000e4241c1c5403030800000320380480958600404400a0350600d0f10441816155800c071101d406003848400000750ba03082c801441c1c0300e802031f2244d0007840115880d1a003107600007131030581845404001540540c50340c550186c4d0043d01030140303501070415540028640080109060540c03480341031000c0b0000c842446404480352100c440030025500c40744161a168000c0010001c1c075808200c01403141c2c43c442d0848492001ea403002c0003c080800c00c5942c581c0781d00b680007540840c0c194070034802c040d68454081d61080c0c0041c100110701d1042145540088c3c82101c282c95480000030021640b00c401c14181c0082a5074010401c5544a1031480c000c101c061007240ca0f684114078281c00040d00302054010180b14035030050101c2003540c215550807081c00c0d03901c101106182400d0201007900881e15006c400038502810040c80400c0461800400ca07006a400002c0500305000520894481c5400c402e0107030f48020201240300301284070300340003d107030003041c1680c098201091 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 624293075 1250 624291825 624291841
    0x60305030408031305060c030a03050406060302330c0703110f1e0103050705040e040b100f0603091205190f1211070311060112020108060303040e090303070e031207032303 75
    0x10304480b504d540c2c0303095055079680c0811015000725070b40c01d4110b40080241c5e507805071181e88402d074018030580c40084e0154903134002c00c41214080511100072404030300762920716214000c1c424003e03520340074aa03242c40c6079000410345400d600e120080c01c0912144202006541c0d0400d0b01400d14405003000643d6207003601d010108061071303d42a8007082c50600440c52a42c03148007241c0030b45100142c11a41354865070b64a03143c0b802c0060402c4100c040300d24002c2403800804904400510306503901203000c85407424200301031200443e0300c005005040010300500b4100b83d265408070f0300c0c1400c041600c41c1c1c54050070b48901c07005051559000d450417038180c80c03484002002e4026180265545008800990000c0c0d0fa20704080c01420340c4611160074140066101d540815171129010301502d0800b507a8510036840f05806894007521600007208014149a00c074080700c5145404134010500801c20381420f0500384a90780c030140130000e20524081c0058098200035003084030241d841e540c3c03441d1500c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 624294325 1250 624293075 624293077
    0x1e020c1005070c0b06010203040501081501020a080c01060311041404021e04140f0601080f0a11070609080919060804030e1809062409010b09120601030303020306090901090b070f0306030503040803 86
    0x404803030010013040400d0955200100b03130303801c1d1041a10303045101d845002c6001c0300e844c0f40d4a0450f04600c0b415812800150941010f0400c0212140022542d9411884c19100582400c005103000350714005d034101110078400c040c19041a010365400d006005810303082c541c030b10421030305141c100c0c0c02c00321200b11207085451414494850804e011303100e916180300456450070305440d1030580f0300b0100b011070200e212951042c3c0700d820822040900d403400650703c941c06d4400c841c1090f03072805404101ca0041d0b0804403001c010781c8d211440c02c80d080905111014200500c0940013608000c40c010700030019468104072030000d5519030441c00c24514100980d203a9070201154221212018640e9200503603507880c1d254a600300c8000d00038015030f030900c103804e90150815800190300a51f40c1d20329085201d401c1c400d15000e0350181c1d4005d07a40c0d103025018401c01400c00341050130340703030324150400003c40d0320f010046d40c020401c0e140640c104045190118094801500007a015000014000402e820004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 624295575 1250 624294325 624294347
    0x50108060a1103040201230706060e0f010b04150c0305070f0501060501020f0c0d1202120d0905120313260a020a050d02012703030f091b05041e020c100507 68
    0x880c06100240b01c82d80304500500080d20001d0108100ca11190603000008914204001c1c0a5a0f194101410b0703840391030988009034407003842e505500044c042d4a0030b0200606002d05a600c166628152800c680c81400b401c510f1450402c11401c5255141090722079411920100d820a032040224070301400c00500801280c881d050140c85200d00c3e540c0c1000c00812264902d40c0014050b809640349600c4107103100480003412400c50159043c14041c03000424058060300b20700c60000644504280307041c511745250540c0703e0581c08400c5c81004010003100400780402d82c1c0c4040c598005001c205c40c03a00c4030030302070300d10001081c40100e540c140c803a038000745201c038850007142242c10901b01c12805030308940e2860412040d104101e1540f55030300e45407240403281e00d8801c0c03400280d00010048100c044481801e0f048410b00d0702c801c840c108800501c1c2c01d810280600710b03010004140390308040010034460040005249030042070b02c528812003031000200040703131101c040c0941d10b09260000c2001c0b60b0780b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 624296825 1250 624295575 624295591
    0x60406110432040e0c090c13030c030b0109020301030b0a0e0a0c08030a14030907050d0507031212050721090c0b030403090312260919052a03031e0d05010806 69
    0x82c10384942c03549441c1c0901d000c01194200078218a101e403009000304001c3c010280d032007480040104c1940c01d1038070440c4200650040e00b400c02040c0c2140740076030441d1010791103080140c6c014401403000c285220702080c0c200680c80c05c0003900703052200340c44d17041850154018225030041500000d19050100040189002035682c2d017003109402d034080907844c00252042c182e40c1d840180103101d241064103a1041940c003440c21a0443c0b5030700d540d44101d241d403a055180010300c090398101001d4070240a0960404901e0407e80a00729041c1c040c0541c0c0ca02048103ea0801e80300d51401c07041c8000e559201c400f030301e4008040c0ba0b8a14107424090121600e40c402140d1180545e844400040e00c0b44154040c4402c500c015120000c03012b00503460500b1010740b400106004d041310781c440c40d11541c250984018401c8024258000f6805d410325441c600041d0440701003c1d4002001846540c0801200c1074081c040008504205681d804d000850007540185580140740c08008030700c071080041c500d4890100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 624298075 1250 624296825 624296909
    0x201050315010c200a0801060810020f0d1514030303090604021c06050f010305070e0708063604211202030915180d0c110f040b040218090603070303020604061104 71
    0x86c0c4d007051802c0341e1303203845411159080320410300b12408d03542d00200144108038100b1800e02141003090000c8a55030b050058026205501c104a1050684a61802c2c2003044000e542140f40030840183c60300001080207101e80c40d5448804542c030480080c40d8400c0d500640108524944803d00c68040300d002e00040e5207610820100040030030844200380d1140a0954a003d1252075001c140100301c03803d440c480e002e807c0101c8002c03103101484021380401c580400019800c40c01d00d404c00c91031407164141010038205081900c220706c0c1d0307000242d12420140340e000061b56943c0b4031081d14181908000c082e40180b0580c020b0040c2d04c100040202841c0c815002a240c001c0400030056890010041001340820381d6801d08a0f030914281032049502240a0008248450071303000060403a400080d5030b0052210f004c0c5400020304203c940e01e0350240050f0000c01c01c3c0b50071910040e589100c002c00c014003541d101c1491041440340398046d1030041020304d407500c1c41c0d00f0001c0d01103c1c0b002c4d440301a00e110006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 624299325 1250 624298075 624298079
    0x31e0c0b090a120e0406030807110103060e090d051317030a0f1718070806070c05150f040f2103020a0314100605070602040b07060b010206070206040201050315010c200a 74
    0x40410501c002c0342c0c2c08498800f41c890064420354101c4500145994003e81d41c003800004a02004d004114292169418405800c1002c0015084494030380106800748801420851410f0707000448241c014001d0502c1c4d51100811280e00780c00326030540154010207207900c0c00210701e000000c081c0560615549a1881552421004135a0084080144100c207907010020171042d0100c5030250380042891001d40e0388594680103034518000080d101000047d011a10038028400d007441100e80303040d05004400218204554a0790401c000a000030385014164002070f0200006c041d00d52254018400600c6030800c00c4010180094100c1980d84d00171a062040c4124007100360b140951041d42c0840d0075610781e46c00d10800710f810b030b00184e00885e9465420040410408880c101404c11544100c90204070804c0c0500020b042984c00fa02d08020f541c420070a200043c0e820030160383d4441c02c2e0703032844001c2424290048445144c0d4407406030000c030004512141c08403056040503a090420b0b1100e4030310079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 624300575 1250 624299325 624299341
    0x206090a24110a0305031e0106050324060301030b0c13140a21170418060f0f14090a1803120b01090605040b0d0e0d0804030e010302040302030c0d031e0c0b 68
    0x641003000e280b420350072a20207500080d0050703005d10780041c2409116000c00354140308901036000280c001c880401d0300402048903012802e1694520584000350b00300d003c0f200100440c0c0140010b00004104110600c001000c07050700000752039000000c01c0a85200582c2c402c0e80594010309220380501503400c426001c80d0010391081d5061401c88428030b000c18594103901d9950040300c101d41c0d5103d10b580c003000006440c8140a14006039541040d20000c1d680b0301d0032400105003840e50340803807011400170100300103070031801d0040c0b10a1002501c10900c00c2d540d1180c5e40c0020b0140d14031260f074100c0c0300e190340c806155200002000035030700030004205043c0c4413401552141014814100064002c000c2800040d004c803005d0990b80b19410001301d0000d13014044141003448130f000700b6000480000801041c140d0081c182146040e00f820218541411a00480d84071b100ca030081e80d01903140711100303000705407142d0ba00342c88819180d15100c5804a640c00700518500c0c6c00641528803100c100c010400b28 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 624301825 1250 624300575 624300587
    0x10e100b09010503060405250e040c031b0302071a01170606011d0f0d0b01032604030201050403080a02120c0c0a081209150c06010f0503010e0a021003090206090a24 72
    0x41c40058480a00350703502c80c1d08200140200510440070044582030b07030040303c42a824005080822504c52190103012001400119a10441f90b0010035007070807030b8017254070701d840c0b00300035a1071683c9000761381d460581c2010003004c810b02c6100c00312088c00310000181c0e00150391a20110402d08010346140340c44500044582c40b4004946800700441324440041070b1610010728216144042d014024102ea241c803503c1505c0026403080c1c1d151281507801d070401e0728800c0c42080b0240300498166007400d003990002040d5000e9800011700894002a1029003d4001c101d0080b031014410034243e690340140c4901034440300a00511030040a0a410219603504082041418039088401050500500340100480d10450000b0603040150800c01c425080b081072014034040c00c81400c032110380742c1c907007820306003140d0308414000c400b50000d00740c0c840140e6406002c56201c00840c41c0100c0d00040c5400001d1140c8204501c203a0f00030711200c00015888942d0720002d003010011004481c81900ca50000d8401c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 624303075 1250 624301825 624301837
    0x30212010c0203030a36121d13020d0608030405040c02061b0a110d020721031e02010e030d060e07050c10020f0705010518101103240306010e100b 64
    0x243c0c00a02c00200002501d6109010040c034201c900d80e00c0b01004c2e0141c1c1c0498114001540883c0801481e44c01882010280180300101c24a4004140c2d007040d10807002d08000700703c02c2c621600d8066045511160720303405840e40117000101c00c00802e9a42c44000b540c1354054440ca42c0181d0610442601444c0046100d40c8103022001c0350342008030682020408a900c4607000c102440100d04000707040d88010040040005003c0d00200344141c1400b0325140301d15401421102c0040000d01000d0003c1d51248425240c001c01211018200c0042c00059025010510414030700c1c0c030002c1203030803844001707030071135000c030f41000800b451240c41c2d4050031100351041c0c2c0703580007940d0321000740807c0420703081e4010001c1d4810445d1850801c131860707568500391581038460081074011009000d804400c148403100082220400801219900000402071404002c000181c002000300c10075440070003807442061a428000d06942c145d68546107204036116080d2480462021001c20100b00d0040c04030031651 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 624304325 1250 624303075 624303077
    0x3010e01021e0f19180510020c010305100b0c010519230415090620090d1e0503042405090d08090d02130903020f0c0f0d060e070b04030212010c 63
    0x84007080c2c0c1c04250895000801120b1500c400308509440340b0207045006000e481141d4442c04600804444007104503016080240305220400b020080c031500044c000103451020300780865a0341e2000c420058a104940c0888600440001c86010985040d80854420a10100000303d00301a80006404949a280002e03108014500d0340d03452071410070101540c841c1c0b050190601030041c4034212402d030b030b100400448442da110241700310003842d92042c44a0746100320003a03c0c00c00b00060005804c83d0b4031035030050081610700c400240a040d005d10024410b81d00042200e81d141d03664940c420104c5e0850501a62502021010340055482441195080000100200c0c00741c50940c8460303000742d2045420b15840b01040b503d810058446414006100e095510300103000c0c2c1040c10042d0078000e00001c20001c42e009202000710700c0d96001a4401007240a413603a040102c80d03031400038020304150127204807510030000001150303284039008000350382c42524078080d402e615041407800d3392070590001d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 624305575 1250 624304325 624304357
    0xd0c2001020303370609053409091d1c120e100c02032119110c010603050a1703071707020a0f0b0403030b0a0b0d110712080603010e0102 60
    0x242c42541c00c181c08038100100503109000f02d60303840300100c0b4007000c0b030424041aa464250410800d92503200d41c0e0351088c0e03404030001280002d0380f2001e01072081180300e40c0c2d914442080b0440c035288205004005040c0c048400c03c0f84098a001c00740c2400b400c4803080f01144a80031003200e20310846441c14803485050b49502c1440e40d4103450f06000b5140901340d0510510400801030035980c0140a800c50510440d005941c0c0c807a00f050016500300c0c040c043c8101c04190050031b0240780000854903480c00400c040000907440010b1203190b04500c54000c002450b03600b032078804000e003c00800c080d40325600c104c3d40000500c01c030042282d030900003210b1900104145154043d955030180d40e0440d44060030348151685032007076543e0103008450f200000d843c51441e0f10200410590188600901c1500031030388030403114500440c00800b031048ed11a540503944071003481145051110640300201e0703006103464508440070900402d40801140e4080c0f0940c240f8010704e0102c1c0041c4211080f1016a501c04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 624306825 1250 624305575 624305581
    0x9060210020706230106030605010203040503070509090c0d0c061b050a060908040504090b010e07031b0e13020a030207060f020306010905240f0403030e15030105040504020409050d0c2001020303 85
    0xe400250000003041d41c2d0291151181503031101c1aa410000659000704009420f50400382c004003101c400e40c100c5410b55000300700501143c0c1d0002010000c40d1402c035408012503036903180e01c03810301c190250420b800c0f654811f014070070840400110300a03204503039a4558144080921a1110810498054025080304101c1d10100740c2c2a00680c0300c40f0f0240305041e26260340e502c04602221401c41c81550405183d10040c00800f100400c01c1d9000485807038140402458000815004510300c2e9110f821f11002c0303031003084540c485860f21030040d5038504085444100303542024000c0e50184404654461500d40040844610b42c403ea9004480603941d400a4906000a0106e03011454580c00342c1c250340503040500c00300c0802c0c004c1050927140e2441a844611b14980540507460921072a071007400303040c440701208071025040d6411100221004a000d031202d00120b00204071341030f00545a17002e00e840315941a030304004c89038003143c07113244420428010004491440040b01c0304050050f0010008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 624308075 1250 624306825 624306853
    0xe180f030d0b0d033f0e060f0702030a2a0f061503080d0b1503010602011d0607050306010f05090d0b1e060f01080405101406010f08130201260411030d090602 69
    0xc031002d03000c01c14901d17096800811a1404030300c0c0052110516081d140c3c058485501d44c02d2207125040502010091054100080040d407640900f0f150141002400e1403a5040401d41d91000e03000700781084941d50608e0715608281c4840c1c940c40c9401c2d5401d90900514040300708511541c02c0859410452580c2060181c281c184080c0900c40c06455103e014503d0302c50211202d140298020a025000001c54044418558210801c10b08030003a8035003250081040c6150400205c0354044400d01c0d03da03c400070390541c1038802d8007668160b00c1c2c0150809600000300809114000d000311070b40407112091080101e1440303620b840448455400034105d0400b111035500400540c1d4006116400392000c3c55900c07803901c0225110003001078003000c11031040c8401560041e01940110b910f502d0013584071b144c840300712209a0841c1070001c0c10041d088440e04101188004401d1b8244100008002c5904283c14413140c0ca9003100d412522a000742985086258098102001100d0264016066096030212 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 624309325 1250 624308075 624308117
    0xf1e16030c32091c0c0e0705180109080a120e030111040e100b030705090405060429011e02030d110a09091a0d1407140a0e180f030d0b0d03 61
    0x107001d0381c2c0040038480414a81d079820080700100200b042500301d0103070181441403c18466500401ca2440040d040c0a909684101251002c840481e0710b021061000d070012240300c010b40d4003400450207160402002c012007400061000b1040c1d03646c070003000404001701401c82d000d07590024140c00e810003040011007126030b804d580c03000c10f1021707510a450396401280000c2d03208843c0c1c50300040d40010804240d150a01c6410780010044c1c0f010800d81601c07070345141d94500844540003a40520191541c0c09a00c103c010904030010600d81d070020661036040a0341d00c1c1c110384143c820307850610001144550711042a59a240c0c070a54880490f94a000700010003080c10036001c0d035007551040d0683e0034503140c00904000c4244504201e85d840c601c0c0355503050411003180c000c00303000c1c40c0b101300022455407004941c1c8141d9007401800e4450b51036441108a030412010b100300414007031541c8218a0380340c04000f600440030a0b10041c44100c85400801044600061008000c0303265040ca08070100b84800c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 624310575 1250 624309325 624309407
    0xc0a0e0a1515021b09150f040219110a0305030106050c10091121030f0a111203040b070201050903041802120f01080106060203120f1e16030c 62
    0x100145491010968105881e0203812114a94588054403285a541005001000d0790580f201340300002454000034a5490040c050500000c140309000e842c4d03940c0c00d444808000c200030021940c48100801907a40e0300d40c942040c0000c10003c0880c65a0794002080c004d41290303156840522303507801d00205407a1900040c001d0071780d031710a1111400c42c915440c8203079100c0500038070414240b00d08242c00c0207041c022100ca00b80e4030151400c2c0c101440e04000081d05d0080d64419201c40e100c3c201218100e452844c0101942e07803500c103130924000070402035401140200d0244a9902450b03451000c2a400e8900079129402698400c010810a1944820304121100c09000d400b600d0801032544130a006030042c0d5406680203410070040047d45001d1040360000d203490300155081007540032a1142c8040001c01d9000341040840002d0048034284c00c1c030b04a42d2101001040c030718281510b083c070310554804030784004a46021462040c86004030081c0307880d1000d08689441c400c405a8556000940711 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 624311825 1250 624310575 624310591
    0xb0403020f070602061008030c0d0e1813030206090609060708060a3c05010c1e0f0f0c0515091e0607060b04060e0c031302010c080703021507020c0a0e 66
    0x641584a41e05002c000010049a4000c1c925801c00c04111203e02c0c1c159882030680b6801003110302005200400c030114010a507041002000e03000c0b00202d0b54038a01da81000c0982408030b0200104030103039000c0003010303038060741c01c40da00c80d03646d099801c0e5078800c103840800d51070384403a0010300c1d810310450446c2c0d44000003408006070140c1d20038195101c800340c0c0600c203404c20001d4400491441580a03591194440d00092444aa10303110018042c00045007000d0084030001641d0090f01038981e03800d42001c1c0d03008404d0010f180b42d90408000c041140b07041103483c2141d28034006140c0c9000320951402400940c2e800786054881000c11060307005842008141c0c00900740703c03020030794850025140c003601501022407a00c0c5104108001c0760281d4000c100505503040038010301c0021300041d25485809200440c600651900050b51100c00b1414000c2c0840c00009080781003542c00f00d8424411041c0c0031040c50f4a442e040c00907030300d80011519042d00281c3c1584104000031040c0d02c523f801001c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 624313075 1250 624311825 624311833
    0x140109090804090509240405060718090b0f0d03120605040b1305090f063408010b130f06051803070b16030306051008040318030519060209040504050f070503060408070b040302 77
    0x1061b48510302191520f000301510305400c1080140101803060300d510503920b00d060420a032101c50465403105183c0540c3c210aa5030306400c8445841d403685a0b00308032801001110f010b01186001021264140800e8030b0103401c0280010b0b117828980600c3d0b44512000b007130710b59113080d110422001020001c1c2000000c3c40380c040c5d8250040301c00c3c050b06000300c041c1074407000c01040191500241800010300324071100d81020741c16202c95400008103043d1070000307441d80e6551054206043d41011a500b201c4441080d96800003000307a004002400311081e50036219000d4195501015200e050f81c2c0300d509840002044030995903543c029500031214441c1c00c0024805440340c000c1003d0803101345112000c18003a4051000b455002503441d800521042d903001c480300c0c00c5550740e50300c0b420392005100400c640c0c0b100d2041001890340581d900000060130400c00317850035042c400c5e0f8900030010740466501070b41c01c0120b514180820240e224a800400342882d004580e80c0f21506030308024400e80c11805 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 624314325 1250 624313075 624313093
    0x80a090209010e0a0c0801080a1e0c0905190b010815040608011a03010b0904050c0d0c121101081308120a06030b0405010605090c1216050d0f140109090804090509 71
    0x1d140c40300180600320791912030030b0074034120311100304551400300c1c914140304a1070010003040c1000640c91144c5548900701030750010300080a101e45180d41d840c02000031003120030100d9101d10650110f486000c0014038030901550260405003101d52101b09140066403c00010720b610740c0301c01303000b9410030f0042d10001d0300a6030780e484942110303007a940b5001e4004501d24103030603d240c24040c60f20b4880c42100c041840f402c06070307500c99640210b01100c1d4040c0010944840900a181c0c82c140024054214001031819540c0350003803010108640203404101e880d00451910240e0700c1c580002194046442842c29818814001c00c04000600d40700d40240c4402011002680b44074019016074411400482c189007440100304c5491802001c0d118145c1081c007180a20403012404650051803c6400f2001400d4241d401c0300c1d50700ca41003803940c500b4184103c0310b040e20410f6018115000786100f8203181662690312100907600400b2001d010305405010502440401c2da000c02d400006000803200220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 624315575 1250 624314325 624314329
    0x3050c0903030a020106050f091909030309120215010f060e010302071416090f02120604151509061d182a0702030606121b060c01020403060b10051603080a0902 70
    0x140c03000030f00d400103035160310b01040340d4101800d000c00c903031400700c481c280a45040d51804084104c0d4414010070700e030700c44d0600000c0c54083e41c080180150081c040e03080506d0855000780d503501c0341001c0c4c0d0013400d424000019203140c2a1070110242d481c1a901e00c0390b416102c01c0110080c1d00700c01c900303407111108200d414501050402ca00381c40741105002e810300c0c1d2882d01440704115418501d01c618054010802400802000707103041c1d40c4031702d0032030700020014a0707802003229113000d0340c000540100d04541c940c2c3d49150442489021141d696072601c0c0b1001406090184001200880c2c1e90080d07072044942c1541110080106c2d40a00c82c2e0001c0720b8401230702c00030002c003000685188e0002540c001109001e500303051044543c0000180c0b00c040c2d40840140340036a40e01c0a114481c920710003014203072031843d500c03402250b070075640202c0255116622420f26800800d0500500c0c1c3c4549210103051038558010003c1d0740120b02e0242e000c040c0000552020b0703805110040000302103941e01e008000050f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 624316825 1250 624315575 624315577
    0x120509061207020f07060207360c120c09030807140f030d1d03120406020a05090306100501080711060f0c0415080601020118050304170f1005040b160e0103050c090303 73
    0x191400381d000313040f4010700415940c02e1682c1034101d1011034101e16014001c0700c07619000305000b07400001031612020380c00c0041c10104102c0c00d040304c4c203130340c18500f9000c00c95620136900301001c5201d030810020b0424011003500c9802d800e10000740f038140140100320100c1c5c6070030386413800303200720301d050f2101410064200e40c11540322880000f101f070341d11184200344005082c03000214684607030003140b402d4444201d448131140014001060705030001050300500c1e10a106545040002404031001d6051850030340c680c0d456940a540c3c002072050340002c012600c99004070314040103900140000ea143e0441080d41000d0090000c000600104030011f0081340d0156500c0c03d01c04547d594031020704040000a00f035800c141c50f0038205000070030102000c954048200c0d0119520361201d1603503050716038408c1d41407100c000121071640c0620060780341840050340043e8031071441015501d001e036580c6c1d01c00c10f5010740b8002651001401250b003002c0c00e94000c0d84000d4102d80104c0500c3c0c101000780700001c0c61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 624318075 1250 624316825 624316831
    0x80f092503061b20011b03060e0a05070519090308040b07050f07060504091e0e060a2016050c10020d0e06040501141b06040c0e131205090612 62
    0x4003038104100148002c074811049045401460700f01104a00c803401048011680031480141da400341180c8840e0f4001d5202000d01015450415111142d941014004240c030344079040d901e143c0b102c0000c1c20840a0322071184182d00545508d41404041004100005146850b00040c454800004004205018043c02c02480017884040e9070380c1c02e62070100d06045016040850b00c2c2d0180c1c00070300c00f19800c20213a905403002d80b100009d00b0703c6401118004158602c515916861500c003c410b1444800304030248107092480d07041c0000e1003660405011681040e07030720101e0000c103100042040040800d080384071400340c4103e0303208003000000a81440c45070740c07026002d85c2c0032103201c0b41c0c0913800c11074140e400c0d9002c80c0c042d410b00c1d01d08030010340300e100c031107000025500b0006180c160f80590b008044450696500845541d407070285450100301d20540654014000b0000015101104118010300b0659004a4007070140403209400d03240307508a140001c0e48601c2c05d0090415004c007803012144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 624319325 1250 624318075 624318133
    0x303010308030702010e1605040e0c0d060c1d0609130f0f06090c05040e0c0912120d050f1017011e06170f06063d08010503010c080f09 59
    0x41d40f4140f0003006800c4803c0b041c445200354225039510545480c0d4a0540c03c125681910b01003100c54101413801d0801c9100b4050961040000f80a0400d0089a900400140c1165190f0420f05003003014242102151082c1ca903a00100400140c81641000b03024444e094034014400300b60842a00c40190a4a10b002001400c0d40e42e651002c01c0081080c0c001c1c1d0b2041c401c541040c1d4541420101c00b030500441c01005100044c800262000c85511401c008180c03525140c4c00383c590315220f0203490308031581f0004d8440300c21420a408103500459544c2d1240c040e4600000c6550054580341c407080e0842003902c00c0078040e544c1e51054601443e1b845010140e4012081d0000484a051480a08141c1000c81d14020300360310801e046400c20300001341146e00004111030040d0746001503454880640960400c070003500c0c1e07003120089004030542645845141c900e07120319031aa0388a806050803500b4020b0240d0014814002142c45054648405a04001d10b0f03c2620b00d0035841321407140c00e00c00c2da088092 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 624320575 1250 624319325 624319327
    0x3090506190f020403050c061303050d09080d11031902070513060e0708060918100204090b01080603030c15130812010306050718030209070c050d0903031124090c030303010308 77
    0x50201402841424488840b400d001c60600d030031038459175907420f680c00301c0e64081c2e40001800c1d0003041410101c1801540c1c403c0484030000c4c442e000090503440c50384140255480742090011081c0e004080042d00300c100d103c021414624403180500451060f200c0c0c03030040d03000f107101c08140c40d120b004010721104582e01c0041035140ca000c11016070107034000c0046041000960502007145c1c0c0c0c1000e2241c004003c0d4040402d92032051650505145c0d6030000840e01a200141c0016500440e801690750311001b621000e0700c56071101c080c182c4a00c6100803070019508504d0030640c1e181790552100b6000109882d6921000c04103654205540c2d00602e02c82c1800c4250300010020040c0710f0244590040103481d00071014160403100346446011400000d10a03d00d1070001403a0341e11507000f0f0940d440e0820200d442120450720094102c8401e07010030340000c0c001100812a001001801c3e0140f03001414122a80400a032a403058103400079103404a18001d000351400c80d9902000030750b010358000c644003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 624321825 1250 624320575 624320611
    0xb030c0405030705032b090e040b01081507021f020f04081c14181c111801030c21060e010b0a120201080c0d0e0a05030c0708030f090d020103090506 65
    0xb500d02881588403601c0f986c000e441109409003444900c2e0480e04001100ca008428000803c0c1c60640142d004988828560b000304003d108680e6860b6040312408015114200c011054150000d4000c84000300940e002c8008007180d046501c4c030130303a07118415440050520100c0004100c41b58020750000341c05900580750301200d1105002d25100030036150400302003c0d000101441d486000e00285900480c1030059004165101d1005040449a0031500350400300140d150405c002203070b6084060180e82c0c00d142c0105405400d0b00c6040c1030381d03003041030707400300d1031901c00041804070f035488903604500010f00480c0001012802042280d040314000072511300c13a04403e0000c0240141e011030070600d094a46400983d8002840c0da07040fa0000c07046a60741c1d03495000d1070000d001c000c542c0055a00c2510a25010710402001410707142e41403206a400d10b5a89660f225900e01a4101c1980007142c10400e1440d0352404103440c800b4640f0604002c14420515292541800406c40e030320b008010750481c1c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 624323075 1250 624321825 624321829
    0x24010306030b100f0501110a02010f120203100303030b270915180606040c170a0209030d030b090711060c0702130c030b0f030d02070e0912040605070c09330b030c0405 73
    0x8504c019007400c0c60710f01c2c00c949002d41d84c5580c0d4000050003905101a021541c200d80344510305405074011445015035903814069810b2445484900c07003680020f1420f070850519290118842300100720b0003020040d8210203010f00d070501d04010303004580070300c251444100751041c80c281452091981d180f14100c140c050750320003170030301100903c664881d0780317403001d00e0320b40d41c0c0c0129404e40c801098000f43e21659664201d114002c1c814101440d03031510030713002240045581a00310401c0b02c102034400034100c0c4c640600c00d07203240718070401425464100900040320140c2c941d0142400a000418080c050110321181c00112039002804900294481c00b4003104c0742071811180195003402d900901000c001c03040700030346a03030aa00900507000304240c0850b81985e0100800b418801800380c0703290b076465650700d020704150300411003120000c80b5541c0000d002117540c03265548001000704d01c12900d0304100401c0c0f000d900c0c818800391040c006000045084242c01000d03600ca60184805c6c40e55890900c41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 624324325 1250 624323075 624323099
    0x20403140319050f030c0c250501030f0603050618010915061707030302330702030318030408031912060611011410030311120a0c170324010306030b10 66
    0x40034109000042000c079900010084c2100e52080040740c5030b640360756a40b800b00d42003810340e540b24800c0c541000e451080021003503160078200d50098904014120355058150b0556405200240c401d40014001440b040205481160041403403400084c104c1c0131507a1b9450100b45289550414660b100810b1040e0307410802c2c00002c1e040090b0040003240e2841d0380c02591080380e40581d005001181d8509841410500016080c800149008400e285803010380250b50343c01c128cc45090144658801e0040c01c80007004540956001f000518a00400190100b940c070003e01c0c4603204201d802c90078000f01043c0c902c10720016003880d2766080d0742c1e4243c3e00c0b401400d5601a02c03244c0034a07075100d014420740980f00c040d000110399142c105140c060017441e0707409d41000e02e4684603200d6243c001031101c242d02e501443c140440380c464000c43c00c15032007000310340105020072100c58020342803543e100c2e1501c4414900d04026810149004261203071255103c4030140c0003500c1c5c0c10b6110285613005d00110300e00b02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 624325575 1250 624324325 624324367
    0xe0d1e1502090a06030b030f030301090213061e0c03050408100e28020d0f0c0b04060212090d230307051606080402241227210c010204031403 62
    0x15200358100302e440400102e20f54a03500c030703e100f419500c54440c9540d807000c0c00584000e0b060b0b9029079890f0b44e50f464a01e00a0750048001a0803181d11250105d22140501074040d100031b0080500d08104508030410303503000740e0301c0c0015001c0c00000e100c0050000420040f40181d0000f03d8400b28112900d0032409150030b03501c001d09001a00102280240d108041085c00b05858045400c40d80186440c00c08814520762500c0c09810700c61200d10104045078104004e0088461f580e003180c86000c04524600041e00580d502290301c8015252a080072500c80b0388101d00c010900c010104103191402412869907000d4034089555820400e8514070085191380c0c180c00a108504000c4080c1c86d05034006001c030044e82400201c1d1007410120744c0f0480040700c05446552200c90a59022424007800c0d048100840341802c0c800410300062032400c1e9080810581c1c40041140076410902e03170302c02447ca549411034501ca03450b543d4280000004a200c00650310104140240550b6552041884202001c4496 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 624326825 1250 624325575 624325613
    0x18090204050a11090103021c021914030709090f0605060c070608011508010b160204060e0f0a0b1e030313060e0a090e0d030c020c0a0f06121b0e0d1e 65
    0x3020340d400030050007080300c2a0131402d2a005a40e4810607461040400041c400f046920788081490300c042c00f40d4010300d005410309030300ca034881d07251482c0c0e05240500c411203550000031825442000040b02503040302d84c800454a00c041551030311900411055000740e050f503842a44034840401500d90000421805481c0980b0880c148401c1e4a2000e004507006100b0302c0e160b0200098a440b00e808003000c0440c003283d0040007440110b03514051001496002d4400000004100000c604070070807a11680380c04c800c0141120104013122441c9104c3c807046144141c0e0140420459052914402c1040801808217502c5810701000140103109850f065034100b0700c24103150840d01c080340840080e0005110050b40b50200305190365200c00ca0400704003000054201501c0000071032002d070001d280701c0603141c19580d0791090310403400604064a6014090707036100625901c80b40d03461403250400000282d0050400300c6107070001c0d0b80d1260701354100441d42030103101c1003514404101e02000080442544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 624328075 1250 624326825 624326831
    0x51521150f06091c14070513050f040210121e15060207180f0e0114070f05030105130b06030a090303060e0c090906040b060a02030417060903041e18090204050a 70
    0x44040400e0441c0708190380716204e08564180d08144110400d0341600055208880c4c0184410102010795600f10314002d2a00c11500b40c0594682030510f84a460320a0000b03079548404c586a6409001581d4000c681c450208038842c40c13001900c0605002da41104642c01040308401e0000800310001c55020a42480d0065000c0d03104010305580001c0c50410b03210500c01346103c0310030941507440140580d0001d4100d290074070b001c68058000650042588141c00350030a88150303105442103511a100d8011000418420f000510040c244400346854103c1f22010001d00c03841c8610000e40140c0049402003500c5866120b40c0301010781c58050140144200090000641800301104626000b688444c501444ca41d400003030b050742c5d90380c21250880350080c0207035680c5c402da490000d489074494010015600e88140201d41c441e10001955482207a000016500b881c3c00c10300300014100030101d01c107060718603107a00852034400703100090381d00558540d40061140020300c140429204010407250303070986 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 624329325 1250 624328075 624328099
    0x3030c0114060f01140a030f1806050a05090102041a0f04030b16170c040b13030204020d0b0405100503030702010f020c270703090302030405060d110705030a02070806040c05152115 79
    0x30380f40c02603886c090114100030603c9401048101c00400040302006100103107901e00c6002d001c100d6202c00c2c0207030314403c1f0601242c2da6410b6554280e00c00ca1140001e035616101e000500b840c1100c000d042e01034403003400d041c03516036240c840c0c0700740305c000740e510301c0702091061400103103a60441c0d0640000b400c58036070071240e0b1501c0807010369580610722075204121400100a283c1e100e000303030a1009150300500c11515907034252801801080290720950080e4601b0020511131440c80084000b01c075001001549014125401168041c0d2040610300c01e41c8541c1c04204042d40d581c40030703100d42c0341c441c101100384a004002c04d410300800c00350000e03060516182003007022990210807942039410540b1015900d03203020030010020807004c40410456500460303010708000300072004207500202542104c001e2a150a409a11030f50709550003031040951034020003284c200464043d00351459098883d0902c4131003602d50f2094010207881845070780c1c2da0002c100d501088103640e00615442a51a412642 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 624330575 1250 624329325 624329357
    0x90203280e061305010219020d020106050603131e0f06140610020d141c0b01140a08060409060b120703020102071505070602130b0406030e190b1503030c0114060f01 72
    0x2d015011002c440d00400c0c1c08010700c0002d404030361a24261640d1241c6640040d40c0007505c5692448115005500b403650002d13080c940202640e01540ac4045891181c09441c1e03100328003d41036200e00b20035130720108040800b140409213202e224902075000803400f0303042a2002481c010300200280e20680c4440315584400e0342c009070100c164002c0b8100744001c88d079a00c0b8000920b0046008448030f50400c4400c2c10034001044d00302041d120070130b8031050504001d298a0a80c1c5014441d020300018548800080d03203480c068100d94103c4e40550000036403030071020017003101c3c2801b01441210799440807104004550341000008004c2030794403128442c48c2640400100300c0d114041e00540307440d801144c2010007100358030941000704001301c4650f9603155604400b070040c0c03840039484280c42c000c400080e100686016820700015910a0380d84030b865841c402000128a00b0112207034051005000072010060244110b01404c0a006c0895141c0c1c60103c08024014030502c3d0128100564510002868 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 624331825 1250 624330575 624330583
    0x4060c121a090601050904060308040302031501060f120920120f0a14070506120412050901090b07050109020a0b0429160f0204020304060e0105100b041509090203280e 73
    0x16401200c0641064a0f00e800490b843d00444a100c0d500624101c000002c100b4050020411240700b40d0698040104a24041d40f55034424454013001c03d901100d52800302c0c4c46803460321640c0500c1540018003044a072201c4005440140305541c000c5120409009586418141c0385c02d0020400c00426440300c962051640f1090200c5000f0201420307103041c445058414082c441c00b400005c1c002075112414051400785001007501d060f10828500208110b94134402c3d000c883e101081a15111540d514054100e2407641c0300c1c40082c6e90039580c03214540010380d01d404e040c03401404800000c589a81c203010b088040c58850130020b82881d800b04440c0070004d0458419103054042c40880901035041500b00a00d00c0c890049000758014800002c010400400790b0000b05c031231503260000c2280b5914021420b0301c99020340180645410306000400c514000d00c0c1e15540c03500c0d0f0501c0c10030b256035a50900081030b60000e4807014000150141c1c08490000e4010b040400c40003950000d006c80b5083d6a207030794031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 624333075 1250 624331825 624331871
    0x50306011701060f110304120501021b01090b040f0510050916060215010302092502150105090601020703060c0302090d052104030b0705031305030c010e0601060201060b090d0501060b0304060c12 85
    0x180b00c1c98400f001180d06050047da0010540d10342480544505031070101d00030f600100321030880091690396202e24400c14031410700081c0c4d00002c8555140c5968440569451021200b1a0140b182c4030380307801e40320300600610340071f03803c0f1600801c0203141510240750b00c209160850310466001c0704000c41d10464424916044a40540d2060455100d00066450103280303101401020048904407081883d80000da03403800481884150003181d072103100304024803600795010341c0140d01c000300c1480444d0090b0f2000d039000303145060061902400340702103059080c1c0c0c1c10065819400c000c0c1c4200c12500041243d640844266209070b1406081da603400d85201d134080c0140701004408800541c4e40044015041442508036040700e89880e1122130310b80c040c003100c11066686008210000501c907005008030400d80e00721164650070b080e070f9001400300c012081a015901d81d0740350300002034481c41d25402507000d03500031305001c241fa4022010150054650320304558501d0710300f401098001c07100ba000707146 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 624334325 1250 624333075 624333077
    0x30606040b060c03040611010c030513061d070909051e0d0522032108070e0f0a0e19060609050d060903030b090a06050111071d04050f0706050306011701060f 69
    0x1507207254000403a010740074505030021644400100800c03c0341d00490a103107000003000080c080410150011000c0d220140c500400c0c2400c0741000c0000181140c0040e2203d1600c00945643c00c0c41201e81c0d185000c2c125441a013100b42d8a00d9940c0a22105000020192030034605a01c500d03006804031943d20101e05203010100000442c100400d11650b003041e61101c080c0b001300f074609540f64102240078903407088a0385800c04400700340c25542d03400f6100851040c02241c079031240b03c0ca0800148003848071103c0507203501c03107241c20000c02d03a1401b605507503001d448610404408000c5000e181e0302219000e80140b0305202008000704a2550342c2c0340e095010550044022862000300d2505801501602c0c00b1590300c040c5140c100034070711903568010f5003110000d0f42c9012201070300c5400d01ea11180580908440303040e81074003901649000c0b40075150014801c0c811900b002c1c0300c4002c40740c1002c00540145000850000030300100e580d01c11203c041c10050084521041c1d40342c500c010780000c40d00c102c014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 624335575 1250 624334325 624334331
    0x120403080d0b2214060901120f020607030c4407060903020f01062102010f020a0510050618090601090b13020f03041b060822050d090801061403060604 66
    0x249080e03465400210840c240908490810082100b80d8605645441c1050081519050f2440c04d000103826041d405190040c00d180056400c04421301080701010b601030301e00381c90310005000140c881d80b004001f40c07406955044580e04091600406202c66081c80404e450b00c02019014a11601100024102e1512214141000d000c1130303d090070b80560f0501410f07980c0760400680900d5000f103000548603d1050003005115207411903211070081d4200d823035446152103400c260065000d540b007000c05510b00d0044401400c500e03a2050f283c4031401002e850483c0e107035402d21416050100c041101000b40c050701c0c44d07041c5400074a85aa42a051044d21002a12041c1311510350311002e0b0700c45105011003009660390300e900881e01100d940280c8007120003914614440d0007440071032844405440d00c0e0b9440501c40d0321018503420700300b048007115003001e2203220340c6400090002c2024030710a41d0903440c0c0c500442d15003a0300390308503a01903000c2c444094644a510342c640d900031134000d80c0454112000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 624336825 1250 624335575 624335587
    0x3120f03061c02190801050a02040f1203170112060b0904020f1e0d0809090903090306011e090606020607020c030105070f120f1103012c07050c162612040308 69
    0x30725904103100c0b102a40080c603a000c64000344462108681c00c2d564500001d2000d5107070003481c02c0481c0f10741e03c1403442d11079045201b8800d4030b10010346000c10f58003030710340718104030b1603601701d0008240280d0080610001e00c4034000200b0a5134091249840012200c0003010f2505402190305966100041e42c03240f61412001a00080c5210594200c0705000e03051400094452074465426070010b400544240c0810002034540c04000046400c2c0880203000740840364a090b6040907104442203000a503264602000700d0400b802d03102c0c020041201e0f034000c11150403c048082e050021003000f507802139040c00b0402c02200d0f00910206000030051510744440c1a4044a00c1d009001881040d007541e410051551a1004514040e5040e9000300e00d542048292410301704c08068a0400c0108140d4850030000c1c0d0a5802400500617958941c0c081e10b0b4000c40030048440012515004003031703024003a10494903044003503030f504d5002004620003012000030040309034441d4059407100602c11035001800b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 624338075 1250 624336825 624336859
    0x605030f06121e0106120804031211010f09020907030b060a0e18090601081c12020a02030904110a0311071109060307090c020c2d27010308040503120f0306 68
    0x807004a20400e2043e01d1216601818651800440740302d0310400790708144010a070003041060040a19510425480c5071a18640d211390818410f04403030400e2002001d0500050002030180c1d0b41c03000c907903000000d03a4803e6403041151221001ccc02c802c1c10185030500b202c00da511030104603845080b203410903001c241c51040001d440a14940340d80021050340201340a200c07500000d41c02e058030680029500780c2540c0e503aa500d81450000b102400003542542042d05840d0654004c100b072141610549240580b0000031070256150740104600070200080c15841c1035905100e004207000305606840d2600c903490725110508940d5551092062901c4804110b04d80d0b41040070300c00514481800b03010344004200083e442d80c10703003070b9461301903014800240f4640f108400c070700c01c162a945003400f804403034620510800611614880d282c0404842c402c032252210a01840d000b0751041a100f942c0d981000706250400c0400f4807442c0e113003002440442040c440a5041d65400403080d0b07441d415620441d070f1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 624339325 1250 624338075 624338089
    0xb1e1303140f070507060807021209010f0c02060a08090d030c080a1d0f010c030c05070203060720011d01060603060303171506070501050708060f0307051306081c090b040605030f06 79
    0x10220710782c0c0c035000034400304002000c500c010031a04262210390044e45c0d1284180c3c4c8540d150500c01c1c2c011a07040000c98103960080b00340d030341034078502c0c508aa00c1d00b546078041402603006041d8440452511010031503204410040e00d20300000c90f28040c03088885600001d0b0010b88040c005090f019100c01100c141001ca8094941805100d20110b0700c0d4088504c1d40b0754020b00c4500c0039180042c0c10248502d81d10350054084071551a409001004076035a540400c83d0500d01c0c4140c0c10f140c8080428040034051800d0260001103003ea075024402c1d031105002e000e0031038146074050014581418010000f0a4004800781112029040fa4685a5442c4141c0f1007007080c0320710b1507a0b4044d4000c01e440342400360552005100c5c0015444e108826100c04082000d100c010554043d4141d0220205002c075040802c40c1c0040d6400c6a14086013507904e07003c41d03e040484c1e01007044010b90458282c44041548036400000402d8680031035480c050401000524512006042d41401c813140b902284840d242d00c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 624340575 1250 624339325 624339337
    0xa05221e02130306050f010308030a0e121308060109060806010b0a1e051804050105150702031c020a12140a051606090b1905060f09090a0b040b1e130314 67
    0x46654100b82140d507101e412850009541c8540b604000071700314803011107100c4c16284c000c00c42506594a6007210405418030100c601c6160040d1024030000c3c00015003e000036805580520007000e0500680503d4440143d1081c1d0320541002c008200d03020010030403506640b0400095941c80f0080801078404800e04862802c600c041c203080310251692010141860b2646001034982d807240d0241040140d480a004066212030741d8103412505031000d80040c0b410320700c050180c4070100304040c0c210340411f07418810540540c001c901c0d0307003007045444a50b02540e4402820140f0414008a80d410014010480300c0030078082c0c00a0381101d41c1c1240c400120106038082c4003440068550310709642d1281043c4e032a4000c0c0202e200c1101030112140c0a05442520040c10500f0848240c004105840a02502c0180c0c207000f18030b01500450042910548224007408213583c0741d040c0010103030a03d440d84419070340751000541c1401076000c10003000e1034a158041ca80b1042001311070700315030703131500c212 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 624341825 1250 624340575 624340631
    0x1120522020111030a020d091e18090203030c03250b070e010c20030708150f04020612180d1b1511040f290706150512010b0a0522 57
    0x328603d2000d513400a44613110901c1aa505040c8c20307030350403600c8207245101c0c100490b4240c01c0541404105090480d00b88810f424020103e9018a1a0042810b590096115643c1900001000c81860081120130010a4205460050030b03074201d44480120a0003d400d59041003010841e0110903880b4240380c9514070340002c3c0307030a1000560445418070310b4026140354028042c1250000f0701c250089400302400c0034440c1c00c15065590303400d01c8100703442d00a00490340000d041c4003100005019480355440b464410004102c40c0945001d0b191408100501c041d003008002595140e141040e4198070218591110080170400d05840000014162140c6102000341000c20005801c1c402d041c11041150703070302445207440399400810502d0200a00043c101d14800030419240061165400340c4140c0d14000d04c004030081c1c498001484140f04c00341c2d15010f5030744403480c603e80c40c50010100b034010401294034044105101c00004002292100b10080d00c0340d4462076003102c2c6c1820300112a80200d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 624343075 1250 624341825 624341827
    0x807060302030615161b0609050105090a031202241014210d030609020a0c021516030905100806010807030f2a1220071104060f050112052202011103 65
    0x2005c40003039040100000ba070f104102c401150030301001030f40345075055401c40d03950088001d08020042d5400ea000010031908a06103600010208a402101c10400c0042d60b016100314805075202c820880f01904400c03900c0480300003400f45203881d1050840031200c0b03034401c2e070022045600004402c081e0003165069042800d0811050070400400c030400035207480c1e102007000b9510350703005a080340900c25030b81c00860400c1c49000d0252508000400380070001456203860110082d2942e9628030100d00308802048042e9014402881c10000d8800003550030b1921605600d41540024000c040c094550303030038141d5420020b080310381716402040f400885c41c1e00d0301030200c1c01d00068850b4081e51880144c0041d40212000000c14401d020315200300e138128104043c0000545d00c540c0d9035a0200500310740d40d0110244224103501c550290034000c0210014846d01107103080c00240013402105100000145410104100c0c1c80039211106080440000324030501c4003c0d01c0141c1e00c0715142c000e40703507403444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 624344325 1250 624343075 624343087
    0xc05090a0b0306040c09050d0308040510020a0c030905030105190b0d0804030b0601081b030417300703150e0c12040b01030201140403212105090c0a0807060302030615 73
    0xc01e50000e42c0900010780e0108204070b1507400496983e04070340141540f0080000102021a2081c8803144d00117000b0406d642051211000500480e0701c80b11204c404a41e61800311010706070400040801003c003a4000d01892070b15500703003071502403a8030601d614a60303a03001050346512190505105182d1000525a2742e03901c1e802c01440d00da004403510f40c0001e00400010f61407410000d688810100c0130012182103442d80e0795903141110320281038442400090041d421030440c6224040601505003003544890142e50000c145180b0004001c00c05150408002c01581a0010030711011225146c5917039080e40c6980300032594a114044842c0c60508810040c00203011825103610304032403007600c07104000382c0e07800d20480c2da9008900c0042d0009000407081d00c0d1803100e04c08603520070010b03842c1503d035001d02078074400b091511880c9040c0303000303507613404008034a1010400c00181ca5811141c461603107250500c1a40c0e034160a000f00030405401101203002c0f80c490300c00b45803810a01c004100d460b02c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 624345575 1250 624344325 624344339
    0x80408120306151204030302070203030d051602010f06080c1201020409230f190903020c06040603140a05101205010902060417011b05041413050a05010f090216060c05090a 75
    0xe0010394155110318642030f150f0301c0304103440049036400840105052032a5860b500c1c01d50003034211a0301a60140800c200d490f884030094800c1e281f180d504002d5030704003803407010300003030841c1c21203281c418142d890f00e041070194200015007000b520b20101d4081c9400e01c2850b9880307029000d11751004488604103504440006845654820405031f640c40805907682c9480c441410140b054a24684e00c50801102c03082d41f4603950407480d94140240105e6121911900100e1842c0e441548103034002940d800010f81248142001142c200d101030764103005a06041d407510000611911a0109207100c0040c40400c0000a400c0050555001070003503448540c1c640f8001c80c1000100707c030b101a5480d00d03001b0005508140445102c50701c0554410381024208003400045c1018121050f034406041c41e61078040300c030361303026645c812200c030203020500d0751400d08490000301d003030b410004242e8018840c20f141a501c44001d044420741195001c16044c4e510203003a5402c0c0700303075010b00e50884500c2a002c9496 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 624346825 1250 624345575 624345577
    0x60a02010f051305190206030411210c040c03140c280f0908010c0e1002070320030105280209010504050619020c04020c03090607030318051b010809060f0408040812 72
    0x1c10b00810551316610717a0040c1240040e242e517540258444410300104000c80c0301c0720f041005904002d03010f0a0751020007004062a102080d030114890340c0081441d81560505005c0c05110007440c1c14140800224150100e248003801000c820030a0f40100e400a100e00d0582c07120030302042040b01c01c5004290410005110003403060340b80300815000000051141c0301440380307401d0542d0555413030088540d28800c0102c01540d1040c010110711803030001001107419050b4011481d0440c407200310780100314a00345825600000c103002d0103200c00c02402c004c1c0b2040860310b07440c0300301075000041c3d40d60302c00c00c0160340a00072604807580210000c00d084080850210720b8001340d4a0342d03001c407a454240b080400050740b090340340b4031503513070400d10a80919017000e00c06012614441e0801284d420744a04492880c458045c2041d1155071080c08003a0032810764000c0054248000e107800c1c2c0807864202c103c10740e02c410262003c00c2c582201c00004c0d050150030740a840280ca130390b40c16246c24901c058111281 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 624348075 1250 624346825 624346861
    0x304020a23011709030a1202090411030a05010b0301060c080a02120d1d070510030213092a0201090f020904020102070f180b0d1205030a0908070c1707050f060a02010f05 74
    0x800c07144403000f41c3c02c1d00c030a00c2003885403111400442c41c002c11500c044804c2d040e6901000315540e024814202c407030303031039026000d030000450742000d40343d1804610b05d0040c3ca0040e8444002c502c003c000601c041607103c0b000b90b1105401500640c0c0d624202c2034102d03d41003244409164500000c00d4030088078206400101c0c03412070244046200d42c507107a005e940c58413003600c034031396000c1315411003030219900075000b815980000009842c802c65851455005540c44100820800405145644004248c2482c0d409124929100801400d01380daa00d074100b90758100300c06071168400300005400c40e803082040e4409800d41001c0d06840c140c0d901503040c00c8107040c00300030728880d0601070050220708010302c4c415103050300035420151941402e5410b071403a9201414917510710340c840b0750020204100300024082688100341c03200c0e0241c9484640d1011104000e00e409080d04003220400841d80d0340b41c51140c613400121402a0b94692244044e40180031145520602d00c1c2850200000c410702c40c0718810f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 624349325 1250 624348075 624348077
    0x40914070206090708030901031e0905030901081e0a0b040f14090d02031603140f0a02030a0306090e150603010b031009030f0504060f0f110f0c130e03040b0304020a2301 74
    0x480c0e0b2100c2e40410b465560b0345c02000c071113900038049400c03198829046066443c11555601a444000241c1d45040d40c1c10313440180d400d5440061451b21650744000e26540c081910307036a40b9110109034840c1c5402d90000340c01c0003000c540b12207000400b0366a680c02502442894941000704400f8940320034041070080324001c1b00d9025901245c00902e00200c1154048020072286000c011025901690440100c1e1044c0103044030510210104074000e2000306030815064004584440640c0d80040c04c3c2d0b40d06030410711a00e81882c6144d01719000008100c140f503058984540e5065566801186c010704800c9112035151141c0700588603060250b0f80500300d814000e82c1e40030789541c07443d40c0c19100e070b11032441071400044807000d5401d002485075050039000d0540d8a00750007040c1030b90742041d1a140f5900201900c43e0411400c030206072a01350500201c8030002101440b80203e0320250b1920307070065203c1d100d407070b10000002808540e11014480c015003856001316002e070061442c600c19555541c21018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 624350575 1250 624349325 624349333
    0x405010608070503032a0304030308010e010f18050c0d110306040f14130c0e070201151a070f0213090b160302130b280302131a090909030409140702 65
    0xc542410701054400659001800461501d441c849152040101d22420300300c03c65484400a00840810700080c4011406940c6189003541440d03601c15221038181d1145080400c102d000700301c1d0102c8030940703101100c1c0f03010700051980c3c1c3d40c0c0d0349ca420030321580341c910203a685400c18102d095411003001d0750007041d0075101000860a00b410075800c540403100a55901c2c03001d2400200b4100d0000900192248102c50840d400c0e59218010b0903a600161403400260f516007950b2484105000d07403100080c003094070880707030300c40030400c04864500ca0500301030302c8940401c00d007106545070801c40780c14290202d04100302c96641c1c0d0070a60040d090959850542d02e24544c030800f04a840390007a02ca5040d010600d06800310314029995100744d100000c2a01648051401029904030345001d40141585030b480159840c0002422040c142e1155002041c1c0003100d140c03031000c40a16136080c0c03140004159031407080368503003060443c95401158840404141001840540d25042200e2a4000d0109400b21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 624351825 1250 624350575 624350579
    0x7150c0309080a031e110a062304020109060311090a2c01050f0108040204090c0303030e0c031f021315030c030b040e2d010e0604030f11030306040906110a0804050106 73
    0xb0548810310f40d500a40041c44940c11800281d03132091402000008605000c030000381200409070a125102d9810b6507a10b58501e1603070f81d0001c0d4051502c034901d140d90030b5000c2c6442c1c140d0001c0e1120340301d801744604240e941c985100b49409403608903140010024100346c4155503600c90360f0140305045e5003540745542c0192074080c11052040c0841e042e0340005040b5103944214800442e0003401c010004d0340d00c01d0301c0d281c80030003017407544a48801840c0203a601007051070b21540003514064104400e50b001ea403200d5600c10304c02070706004e054201460200f0142c0d481900d01003c0d258031075503800c208190302c00c0d0429a03400540541c0840d07150740c40b90f1024807070b100b11001040111030700000207590580042402c0c0c401560708c4014a501ca1801100c40661281c2c0e02a4041c2180c488204041c029880003085c4020300d50030000c00e00d1841b2482c0f83c4010380e0190b5100150720303404090855405607488410030410400d20760031680c5c4a10151040586410135102c00908100040d18296a076511f80280 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 624353075 1250 624351825 624351839
    0x310031a1602071a0310050603090d02061303021e0c030f03041e0b0315060c070f0e0907060207030f050123150a0f06110106031707030f020c13020a0207150c0309 71
    0x3880481d0790700084c034003048910002d0000740e60b00007000050242d580c0c4c5c42c080341603a00d1002641c01006404000d1622440985019282c0346c8060500e035500841c040991001030781c00038140394200d21866403500ca03041344969061070401390501d1f49074140902200321220750b000001901c2107c00000301046c401c03520001c440318903c3d2500814108103410000030305442d8101c2c0c06040b0541010b4159807500794200100c1c3c1c10100260090401140a22010840001042c1020790801a00400740005030700c5e2020103035507501c0502c0001d085251aa01c0c0ca018030500394409804c080c902580903425a60050542100100480f040700c140e114295040305a410080c401c4001d4802411461640074204070054806075040141d01d041d540d215038000c000030760b081d40c00d84141483d924200d5201e04103403030040c05104d1207440410441d482081d1a921507647c189050200c2d0880c201c00503901c1030800c60403402d1020702d41001c0e01000740d4a0003c0300e860384c02585401450300076600c0c80c54151300c0305c076 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 624354325 1250 624353075 624353083
    0x706090503180a03020a0303081003060c1d0406080a030807050c071d0a060303050405041505060708091309050a0b06010c020406060801050301060e0114010e031f0203040c120213020310031a1602 85
    0x13029422604030501400001c1c0104078007500030003a101c0c0d11500542d130340e03140702c203403526500148001116114030000c60210581c0e03800c50050101d605008041c10122030313550300c003060384010303003000640d80c0825210340c0039204413100f500000e8240d98040c0d8440003500c0c2100c0c0603d8a01040300100d00014140e2a0742d40300310010f4a500d5a2a146024a0001000b026103a03598824078100c0d0042c4000900341e51b403000821810340709448041d220071428080003041c2c00e0030021020001c2c01d0180c040d000410100d8101c4507a07510003484510750322107000407540180d04001c0250405d1501c0380101d00c41c2d40000182d4102c0304124028440c480e11813071305c3d0708030b0703d0701b88244840888400041c003520b40c0034001c2002e64010103000c0b28410075400403440002070b130744c410b0b50351255400410300050001c010074000107403000d00f140000d12079090f800b00710101c02c00e10103201d04680c04004543c05004030f0656000550b04084400b064070b04400c065000040d003a910540350b04945800040344a0002c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 624355575 1250 624354325 624354329
    0x13090509150708070225170105010e09192603070903110d030905060f0c10020d0b091303120b03010e0f0c0a1508071b080702010f02160b0f0706090503180a 68
    0x5400f0b410a0460501c500b0f0942c81c44428401211403412070200d00ca40b54000090103110071f0f01e0021a0f90f5140c0004e040f400200a0503003101c6812903c018060142d812a845038081e920029071913032280403544488070b900f1940542e480e010700010611003800d600c0f09542c800d03a0700a03080780819081d502c2c20443c043e426018000d01084000074104110310300803001c3e100703000141d00403030b2038181200c5105081003000100e100c1c0b007580c089010009207030701744070300e0740c0141c420ba80380c6101c1d050450902005845882009080209107090400300e45010340140d850184040d009000d44081c00d20180d4880380c112165420314481c0503000706c15480d11443d014111280102e400f5152068100c1c111050f2030300030801c0f018003050f8208041c5070070389003981c44401401035021540f240f04a100041a148074403450008540c00b00550a07030002540381d4510441c0d41111000b6540c0011030020b020601403184040d010501e0304160304180000400201002c031318064585111501072010400f0046d414 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 624356825 1250 624355575 624355577
    0x140f0606040518040809030105040f050c010c0c090c0315080c12011103041218181d1b040f050a0504210507020f04241e03171309050915070807 63
    0x60b5103001400f1a41c0509076046409401c65034a07120350440170900703582d825502205c24089890300001482010f101034210342201f4a00316180685985910100842900658440c2c1380e035843e102400354001c2d408071802410510a041c80760f56291080f45e1a0241140d10034007842103403844041d00c20061050115000315884500d04684898803602d003600e20941400003030000e80441c04e0000301d40d2405020041a401e10200b0f41d008800d0031040548000d803803040101c0350703500741100e5080750100740300404103180c1e0144090755012000040140000700c101c000748510740f0301406210300d4a03401c076501c902d0080c00b0000068640c0940894051640390136080000c074240040b0005250050303800000003c01130001c25220035260000400e002c1418802c40c000013130720070820080f600621080540c44031081900b013042e1642e15401c01c0800441c29480c00310100007140d251000da001190380151010080800c5980f82841c6450340d00c000202030002405060b0340028001485a04418070403400d1b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 624358075 1250 624356825 624356839
    0xe0c150301080c19120c0e010806010314010b102304090b0a0b07030203030a0f020705012a0201090b0112050f070803071110120c020304081b0a060e15031009140f06060405 75
    0x2030500e1816a01400b051708a0303841495080006170034440302e4405000e8005072001e00840c0d4910314003d1054480401400304036410003211400d0743c0d540d1141c1058640c0f05040044203000481031400303070703103202004140080c4000305002c02c29110319440604074a005845c5444415291b0140409902904000600507802000040e012026035000a802c40030b1010b0054280390040d99003e09550154441c820344070480c018040e000c5001103c10a130103c610300007008010060b4880e204502c034140240c6030004072464001c1d04121003000344ea0b00507040348040d02e1007103031120b8030144c907030f40420000c1c0c0d1035040c0340080c4502c919002450070286003079501c0d50044c1c6900030100310003400d02c2000070001c0d400305020008090000340402a42c1c0005a002420b141c00d500e030811403401102d402007401c11000d800001c000740c5443c41d00110710301282010b56107940d144402000200c9190b04890442c07400e203c01c2d503081c02d4900b14600e024850f9100030002c0b9035948801d02c01c49000d98803406503c00d01f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 624359325 1250 624358075 624358079
    0x80f03030108030f0c0a3906020a0f020303040f03140d02010c050901030e0c04110706050109020f07030c1e210c02011b08161101080a18060e0c150301080c19 69
    0x1613400014400700b0602c8059076445034241e25415147c1d8050040a00745640d0003843d4128003200011303201e800d203900c02130481c0701428450001d40e11307960048024000704441e9180e50965400304107030340060070208105024070740c49161095685010001100d402e108420102c80858010f0082441241c55a80d40a0030003580e580110060007001405a0540c010700004c0106502d86008101451509103542550780129190240c1240e0f4160700c0804400d206000340144196500215515940c140c54542405640c9042803480c4d004640c0e00450800b803903451090030019400a09210309241c0791030601c50012810003982e1031100000001d00180c501c0d6100c0d05116122000f54140d5805034011a08000401641c030010b640c1f4118142d9144503045e0070340c00b056078008681980984a04410711892403d02005200c0d0243e50a0061000c0e480718074840c40580c04000010302e0003402000b00300a80c0000303280c64400d03030080c0100c071400d020703400a042090400301c86402d100c0c0e000b60b001d17004440c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 624360575 1250 624359325 624359347
    0x31207020306190e070608060111030405090103023a03030605040b13020c010222051c0f061a061603320d0902060a03060e070912020f1507030801080f0303010803 71
    0x8814080200c035803582c035004d8210000d4104202c1002c4c24807611008041e0030304500160009407075009402d1564400c00c010300840e20b8013454141100d90645a825112207100380c001c0132007041c52443e8013801c08504811100000c0200c0100b18203000b520200206901c460600c01034074090704c0125004105905051000041940103200c0318100d03900045c00c25540b1141c526500c0080c8074201c500c0ba000e0107051040c1e15200e034203c03140400f4281807419110030341e41c030300b4410100e554002e06056641d80d8030201d02c003503181104034004001418690b44000c0e00e0402d41d07004041ca80141d0001c3e03041503040500c0e6104480c222140c0343d42c3c0700101c072a0480b0303038001403003030344141110240252115020f00c0140c855a02804026600380c802082e41c50a001d64000e00700c0000f4070800800c2101e140030000d641d08011600714039601540c181d0041d05090001c1000941c0c00e0300401c121042c00140c040a15074051041810380321840181c810728804001c2c0c0769039902082c0501159500100402440c81b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 624361825 1250 624360575 624360601
    0x15010f0c021f110d050a0f030908130e0901111e09030a1a0403020c010926012030061215010e09100606080601030b060c0f0309031207020306 62
    0x141c4018800094109803250225100c1d018081410200e003154800c1c2c10710180a218803e40d40d107092030005c0c244a001d80c00140225502d0588400f410303a104c3e02c060034445140c0860b21050003030408496001ea8981a2924800044903240c40e00d52814450100c100400c030101c1d1100c3c220124507505000ca41e211029040e40700d01e0303c095240c440c0c4008000040c0709202c281c1403066003051250950300e440d090281c1031171100c4c50154104030f0295402e120055800c03144c2c1e00407c5d02800c503507082e110b180e070065004050703180010380d121507051098100c00300440010440120341e40d9210061200d1500100348000804005106080310765000607410305007040c40e40f10800041c01140c1d185800c42164a000c2542038028071070b140d150404000d00c6e1001040445080c0e003100401b0041d50703180003001495524042c01160406486100c981c81c8e40c0e81fa41e051381d80d51131010054901d86001c004005649a10500740d541c068015481038540ca911210161416550090090b101c1c6a40f43c900c01030301 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 624363075 1250 624361825 624361847
    0x5010b0409290f12011109011d060703261602010c03110304110102071706010e01080604020904060c020a08120f0105220b37120c090b010c02060f07060515010f 70
    0x5510404e503c8030f10031003405038402d11102400420750701c16822000501c032415240c0c217106000c441060b07440d019180c40301110181901460b0840c1888071800c034080c0e400d10401032001110703810405001200c980e601404501c60040d070001c00032861151810381c02c0d9680c071303080b4040408041c8002400310f4140310f1181401c80051041e2135016440b64542c40d01e12031540d941c0d00941d0b0103600144000c84e141c0348440e0240441400030845031906500058145030002c1000701a10349403907088c2e8159008000034210958010601900d409101c6040c052160b012110590103000440001501b400c080e031800145e6401015009290b14502d215080500303940ca010f1504800784002600312809007005840382d074058011030f8100702408480c0c14281c04444d8120703d0340ca96484800301c00050303000f1120411a10319000128440b03d240c00161560803007114082c1d0091400582d80c0d03800f510030f1004018175807003078000f044291a10229481c032280b00d030014a000c10981c1001124030743c050140095 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 624364325 1250 624363075 624363079
    0xf07091a3714041a030a030c02190602030705060a09020102030d15050a12021201020c070501080408040506030106080a0507020334023309090601180905010b0409290f 73
    0x40340e4109000d041c08a600c0d588408034640454403034440038a000d0051900f0130540320784841c4841c0384840000d850300c40e01d90004042c042c00410f00407c54886042d41c03090b401200046911250365040040d45036481481c04a84a010b0780c400140010310601c04c240030070f40c041c2e0086042c903016043c55001061281550b07000d04030800701c00101996112090b10103070034624141c1c98a0300c1944107004203291140203c0c030341a4014409801580d0001402e901151000d1078440401d48940c101503510b072081c0e400458200380c001001041c07441d00141d0043c052140420100510f60316004200d8a034005d14000d1044480120482c10b40e500340c10703828110301103401d9414500b410180d4000b501036200c07030034a03480c1d054020700e80c2411000d000403a40604045203040328904010b00740001e0310b6038802805a8144000c155010002c224404e1a400241c0516901044156140d00c40c40320b1a070894400c0e203408900300030f564040440e00c0c60008a0b0440314110302e0380c00da07000c44100119800b01d504019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624365575 1250 624364325 624364399
    0x80403050f1c0f0605240706020705011d0a0305030c0a02031b2a0f01031112010e04110d0b0c030c0d05130c0816050904080c0f07091a 59
    0x710303003100003009004800760000c04a491103444014002580d0640c10038240580c03030b0440822441d121203201d01c0d0590320f4044040041040c100007440180505140078000d00d2004c1403200c20041c0560000c50400000401803085203a40c0014a98070003613100c000b00092000c4c4003180f01800c0071006049403020ba401501d003486420418070404000c070f42c6405801e80d200f90506071000c0c0000903059080b10f600340c2c201d034001c02c0003408180b00c0e01b01c100545040580e1124032080240c000c40c16600070000142041da0315580d10401074891050588040d44c821844030808442e9180c40c00d14000d480ba0b003c272203110540e641c80e00398082a040200240004c040c10040440b904520f4400c4038070514440080b02c4145c042c0c1d041c50b810710a40c0d034200f0800c0380e200b201301113144095282c080d01103d404841c200816503039480c051050340120303580c0880620a042c000114880003041c1c1200341c03010700342c1c00c10800d1015030703200007002c5c546155503400203400d810790340b41a4000000341010b02c00f030302c80704 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 624366825 1250 624365575 624365587
    0x70e0103200307020106090f0902031b010201021b030301030303050105060313061e020c0f0708010b01120203070306051f0e01032003091c200a030e0f040b0402040602010c08180d08040305 82
    0x1c03040d42d0720031a042001030355a40310500540300248688240c1c1038040204201503411030380030035507500f4001006641c2e40440300d1414101e80c400d4046405d070580c185804000c3c105c4403c485a40c90f0400c0c04202e0100b030902e0004241030502c3c0d1b05482c441d03c204061074100c20055141d030320090082c0c56070a0404200454a080b400002d8002800c100111600415030f140715005202d08103046508126410790410010340c0365a80c0c411540c50002c41824001603882e2a945021760040089600c85500a040354a0710000000e40011804424404d5240c003030801c00707c000118101e0341600c440d1007829441201a480e101ca1100245510000b04c40803103c0300280c030400d8040162407860714500003a00b5151500320005664011048045410300400812100759005003003a240f6151035406603500700c40b144000d5889402c01202d445000d40110341d51071725544002d0190482c50003042c0071500d81c1c00440d0303d0340f58902068200c200306501410f03c441a84004803605c207000380003a000c0000030f00c50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 624368075 1250 624366825 624366881
    0xa0803010b21100306060e06060f0c030d0908030109050a0e070b160822090c0905040c0c023c06040b031e0702070f15020a1b030503040f050a0b03070e0103 68
    0xc15809040908000f440c29032861500606450046e00180c420034400c109100283d26000e0036100200702c200c81440c0c452681000d0140345d801500c880c0f5285034184032441701440400d03c0154140e4076400340c14001359440c04c0a5100703844041c3c030010901e03444003104010b000000000740c82c550707003220f1900d03001c0f46039601c4070055900802841600c0e02c60303640d4414a95803c1c400104010000e401091090601880d000f4084e03488078400c0e103001c3d035240d405a503c00b910440c1c0c10013906072b009068827440c52484000f02c01c080060141d0303880320400c0071031517005529403445003094008000c0100349017070706051144205800c06018501c01c0c02001c0c0305007504109500d600e81c070600d400d41c02040c1281c60240842c000ea1020b44c05424030052003903030000041d03404548c6040c0550000c00c19080c06035010143d019690382c99101418500000c02e000c100000d01e04034480446c3c01c2126109141381d258024192a8402a14080041150000d90004550003500040c0c14005205040030403611070b041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 624369325 1250 624368075 624368137
    0x504050409050312090d09150e0301050f0a06090b0f150f070302060403020c0604060f110f07180c1b1707020405040f0605012c0907170d0206090a0803010b 68
    0x1200b110036400104070362481c070b240c4144140d4801d51407001070060021003031015000b80f07801c1c0125104e0801940e440c01c481d60041c00d01000b0580090001c214500d020280904040001d54113450b0140c00c1000c0010091081e0182d4054110000e21414010340c1450410408003403a1050024150050050082c510071034409801070340c0c0290040c01281c0703010302d002814040c00102840c4188400e1000380000c590010480b020008541005001481004a01407404480f860240800d10501501240160a0310250041c86494100c01d01030003800440c10ba030f513800300d80c10306020303403168655500c0454001342440000a02000d41585091516004603003503480880d4180c800301d4038100c2c40130410055100362401440d03aa00002c1c04200d11800302d04851b800b02c1b04203c4801c08003804943d1013182884010000c0035880300c0c44981202c2018200c1c0c0b0307181d00050010142c0148400991500e0004c130303030841d5039075202800c5451030b8204902c44030a03803c44801c4501c14040070036100d4107180e07014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 624370575 1250 624369325 624369341
    0x100306060308040303090608010e0402210d230304110d060902060d14090111041203170709030b0906010e04060e0312071e17060405040f0b04080d1109030d0e0105040504 74
    0x110b405591a82942005404042907034003a00070405000700400c640740030716004a81140d070488800030381110008002d228080c0b48803c41c820350080720729065025401000b211007140d4186850803001c105409400e045e404126006810001032810851b054a0a80c155001c40c070701c11107001444450315004100c16402001000f101c056440c83d4440c03101c805220034590101c4800001c3c07105c0164542c07201054040c51190211108548866008140c09140c03004064030019a00d18024903000c040144050003500c01503420240f400d002c84d400c550042507140c180c96a600707911000c0d8440d69a1a0004c10b03c513590b03d0098001480000340071181901c0b6180209000d40d15495100e00a40145c50b00b030343ca8004000a100c01d80701c10700030011030443c049621400c1240d001a1554490402c144009100c1c0001440800780804120410941d5000780821000c00740b402c000d210041c10900300a84121000d860b8142e000f80b141000c0684980c040743e8580c0010f02d00141000d940e0404102654014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 624371825 1250 624370575 624370583
    0x30e1c020703140c0a05040e0c300102030f060a0f06081b03090d02100204030b040b040618060218010e03060a050c09030a150b03010506130905280308010608060310051003060603 78
    0x2980e0740c031140d854a402440094401103404000f40c045040225559070320b01c0d660b06000b445003c4ad40c2018961030075159503850018840d00e603242c200380c15160b000754806c6038140c8049122601203251810803920513000e90b103145290000443c2020360581c0c403110003c0c030740e480171845407010802520340100a1030191141d03100030843c0d000e405e10003070305080c0c000103202c0c2c0c0ca030300c140f000700081044104800d8019030440c910110076161428041c000c2c0c50800b4040650003c0c42e580c44007004656030041407441e90b08c15502c0c030090f90000045800780d042c0540e00d40c1c1948a1000300300700c08440e03405160402c00c0b0310900c43c075028045010074200a803040080c0d410100369100c240240304240901c1303200d110100c0007000360b443d006c80014540c203a2980340095169480c18241d080107401c2040090300255002e00c00410030410b0f03040c41581410000c100c000641990000a801e0700565000b806103100501501000901c2d214000007000014000894024888800000700f1414480d5074055401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 624373075 1250 624371825 624371833
    0x70516060c0212010c050a081b0426060403080c09120708070320011e0c05010609061410080c071b0e010812030103051b0402120c09030d030e1c02070314 67
    0x100d0700401501001c4601260904c2e4107148030081020783c007001312080030081d400c00c0816a203c0b00803001c2c03880440d18050560010009001c01d031200e410807118400c03600d4051072903214068620064a9100948004000c0713210100420810b404110207440c0441000d415250b0035282154514644005c40d44144969000891b0a00a0200ea035403030792091071002065807c0303000e204c0c0c0000d000c40100c1d5004c41c00d076020026941d01d0715124880540c411078110000b406000e860b44101c40c010082e5114800091540d1006061740d820080f4034500380181948a1018960700d074250300c481030f40841021145603009485c01c0c00a080004800707000b6096004d11541d1940c100b1000522308181d048201004c0c0034107100400008038000f50680a50000410903250090840007242c083d000b40452032a022012a0400c0702c1120301030090301090804a00b194900c0ca43d00c40240c0c22500c04541184494112440c2a002c0400840c01c031031500d0f080d48110f80c030480c6e03640c0301c81c1c90861220840c3d01003908 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 624374325 1250 624373075 624373097
    0x10032d090c0b0406020f031e0309030c16050a06030905060103030e03030f1c0b03070e010306110409020a020c0a050f09060405040f0b07090303031a0303030f07050f04030506040501061a0f07051606 86
    0x541000311b0051090000004c0d460820440e40603e07850000c90380c0d403500f010b000800500d488005005a0ba505811078044400c80d1080c6112503590b02e8050144c90301542c504080092058424001c01c481c0a8009001d8003040e4216101100c44400a000054042c401004a415500c0e40d410048c10b00d8291203107444142c503400300c00c403001c1c0c6902c000014800e9008440c20b00c4000aa51082d0b411a640130600281c400b0b9a02c6040541d40119440b481d090341c07012805451541d0041610302128a0481e10700050030340342c4081142c004401069103410004c2440020003a0a269200e6038100e40514000840e03070390b150380c0d07912241c20f089404100185488000f00201a018000d0b0440f1881b042c08200900c00706401190b03690000500c20140c42c802d00c0040381d42140114120784100301007800303030350380c6a8a0342455030380d66400351030484841d840d02800082c14000c4080b9007440f000c803820345620346170b803481c01c7d82c00301d401000c01925113000380e01440960b0000c502d81074008001d0350302d41c2d1560b41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 624375575 1250 624374325 624374327
    0xf0a0612030518030307020109151205091509061003020111010e010c050c0d050306060d0b010309170a14031612231501140313080708040e010510032d090c0b0406 71
    0x3d89000c1c030b8005c1d882848014010f0380c1180c0114151a8034080142502828002c115000b041004402418918040c2440640840407034203101d403421100e01440075071944030f1510b0703803001b04440b0301ca490030000c2024001503210381840406e814001e00046010201c00e03c00d00c3c00c488501d803a030808104005509070313240c072083c4084031081086061241c00e5203070110104a292250380009140320340e0300c20240401d030703000c0d038002e0804d50380004040881268820401105034811440c0702e01040300440141500802e1404891203114800313500e60454803d41c074240d8900d4444251b985d000ac0c1c66045040c0c1ba4100750741d00301911401b814030140c0a040078900c9545103101448003a0400400c181c071040c40c1102d042c02c0703940120300456a03081c0510301d401d00094034028840d005044076170020f800101000031044003410b03290226100d80a009102d0425012940b2048909075005190a61301030300081501c01c0800c1e543d000706001c130b0300d81702c40d998840c282082900321500380c01d40403070140041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 624376825 1250 624375575 624375607
    0x3030708100e06030606120a06060b0904061703120c1207020109171e0c0c0d06020a02151303050f1b10060501210b0d02131a04050c030f0a06120305 65
    0x18003080150182d6801c00c0c80201c4c0c0ca0b014000d0403d8001c45c0c1703030842422a98420000600d00c1c035001181000142d442d520000b600fa80641c880b944150b0a01c0408079001058040e9408222203801c01540783c0070503150070710880c041c01011158403003024000795030300c01d5080c14264461810366000180c10f904910f000c422945442c002411059000d21414880c03d59012103950120300e803ca01c5600c41001403890752501d5003c8800580041040c402d61080000c681c001d08882c0b80d0faa02602d600031112078207040ca0340030444401c9814104442e524000c24007810003060103040000b002840c201d40e0510300c010703058000800084d103602248414496880600c20f010181200340307031088030b0315412003500e515000100300790400c1030f5481c0861100d50b520b5a07505031146501400000c482c24000400300300901c00c001c1124013200c0782103140400780c034103072003114800c50603203001d10305680303a51203030746d030409002081640c0b103035a03071403010841c1c0074074030501c41d000c44c801c3e40c82c00c0e0781d0f0710755000550309 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 624378075 1250 624376825 624376829
    0x90709051509130e030c010213050906040b01050711150403050a060e060628170a15021303060b010c060203161404030b0708070c061a1825020f0303070810 68
    0x5466014464000b0954030300110000c030040c000350201d20344c2039a210b458254469030300401640d62001462030b5903015100341c084100c80040350b90070b03000c0ea2808140010f9071410065180040c038104614400124041141c5180c1d02000c3c0540e088602e0319080c071443e030350040d0001e980310385c0210a0a03080002c01c0c0140b407580e80540d000b400c0c65040420214100c801c4441e580207013040300d111084159040e2101400003019914617518180405948280c2c90b00d1075a070040ea02034a2081c00e00003004114000c6403484881d002c2e000d5000d5145071500f40003014907204442c1000f8080095501060260010350b0040c004040d4002a0041c2c00c9400385c00d48070962a50001a5003c1c001040405e44401c0510f52003c60750400d84100ea50b94541201c0e01a42448002c28403842d0640c0c04441e55614101d1207517010060340d904215190019000359040001c96100d44440032840d000c00d14024010351281d50000540111600e1400a0140c02e00310b8108442d0580050030000420108031008404000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 624379325 1250 624378075 624378109
    0x5070201060b09040207082206091a120606190f1d18070c151e020909010302040f020c0102030906091c080f043e030c0117070e09070905 60
    0x70185404110b03031480c000d0304500740c86250b01040384024059101e0494040b072805080e04075899007010b0081d0380c002814060900059500c03580403031118440602801c0076441401020b09090b200140386c4c1c1351304001400580c11120074003011902510a0a0904020b00e186c0c45410000c0e2440038010001002098803070042d028041c40c40301181c50700c0306001070100403c0c0e4034000c01d50f01d03214243c03030303c6c0da48140c010402400408401204016980140100c9416040780ca1281c03030054101401c1c0d0060107a02c40e4099001401040146041d6000901d0254061009030414803098099802c90f00215240301170b07500540204810103030284810a80007203109282c54020400030002425074400810303a000c4950800003241c00c0c844c070b2000c10012a031110031284150103031650808141e480da9417043c41200c0514180710440c2ca0013180300b091512042e980c482e0300e20030440100081440c003402c52014005045000000c50700d40c103da00b40300310740c2c0c2d0301e038aa40c5030314010900c40c0800a00c0f1101e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 624380575 1250 624379325 624379331
    0x2040905100e1b0316180801060311040c050a0809071224110a030b010e100f0807020f0d21020a050315060a170406151806050d0807140c13090605070201 67
    0x19020b800c3c41d090365000030300824142482c00c2d0b10002030310800c50441103002d10084140c00010440415040715042c1c91142414820101c0c000080c441a561700800c642d012450602c10034100c280301d0a0b1656100d00340000700d440441e55002c09441c1800d01000c01e0754101c2021541031881450400c0d01c00268038a0401046101074071400c861a601400f1049000c058590844105603032040c003245191080c000c0c0403422801034120094941541024842c3c0030604010000b050140089010000c954000c409010f1145404100322030820200600d0180b480e80c043d44911059120301c0540b614401c0394459030368a08001a0604420301480e120b00e06c625410440d00d0784442d4051214041d1812641080e0b0f865265842e2500261444903803054014502c0c0000190004400303250b04845c04260f10204400c684032428406c02c2d65407404068136965040209000280d03003145810102c1d003801095420105c1040c002500740c00001100d90400e54a4108401c14890944546504a00c03903000030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 624381825 1250 624380575 624380611
    0x303050310090507020c03250510090b1201060215060109060f110a050601050a0906050d02010e04140f070f05190e0303040f090203041a070c110103090f260c0309060d02040905100e 79
    0x10f010380c2115000d440e0054070b401c400d24100e80d010b484800d01403c4a009641d8841200d00714000c8de10509120300b00c01840391000d4158400002c0a80364043c10040e55800400c2e8204001558245050189401041140b640c0c14100100030302008590a11610103021107500d05000c02000744c500380c10010b8213a19242c01003005640300c10203842445d03030a00b0555155902d084c006001045480701640400c101002007144070507442c07018511038000b5481c1c102c0c00c2c2a03c0c06045403140a64814484881c200540c1105650700420725020b00d00002804c80e4030f000e0700c40c3e80091203090194004403d0396004802c1c00200694900c8000310709003542c1e5201020b2412100042c41c41c410400050181d40a20a405099920a80280704c2141c1c0003e0030f4040d11485142140c1029042d08034503035880707419419200341c614000115038440e5001e500441c20700c015401000381a0b03010f80d181d03d168940c01c020001d091160703030141d584580e507401a0181c18070b1401c40c668103403100c0203000d60910f403904254 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 624383075 1250 624381825 624381883
    0xd180605070f1a251407060902030715020f010501050103110a0807140703080108151b0f040f080303160809070b0c0a0f0813080106050a0303050310090507020c03 71
    0x141e80c0c4240e00724500c6a080255818109952540510084680140714040103800109108003600c2c4006034602030403611a0481e08440040348a400d904100c1c000308406001b0a070941c0140155a000400b9640301740c0c0d4031482c801c552140e000c11032002d60085419260220350a118140c0100000c3c03d0511038200e400344141c030b0610800d0614800e101c1c000022411592040204034402c2d800c904099580c1c00c06800e01820341d034800d00c103803010340c8182d8600118020391343e8441c5001d4100e540a524890761003a219001ca504a05d54208451506120005088140283d144010714552000d1503883c2000c84440c032541c82c00300b0901042c01181420f00c819034000151003000ca424104220381c079a440845428102100204040d02074401c0c0390784c4d0f40c1448400c60040a0300c0550382801694207a0364088a42600c00c1c610652340d105101540c1040800c2c054001107501074035143d444251103881d941410300300c03002a00c40d140149e0100042000d41c1c10100304052901c00c8a103101000700c552468 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 624384325 1250 624383075 624383077
    0xa0312050d0b031e0c1912030512010e01060e120d180e07050307090e0c040b030403030e060103110a06020c0d1101120513020405060414040206090f0a080d180605 71
    0x291080000009003911004180d80c4203441400380142610b80100040855038142c8944444c200001d004540c0803000c2840c1070300460381c4481c0340b144d102c08010326018040304a404818410307414064200840403d80212407012406000424585e031007075410b03d90010031405840c42003500424201e0071030740c4d0440e40051055644c082524013000101d281c540312903400e40c115809001044c00308418048040c0e000030207540b00b500595a403d441e40d9aa00e218202d1402c01e980720780000004201c28015480740b60021039205003c1d0034046100e90203030304481d2500d0001d03401130f105c2d5420606800068903046614800030b0000384010002e850040e8001903058404010003131a010a580049445901070b9030521408484001c0400461502e00e102c26800012440100c3c0710b40d02e0540003c08a240030f1107022610131050b01c02c00780e81d41d00e82d401c0c80740c5680821921a840704020b4418507156640f00e400740f0240501001805c3c200400b040003070800c2c541c1c03920700c2c8a00c00e1100380070310001e6030180c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 624385575 1250 624384325 624384353
    0x1e02031618060b090328080d141e010302060a3f09020918010e0714010207050114090d14191203050402030a03231603120b0d06050a2301060305060a03 66
    0x31b81d22161580707421481188014852008190000118110b01c400c8120741c05008211254010a29a95104110510852690b58200340c4c00080100180007508105000d0140d581980c2030250032007401030000040d1703031801b90540446026040f14044880905c0340d13051950304040343e0074000c03c4040c0d4001a00e2100003802540d0ba44000046069802800d4210241d01ca0545050303541a0b83c07074040c2d45090b000c07194003a60161007079220000d241e5124075480401c0d9030321608114140320400c030800103156045a005d603a943c0000840c900030031018130140700d01c0541e501807402c487c07105d45048041c04008000c80c0052526100c1003201513200450703c41c94042e030524050420540b001d00d84480300002c4106d8081501e000f0a14803601151201c00e07039003c038000d495006030b0100071004003050f24000003805801c80c0312034407120005000d0340c000310b07080b0031034a83c04280801c00342c1c62450302c16901d1000d04080034110300104040d0350107109864101205885910000b030560302d4140c0e100c0240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 624386825 1250 624385575 624385603
    0x709090b24030a0f060b16230a0b0106170f0414060c0702090f15090408040f0e09100b132706150906031709031e071e031e02031618060b0903 62
    0x1e0900c0c03408102d20748044002d0211000d080801230608203020540e80c083d40c10089440340071010000c034000c1e004242e02d40b031701110303c0030040d09a80c442120501a04010b002101c5400024689030500c0d1401c0c003500d88141d42c8100d101b91207507054010042940c40c06048000d4502d101410320503203000d40d424510038607500b502c80e41000d84031458903949511841e84180d00041e14440f011032440c0307062200c24000c845e0242220344001c2d000484c6002c4a00341d10000e41d0040d04510f101210fa0701c3c1d030b0491400e044910840b01c4031125050b1903032a01c0c148804045500d0383d0b840419042ca0703075804171030030007030180c1d610100b01041c10b6503110800081c03c80c9241c00c0c82d030701c01b06101115942c100011004032203100d10349100000700180c895901e09082c0143c1907410007240c0b00c041c0006060080804403500101c50800559522080701070b40e02008105070707098001c840345422500c903400305602c000c00e0035800b4075080c0d06950340b02e01c0464066402003200c0f00c1d17040100030115580014401520342c11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 624388075 1250 624386825 624386857
    0x5130302010c021302030f0a0524240c03040602070b030c040308070618060506041b140a050f040f0614030403210b1002010609060803030709090b24030a0f060b 70
    0x1107800041c2c0324040f812000c4d02d00c0d900001c100300350b0070b42c044106c60050b002904144526155803044c03100004421088c500301400d54250240540742052800c104c0c1038000e81c0c0c4031001d0309208940040e6910a0200c982c1503480010100020780c2d04001003001450f404d0010f90460400c48684003a44c440d9100c060315003d00816684240581d9034040b01c14540314041740c41d600e1043d0314000015000880f004c42c070032482c00c12103e50800c0703040900c40300200140d81c1c002030100011032805040d0440340c0c0d003204103c024421404500c51010046c006000c0d80244840500d19200e4002c02d90300144a45d80c2242006105020019400801486030382c17160441d840c40c0aa00181104000c2441c0322400e9885403002034010510398041d80400107441503224244800c0d6192941c880c0d80740b20550303440c2e0002e081200104084102a8014603905070b00900404e00c0941038a0120519081c003050410891000024030145050390b20910f681c424080308188000c5180c03150a8040303002d030350702c01461204 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 624389325 1250 624388075 624388097
    0x601290a022a041b090b0c0a0f03051b07180903030e07140f09091203090109050303041a10031101030905010b060d090b0106030b0a0603230108010c0f0513030201 71
    0xc0240142c00103801c1ca410764002d03900451001201520300750026034062480d060120741c1c0c80300c0c1c002e402102d618a03625110b1803903281c450040c8080e80300010b0f011050007964851070000e8000124200020b001e6030fa801e407611404200314802c10a061969107060b40714440400030107600c2404034280d002400d034000745030185801c00b600645810315074200b05015000000c1198000b00c114541400c40a5503030700002400c03102031128051083d00c0c01150b590150070440d6590702080011944034048000103d4030701c0d03c9a984c6841c2d03400c140da0403940007051260000c1791004055045030300105000c01c0d10000f901e180c451500699180c643c0c241015201c01015040c03100035007000000c00310141c0640d60304c010000f4401e004201c1c0301806c68515600e000001003640c4280160030a500c001000c10300304078030300780c0203030010100b201c0700c81c1203111041000304c2c0300144000c0755030091840100200b0f401154410044c4201c0d03684021505004c001e008503181c90360512148020340e582801c22a400c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 624390575 1250 624389325 624389327
    0x905180708180a060c0810050f090c090310090305030726041419060b18040b01140a0902070605060102070f08100c0915050406090905040f0609110a0e090601290a 71
    0x28032070380d03c0900800d0800c01a0048281d00040080c41200b01c11507415000d616101044450020810810350058022000c43c603882ca030040100703401c03031005040b5054402010901006d44d107510380e00f500800c2d000300030000c00c590001c442c20700700041c03000030441e10828220351415141001c2c0c0040c10050304228984080c880401620004058011071030300034507420300d00300b00a440706081c8903004550500c5a11040d54a20448502450340040307500401e80c00c10401d945500e0140281c503500509810300002c0d003c01620042c0b61940c01130300c02080c0c500e020000079240041942c8065182510010104001400440c1c845c401d00301440c400300b517a5107014030499080c43c880e003040a80c1d01d02c105200c080c0070f0300b0800a01c2203800c103458101005941d80d903448101c900840300604005a408510400034245900200c0707000d110300b1191030820a20004500c00d8242600142a046000300c140303c0400c2c0204140380c014200c00088425604d105102c0030000000e11404882811011812030030b85 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 624391825 1250 624390575 624390583
    0x80604030c151e14010e1503030f030a050901050c04081005090705063c0a050d111303061a2407060f0501170f0705130b040903090518070818 62
    0x15801d041003403141c51120f140307607242c003a420002d0032503041c80e0a0104d00725280c4c1c03003020b40c101d90b0707201400d9440e5541c140c07852801e440b0a100942e814001000365110790500c81c03001d036010325074000c0000341c113103840b50b9a1402c590000d0003c4151000600c01046040b03400580da4000804844011810f62224056107241501c55048540d00040c040b880302c400821070040e200c88985081d100c07012072070400a140d42d070003680c0002c86c0720b051003c2000200e69401000203003500c00c82c01000060b112061810203081d130b0840000004507465000040060000d28010400c4054110010695044150000414000c110b03841e01d0541898064010721b401c0907502594907a540220050180450040250700204401d00440d201d84d44c250444402000300007481c06203000404c0010500641000c003044441c80400c001902465110019a69907464034008e04c480d00b4401c4e2541c14030b0900700400c00c10039004080c1580c41d103918180030003001e0399003c0c85072074111400741143e1503003000410b009810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 624393075 1250 624391825 624391853
    0x1060311040306111201061704170c0105040c0f450c030c080903090d0b1f080109030f0815040914160311030f0303061c021e0118080604030c 62
    0x40d15141050001301048614010300c8002070b0790300c14501c02c5e038881d44d06032000704201d80b90b41c00072000d803000200000c0388a8003900c82040031104c043d081040d03141c102d90a450084504803600c4800c45020081e03041780d1489003014146201030b406601504862401c211001180102c0a400d120010418009500c0e070480d480e10702802030034800880e144030060050055080e9660010788400c0010740020804400c2d01c058080061060825808076290039001e588090240019050f50003548906601100a140010482e14001050051450502801031030490495105202070f4078100b1213961100c0184034a211401c950009900c0341c01c1c1000e220380d075956204c0040d07078480c3d40300089038140500c0501c0102e80c894180c041d40d18004005164076540052601c00c040c3e40203001013405845c01000c1d540e010031140c800100d01080350780000d522810b20700400b01105001e40701d454a603591080c42e044142641d0705640107680c1c9000a10340d07944c240144060b040007540b9814071304020700440803c0c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 624394325 1250 624393075 624393083
    0x901030e07030303020306090105120a0201080603011e140a0506151c1109040f110414060d150e070c030c032d11251e09050a020712020114010603110403 67
    0x610b80700d140140080d401518810700c5501560000155403400302858101022001c02a0880800035401034421090180807a030f859501e03503540304500400d1802402c0664024000824203030352800d0f4108440401a0480c02098244020028a515040f032034111100942a804d1f94845444002a901e2400700d15103080c0c143c1044c40c01a242044140a84103082c400c40c0d040048220304840141250418640141005024030080000b03042180c680b0000c80005444180b800301d0a0240030112103280c4503000e420340320800203103e02c14800546941c00005400d01110080954401501c8034240f858001c0c01c01204490f00c2d02d44215030a106003000301e851120300c0b1944400da1001d1314043d03144002103ca80302d800441a860300450125140400e65091503541c41804c000140850307010300c0005118400f0290400940e4800c503100d06841141c04c6080103031100c00d64035110055503202d48440c801c681c18680b50140545103c000d084c1100d5850034005115240303152000304d54000c0340d1001d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 624395575 1250 624394325 624394333
    0x9010e011107060b03010614040e2817030603031b031e042c011502120409060f0605030702280803040b04030305060603090a1502070b070e010f09050f04020901030e 72
    0x2002066035440030344035943c4921014004546100107141c01c070b5003d4401c40d240418181c940c6007050078164045104103410720142e51942410500700840319801c481040036011820b4050b2050100841000e280c1a0303040b500c40b4036504002000a68900030840c4081241c8501404135a00c0c02081044680c407000c1c400711550300040d241c0041c030854200f4030610800003d480150080e03c40001c00340700f0700b4101d00210078003a90901c0e00b207a0071108008807640c1544104c00c3c0340e0404020400181c40140040503000c20075605025040003082603e41c041c1c0d040c48014400d1005040e004500c0103802c040000c40d50303c203100520381c069043c400300030003d86400c8002040c8818840e40d9031100748128065103082c070141d01c40906001e1740b40320854071078180d6002040f00000042e80e03000c1c045520707580006d0240c2440081d07200c01210440941d4644040313101c98401c50583d5804c140c202c06009800d080c0f03110b441380340c0b1000c1103c10b501507031107a103c0d03503000807080e00e0360303000350b02200345141044220f0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 624396825 1250 624395575 624395591
    0x110d1a0106081308070b10030b010b180603040312050405100903180605070302030f0706060b030901051e09120906040b030c031909110105070f140307030305060901060c0b09010e01 79
    0x108004050a0280c4000542c01c140010900d05101c1c0005240c240e020191904e41880d60b2140e03610140003400300113002c0c040000000200d8110407440d8081c00500079816511008038000c1e0030003c407440e00300c40c0182d80a004000119401c0301100d07140d201c0c0701401082039074503850110b0628103111000c200e11880c0807104824503030300c1090442c00092038002080440d48171441a600c078010b6000003401640308020b905144140c0001030404144034500c0461090740750141104550012183d190340b9a54400c10082592403d411641d841504500b0420160820000668690181400a0382c5401c0001514041070b02c6d484225030040000d41d04242d100e041c10601c1c20203c0e0310503640c5203440d4515070175007820703101c035071040c43c0300298003810420841d070302d11f0010744884e040510241c90008004401c04045000e084806100102c1100076543d10009850301800711764001e130115024865080040c0809500050300703c0c1c1c0241c2041c4002016501c140c112405802804c0c048c520a50074200c40e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 624398075 1250 624396825 624396863
    0xb130c03051002180319033509010510030b0601051e0703020115091a0d03030902040f0c090801060e010504022a07033e03030403020d0f050607020a0b04110d 69
    0xc4d014141c03402c0c440502c1811000100741d9a11507a070501d420b039008009030800081d001e106024910508074501216417042841c3c101c001d42c131500e4155052a030040c2c200581d015088c400c00358000340700e40454501904545461071500b00041000f070602000080d4410044124030810680070050302c2503540d606030301d107002406014581d09510100c4030368000803481c1d06c11400344221600e00c409110505140f800100040344560382d000350145030b030781d10b101805610b440c06800044502e030302001c900d5904d0b00500800d500e10704c2d4060141c0e6490100700744003041d17a001c081c2d41118400c5a0240e2108103020050b0200d2694070940c0c0d421a5448661268a42020406d0011a03011f03881300201d2846c00c01c08400919070b1100070344080321101d989403c600180e000308103501c29018007140e00301a10f99010461003511030000341d411240b03903107487d402c00c0020810b1960101aa1020304400c448990351380340302e80c502401c01020340d107010084400c1034031100b2103092640d410102c82e4003d000a2a2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 624399325 1250 624398075 624398077
    0x91501030f0519030f032003101703070206091e091006120b01020c0d17121b040b03070c1a130311070602030f031807150807020a0b130c03051002 64
    0x904507120300440320740768107140300030840086058142d2100842409001740450060001071070500550041d00001d031410600240610f2140291030042c49806061403120403c0d0050480c1d8001164010450200142c642c5025168100800c6d2144804441420700300d103200e0035941c0c0d03616080665038040106140e03070002000308441c0c07180c9540b1609002a499407003550402c5402d203025a10a078500703840f5041c0078410f0080756000d400000c4440102500c0c12803560b000c0102c840107210001c05011441081c024003801800f80008820314192078030200000c1070000801c007505100b144d0140109001005100c031914100360b07400314510b46400c075401c2c0c040e42101c800c01d40c001585010700e40c0d500d00b0000b80303010544e403c5030025420320188240701022a40000d01c07411924100340c46c003081c401005c11400c4083e0011100e03041c06e000c100c0c08000c0110174001c262030115803280d441c01c00494a03055019420120942d1122a2030a103810a4041d02c942c591009240c0e120340d00121900b817880307074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 624400575 1250 624399325 624399353
    0xd0903120c030b060a0f0c080a0c21020d0507050c030d0504140f091605071209170c0108060f030115091a2b032601090c031a0909150103 60
    0x1000700480c110501c0e0407412a40e00e5591030f504290104021420140602c02600c4416050305e001d80401c40707266076030300103600452050004a608140c15504100085540760100c4908200300310704a10116002551100b051208006100b0300156600500505016046000f0005800c480c9900d00e0000004d002c1d40c8140301d08040380f90900c1181e803403132034481c07034200c001c2c00000c00e44a095105c424030003008040540741c540c103002003046000001420186400804204c43e11100c090a01d0001c2c040022040c03000f07408801d801003821071500380c3e04081c0711508100c0070b0350390084401032580828010038808005080740c80c041100007920038070310f030855658a02e14429400354045100c1c00d00c20000030081e0401b2034a0307009040101c070500d10108807007403503021349040c1e4807402501491200980200c45444c10010b01a001409844024010325282080c0b03450108405480c040d1035001d03085641801c0383c0324160a5010440740c0c0c0003040310200b01d41c00124081c2c11540c0d03034903291559810007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 624401825 1250 624400575 624400607
    0xa1217070f090504021903020904180803060306090a03090608070521100609050d0807050c0604030f020f10080a09061b020309030114130b061f0305071e0c0b09030d0903 74
    0x1c002d002c070700303401c1500903141140113016806500c1c001c0c2035400c2c2d020f50000d0310125000365448500d1609031000c18415071046005400550f601d08014060506003100200504000d41c850040100000c1c1d2240144040350440e00d08010300e5107403014100c901d88925003410741c7d42c1092600108074222000701c2c0c00c2c016075001c0501c0c41110382e50007050381d15903020301c2015409680800c040c404186000c00030003801b4420401c0e41c150b1100b1800041240d006500280c50101005582c9801c60a082144d0b108100048918941000900300020300a5000a00500c00551130300965010055903420942144078860341008948004010084d501d8001d076101c98030940c200000c40f0701140b02580581d0046031107000ca1600c1ca0301a440d0410b4184000c0d1191381c0000903000d2803100c40c03a030310220524818160350003007070034240142e0050044107400304a28482d0011a04150260703000158071619580c85001005c2c0750f5108002d00c0c0c1180210b56600038110b0401c07405074201540300348844181010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 624403075 1250 624401825 624401837
    0xc0f0b091608030409020717070302100b03010212070e1201111c0204050603130f081b0d0206010e0a0c1b03080708090106030f030804020d021302040f0e06030a1217070f 74
    0x2090031144452070162240e010700b80c10400050012500c03940041030400d0140c00305414800e00310440c2c0340164400c2c40244e00580003020b1b20002807405000d0f40741950381c214001d504001d505a04c1c06199a0040c224005001500c2c0d0040b1440e11014207100d604202a0020400b0350001c105051180e4032821907110309802aa000300c003031858510903101036a80242c943e50450380c44081c1340d48100e4000300141c5400400c5840c910004d00788200034443c95000034109420b200461107010724003865141c520301550071907c01440401c1c400000b00b80d02c40c8510b40c0c04100c0181d480d0081d101070b001500032117004d4a078403e104040c540c000910394001c9820f556640303115034486241c0f50881d485404000c200540d415030890201e131085c0280e0360864001000c070351402e0340560005407040c094030a40f915054010600704800c2840800b40d2005103003400744184145801c40c0043e48514003504014600400c9680344c02c0750b584211043c121880507914010702074101480090304052036940d844002a031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 624404325 1250 624403075 624403093
    0x203011508040c030b04170c030a030f18020405130b0a0504020306010f06080705030a02040b0a0c020306010518180703080309250b070b070e03030406030e0c060702130c0c0f0b09 78
    0x121a05110b8481e81d08554407194403425a6114041460098000e0310a1105086955095656500101010480b010042d9030390b4415520117001e0328203800034102e08501c0c09003003240c0404e007011112000c1c0d50440340000e0603038800e08a406074203003500c4003a000107a203104011402595510003030056000328200c0c0c440341c1e6265100621484103018000c0080c0ba00740c0415171407130180001d540c000c0072518000d42800e484142d10038454012104c00d0b000942c25603040c206504083c041702d070142c402602c4045150240014290f205000a008040c0f21300c4001d908070010714040c041e500c051540700e0902e070b9907030500e000256564201031848003414041400038000200401103014201ca00c84403019040c0700c1c4980740c890308844000c090005004910081c407403140e6080c0b0040014060b191000113880c00a501707040e180034440c002c0213025080401005016035203102403246400d401c00000711b001d0301a4ac00884440054070001802c81191001c03100030011524003941c480c8030320700d0442e40c442c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 624405575 1250 624404325 624404327
    0x8030d050f0705040b03060a03140d08161d0a03060908040e0c0423030c101808070f0e09101503033b030a020a0305070611010204082e0501080102030115 67
    0x32800c2e2070190128070104420442681e0000142d0b5004000821001c85940d83e9120744581c0c1114004001050b001003480500a58119190b15042800001c00078821404a4006005c016400440c840a040002c401d18400d0752813010f104007555101c5802d0000020394a06600690018040d00045688180c005640c00026070280c40460344840e801e0300c42003128150301c100c6000c8a9400e5500350180c80c016141c50703119a2008441180355944603e23801881c5144489280d2482e0042d030a1600700348000c0140e00150031a00c010741e81810381d0b440036621f0b402d075000e2900484205421483d0700b4011102da00d50300030f542d450200d81c042e440320002403035500c030420340b400b0041011610140c51101d0740d034180d400004609580c508090119402e01c1007903000600a064243d000b1210342e4000c0c8002d1020700d43c410003403c01038001200a609003400c00d40000d850344545440c09180710041126460074004100094044028182c010411543c552444a010358024060030003c580c0600c004101c3e6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 624406825 1250 624405575 624405601
    0x15030b100201021c020711030f030a02070504090809011808060c090a080606130e1e03091207030b16030b10080702070501110604120512090601030209240d0303020d0608030d05 77
    0x40c180d04802400c401820319007030130081d0400d100c26035804680c00942c0751030341c60800c030a04007000850001c607103507040140004c0c9000120380243c5d0181c1e0404148000190b030b00c1007580c00455090800d91041034041c1d200310030380402544890b1443c8120030621586c0d0700303824020024504142c407901c2403180c8550f4044c3ea22881500c14940007051101c000c030213004290701005907a040704080d1520000c01e0144e6141080c0d140340c0c0d202242d000060103070541e00d00710007044041e50580028080d1503182d5158020f0301140140b1828420301c01410100c0c6203886940700020b0540018200000a044514014141c10b01100c06001610828002040c958005c4451050306104000200180e640701d51303070041d151040c07035840d000b40441409440078680d100da809a115a00400c01410158558010020075102c058441d64000301d601500352820280680508994401a6101c00c1c101034640340c102c000303200d11600841c60034905a40410360031400f000034541c001100c0c0301031040d42c541300c00307031825 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 624408075 1250 624406825 624406837
    0x5031b16030918020f0a14090a14030c09010308070308040c050d052d210f07051c080c0904051b030117060a060e012c010303030507320c0715030b10020102 68
    0x9852060000210031032150003940c2001104c00e81c0c580c04c2c110183d0100e203c00c89e16401686c0e05005200c48a00103042c1001007144283c0b0440d840c035401d5256885802c201e2088e00400340402503c030b8000f4080c40900311040340184400741c07042800517440c0c1084c0e5111800c07030000d02c9511903803003c0d106540c4d801d485503100d45040280a090b0031040d2034034405600501044910000c40103005601603104440c01901d03030580200080d040e05640b82e08140340c0039120803551030500844a0a002c070382c0e031000043c1c940341e81095a000405886152001800eaa401c01d080c08119030000004619030f07000700d0a03401508400012581240c1302e5112013002c4e90b141c3c1c02842c140e880c24000421010103180c0002039201072040c800c00c0c1108800c0b20358400242e0076002a00402e0301c0b903080c0200030340c0c0030b0740001203941800d072211640d01280c080415040c284440000c0c0f514404680c2130141d140c06e000c1036000342003844404811070130100d40a0090148050920301c109421251029040d006008807a1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 624409325 1250 624408075 624408097
    0x1b171b060603070504091406010b040305210319020702130e011109060d020a09030c06030b0f010e03070513020c16080d0207290903030a02070f0f0605031b1603091802 73
    0x103c2981002c085c00300900d01401d05440100c044110030183c51414022217003c1d2001140b015076075401c41c28020700d80214800601e1307000709046100e1041c8000001941c0d0003100c490b440d03844030348441117500007134016200045d5110310800c0c546501d410703855000403080415140240b00481c040c0304280724900501030225085481003059540031310960b4020245c1315500d05215101e26265102c000e00307081c4036000180800d9036981c01030164a00b91108105180007440c1100d00101010f000c2a281c24452040ba40640806a09005864003540545006502c490111400e035060b2555018001d0002e00c9000c205000c2e41d5a08000030b4800314100702a40d0030619031380c07a415000c8001880c1d1940007100c201f1000002c0c04181800c1d64103000420540d080d60f8010083c840c10b01c090145200801c0c2c3c0010101d04000c1d00811140d45c00c0003d9a60080c041192a644503420380b5803070711b10f0710401d00c0340042d03003c000700801d08150b0401e0013001503da204000007007021000c501c0408921895000c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 624410575 1250 624409325 624409333
    0x503060703090203150a0e0d02060f160c12050405040e03090406120c060c031403010605030901050c1e0906040305010203040b31020d0303060e0924060109061b171b060603 75
    0x603c907860805d07001d500308450300e40000301c2080804102c1c4c10442c182d000100180c001c50140880081803001c2181c0000354818002110074004c03402400c8540c89043c0240f44440c0603010200e82c601480039500104006007040c8000032100506c60f0316070344104080c500c21443c00002103401c00481d070400815030341c004e01034641e00742080015102da04042c00d0490030070604d15034543c10600814040c500801d201d80b1140d0b107a0602c00c0300707242900d078001d0030f01072581800d120101c0c402050940004030f4945150358680d0b103500075008500d080c8034981000c0c0042d80000144070801c00c0f182c404521030a0045c112350300c500640350701011000681d09003c01c1100343e0001d2140986411400007149034840e003000501c17650388805421080400301d401e00d2454011686540b110030a05040562900b00481c04880c40d190080c0040e066004a01a10b4208011100d03000020301d02040320100b52608010302c41500165041c110307d06a0044003281050002c0c109503646001380010039a0150200801038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 624411825 1250 624410575 624410593
    0x80a0c090501030218130f03080103112d190e040b10031115090a23030304150f051605030406091e090507020c04090b01080d050a2c190503060703090203 67
    0x100c2c00c4017000b5000c0c036200804280300d40c00256034101110380d014485e8487d8441985981403000300036821010040c018100f02400a244048504030f11015088403c0e11010100580c0041070300c0328090180400751200da61070200d0350041c0801c203684542e1007042107185c5541c0c0d041010b10312601e148001000f00c50001045816032404012a000760f10071441d000782041603c03400914500699840f94080304011502080b02401c030b4140f87c14603400560003503103020f1030403040411500c070868144007081340d0a03404500e10303446002101c00a4566030950601d5800c6ca00f01036890390700034421180424074002c4001b070880c3d41001150030410b040000c4c2001c4d589081380e030801910303008081c42c00710f010303c00d68402d83d5a034a20500c1c000764000d0301c1c218802d604100c14249080c00c1540c118050080c2440908011640700500c40280031055128100d80d074440304584040b054204e1b021584050241c0700140881d03000c180000848400f00c1c210b541c50745494000b80c04680307010401035056082880e007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 624413075 1250 624411825 624411859
    0x140c0a170402010309020918010b010c020a2112031406041107112107090e03030603190215040603020307120b060d0e1e1c0206062d0a080a0c0905010302 67
    0x2000c0c1e4024010706010810380c90035800182565011904d008020a01a010303502d601c400b407052a0241c0c0302820000850325058000407003000080c0b051140c0d801180035400032200c1c010740c03001c85c40f50340f0a030800e00c4110b2228003d400b6205928005640360300010000300646024002c0c1210340f103941d64064548034003615211020300300e4416480d00710690030304111190f10071520414000100c075010700811402c060720281950004070070480282e0060052000c9a40c002c14450302e425820841007804005510100f890703502c2c1901b00000c00c5001140000d025070305a00150f21561181d230b00e0380080f50303425212004854101d0b10031a0044d905110741707407034094950301289840c40864215000ea264003032603e41003180703005091030141c11180c0e03101e081d426680c26030002860140003070300c241d160160200303a6003092062403106c84412500504034482903124600181803010302414945521981a10303900c0c561581c040b201c0794046140058102d042d44187c90603603500901d400c1119030340c240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 624414325 1250 624413075 624413117
    0x609150106360b0a030518120a110303040b0f1b040909110301050702030a09090608032a01140108211e1201031a09010902030a150603080409140c0a 65
    0xba440c0c81e00c200c215400300d18034002036110080003c20083d56583e40302e202d00405841c070103400704580c07003030101415075030030030104085000c0350740900e0700d5032a00c0001004465418410042c0001404000148400e01c00040111845107030540d03400c0310f841d1103414000310b4503881491080c1e00d0361414071080c02100507540100c17000c58010703201f00f105034848400003421680250b603030b0f4015a10000d1341c0c013104da8000003c40000c00e1548030402030741e4a01401c1540782d120b80c0081140300e00100d000c10400480e010040e911081c82c0100800c641088c0b10407201c45410280900c061610031040d9020010792400403032440d00007802101c5081140c0d42c0400d4042c00860704003829011000d1040b141071000005416000394003400400384581c844041c0440c030340f0700c05005810140d044c0041ca02c090303200000c2c254000c035401030501d6407a95940203804c000b0300c1284c000030544400000d0004d040c00803a000584e0069120308036080075200d0894083c034600c540d026000c042424504900c00905140c1c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 624415575 1250 624414325 624414377
    0xe09070c140309030601090b1c0f02010e121b040506030a200121020301031b03050d0e0a0b0c0c04060906050a06030203090718020a1211040b0f04090e0609150106 71
    0x1c8110b0381064240c1000a0418070309030045000c41b1b554909400321850061091051014000f22036401c150194544007041509450302906000c10641c1c210311981b20030600704001001d05042c1c0c0e158100140c100c802d44218203001510450a080c042105403a021490300030080e0b100d03803210403100da41075441c02c031003044400c80b906006039054000c0b0062010500c141c61444150401641c0e0340c1149000000841c80d503044031810108001d007407000a0000616480a02490611040408809001500180c901d8120541803c030104210301905130001e662480304c0d004880500510f91182110340c1124128443d040e444065890300b040729034002d07801940c100d14548290350040e91548003110b00110f00350a0180387e00c0e80050400c00582d84000d6141d42c001000c1000d0010610281c0b024030140202e010f120106000042c4000180b482c120484000303081c14035042c0602c0e2840803c59455000c11180c010040c0202c1c070055581c1d0b0780c841d2640d41690300a440c4c0c4030088000900d00e20402c100030f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 624416825 1250 624415575 624415613
    0xa050607152406090b03040305090904020f060d091103150f040f0519030314430305090d050309060705071a0c180a03081801050d15060e09070c 63
    0x240300c89950b1580004150500c828600800c8441c1840c0500081800207158000c00c120340040c0240300010754480125070003000212035101040d2a10700001c0c021000b800485544040c0009603145240c00a4010210080c06002500c607500b21020925480c0c4a4200300444800040d0740050292054604a01d40280c02144107209218059461178900710a00d0b480d507440d00315041e20303001015031501811390b0703800b40340100d07094505002c078072403203800581000c04940043caa0140b400304015a142d05150056060882540082841d4045c0013043c058441c3c2000340641d04084c5c0ba414000e90490340100315000c028022607565500807140c0d034200740d1007240c07007100d2070729800d65000d48204168002c8024205072603941480725481d42400a1443da000d000c1c0c0d41c040000c0000c50309144c00c4c2e0710030084c0d0040300c0e407400c034051004840d03900c12054211280d83c9825200b00d694030703501e100c90b802c0e14078680b10000503401d0300702000000c1004550b904002003803140d0040c0010f1010f00e41c0c070000d1480c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 624418075 1250 624416825 624416831
    0x605130306090f060507050a08070516081206030111160809041d010e010506010e0f091018020405030106060302121902160807020405010b190e0604031406060a050a05060715 76
    0x101e0380c610007503070907010040e990710300c440f00c6200a1102e184902e5405c4034082c1001454540c400202509814004203003005001012900d0480f020742c0004a0032081c1c1d11600d03e81d603a100c2c51004102281007074a209002c2d48ca064403d0f0940d5141408031401500b00c10700060142d0016518002158415400d25412039103440214182060700c15004c0070100c1c40c0c60012600c0c081c44401c182c2101c2004119038100310b180c0700c100000b6280c2d0381c4030440601741599082d5030b960b15459411050115581701c01ca60801c1050032210499aa0340940250341c0b0480084c49030a503a03034021010390142c2c0b0702801c141c440c13000100300d4090380384010801806c0044009400c5c00c81646400c0c020840c0e166003503c12100004404003140707810300c04d590140010301586810000c01501101f82c0c83c50760002d100502c601c10701031150f5980c2c1c1d44203440045a00c2440ca03850020204102c80e218101a1840d038040c010a14021800f85009c00384ca400f5980050081b03410305d20076488071003400f81e440130040401e5517 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 624419325 1250 624418075 624418079
    0xd110c0d0c0e0712020c060f100609090b180405030a030510050a09200d0b0f0a080c0105160203060c04061d03101e0203010b0403051b0604050f0102030d0e0105010501110c0307060513 80
    0x911303030015000000802024200b2860400f60600c802100242508922103270f000080c0071158120301000252601d07201c000a02c01c0320350011a101b402c03c0381405c4c540c98040d400704020030900000400c460b121701c1e5000d0006448204460507001e2090140b1980003401c03020521450289511150441c03802c000031798490614100345058507440a104800c00d03c3e01d601d0b6404140c104450204140402a50400c900918001e911a2240c0100b02620704020b000548003000c204801c05804209400406580341820a242600100d43c0700348100408107a2010a1040c1c03003000b640310f500c135064043e02801800070304070000c500030a0350324421000d041440320400c11036285ca2000d075010701203080051b0380ea14118100344e4a016058924000c503214040545982138551005403411910181d858403441414000140c0c10b500442d401e41c102145480d45038802c40a05400050481d20282c80d15902810245426503c131003011840c107805030301c25181009960b00c600005e25500714003400c0134072915 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 624420575 1250 624419325 624419357
    0xc0f0206070b09011a0613050d17030a0207150504050604020111010612050109170301031e020a0503030307020d0e0a0b1e0f0a03090309090207051e030c0d110c0d0c0e07 74
    0x1002603800003d1030b9941d0003031070030800c84201201c464803001c40c2d1136410800210f8020034080640d01915010709a0468684100405083c1d8a00c181240390141d50300c03460288a43c1d0025004000d090310003e803910411f1186000f94030407103010f580c000014001c640d0707880d001580c002003100c04040c500d640e56071000030084102c428206616110380e00200d0004183d041805021801003004024600c04100400000b4501441104042d50000540303000311120300000c4c0b1280d0043d40300c2500740c04000f04014030154046007030f1141c42d1907501c0e60070f90304400ba000c6c401c0d020894010203411541c00c004c0614a2000d25041c030700340c080541d071000d29000d11111150201d400440c2c0d1781c1c003ca41c44071805402c041e00004120b001c1c10101d0421420801c040c1c84881e52800d410b203042c058000c0702ca00007001040f00f8411210340c551044202c2d4144d40030307050000d2035410301c0e0354104100e0155801c90703001460440c020502d5070350066511041d03281071001a02c40300002415090030700c40c0000c0030740c0c689 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 624421825 1250 624420575 624420593
    0xc0308090a0f0e07082e031407080618011107111026180f0303010806090c06091c20130b03060f15040f02180a0308160c0815041a01060c0f020607 64
    0x101086422100b40746e403540c5003c40c94200300d40c650281d990000d00e405e002c000340c00125103500c584010480300307500d046100f020b40101281002480031620020b014014081c0d180280031940c0f00546501e006941141c00403901030343d862022040c402c010300c3d4011490140d444080c2d400216166800071428441107080e840d0050802c1844036035000800100712203802480019405600000a040031209000000c1c015100c1c40382154801c0154448440f107044001050120f03069101c4282d40f8030012400d540781a00001d1034030540b0800400301c480d0900049030040d074916520150092070300c0c0e00d40016609003c14010a548034820000300c0702c18655031036015601d2103110f029801a46e1b402d00c03403800c1c00f11541520501c1c0c010902ca480410000309010308403440ba0480090b020110200c0c1c0c0340101c4414800d9119a144e4400c840c20400352410001103503006903c6403412032851500c41052407000c140c01d1040c080031815840024002c10069a2000c02151008100c03900d4102c00b030f03450a40e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 624423075 1250 624421825 624421891
    0x9060e010903110d091d041511040807061d09040515041104060e1312020f03180f010801080601091d1006060f1107120606030c0308090a0f0e0708 64
    0x346500040f001c4080c0306010945424119140030303408507081105095070303106001c48070288000010002010300c1f400c06041404883c42c51401d000045641c07809564680050086448030f0048250014052b030051440c400f000d24003680e01d9102c461480100720360b051006009075480d004d1610803500c4a03403498519803080340b00d9078641c82440d050106020480e16150400f28a40d02c1c91424070101107002e01e14140f1450f846141001b0040c00391300100e080c813a41c4500110300e0300c00801c05400c0051500b03200401a1416544104000c0605004540c0340384284035040d06c0d40c00090045c440150300d0f8100b801000f52180700c1d100c410001000040c0707400141c08404088a544000c28482e165205281c8890405149044001d40000d2800d1079180c030380340c1c80340c4c4c00c1e0a88001c281d40100800340d04108010b40d003000c1048610303562401c01007155072201071428410515000c02186003c03608010409440c6218104034243c1d8030300380f040d548004040d02c2082c03160240610741c0c40101500054400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 624424325 1250 624423075 624423077
    0x30608031315030b27070e0627030a051b0d0c031203060b04122001050a0305090a0209091c0302120106050a090b13080c0609180c04030b0109050114180a09060e010903 73
    0x41c1c1c010320154074031711009042d0308104050030b18a12015914001510500361400d603060305400c4e9040503280356061030b401c0d40c680501032a00101c3c103201e000318136101c43c119a0101d40d400c4110140030813008225840004050401c400001d0000c00c1e00c0c0d003900c2e0300140301e900b0001501c40e01c41401341656007050b400b4030481c08540f51401d040000c60403212190181614081e40700290680c000780660180c0321720f80003010380c2c5500066013101d007001540d410580240260f00c850070110340d40340c0c0781c08a112480070641500224803207141e03c2807081f60311680400000114690070560b0840e02c5034000c0b1111000c01800c01c00c0400c8030f1040c1c2e00104641c003901440791046514115046090564080c10240320700414050320701c0070341b120900150418022600e4074440c2d80c90408103000d0703028a0300044c1c4159041000843d50305070540c441c905a44514032200c107052000b4ac00c21501c90040c5410303841c80b440008c040703040507040d82c024110580c440e0101090000714100c40a0031512804002d074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 624425575 1250 624424325 624424369
    0x504060312110c0922060906020301030507080c0303040b09060d0e07090b0a0302031002210708101e1401110303040f020a080706021207060b0306100501030608031315030b 75
    0x3a8442d00200e00034035164042015292100540f800200100b000030b08500d00c40700c510b2950794940c016180c140100582c4408200203880f00b50400304020340003404203c816200d41e000125030040300082c1407a510100030700170340c030781410100200700d5900010b18103500705005000c00e00952400c1e00510303040003003000c0144104c1b031610403100107592403e0003450042c16440c40a10158a000c41c40c000c0028a00c00091b82c4e0f10300d21a81c0808200d4250034050304040c0000c20710402da584008042d000f60b001c1030745002950740703a0520506100e000706641000750a10b807401c00003090f600f01e03001240c880506180300e100319100703122030540c0c0c402c81d4102c0e404418200203108528291503004058a00c040040004600b000c034042e58650401003c00700103000400c01100b004500d4002c01d01c0070304040c00380c0d01c4e40e00b010922410400124058103001c01e04041000c1180e400020035172b0780380d4070295551701010380782038220003140300b24415003802c01da10b40c40034840300c1d2680d4038080c2c55450165034007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 624426825 1250 624425575 624425603
    0xa180b0c100b10090506250c05010206010b0a021b0303133b0a020708090d060c1116030f0215040b0304050c0d1203052703070605060405060a1e05040603 67
    0x11500b20751600042c03520a001c0c20f206510340a074400e24000035240c003580d4103590b80307881039520348401040d07403807900f1100030401c107810412200c081240110381003a000c83e2041c1c0d0b06d500b1902c01d1801401101e00051f84840c0365201080c110603001c250620700981640c0c900700c220200380010310313101d030003001d00d804154081d40108100038a07420700b03000115003030100c0c3d48502002d024080001518401840742c001c20107209100f00ca004640030980000c01001c54404240380010240c02d140044030003044004407a2100104045100104a4015800d041a290a641e80d80c414010042c1c0c060b41c100301e00410320100c0b6080e003001840503016081c5200d403a071070985000c510740a0340b861110f0080564188610000742e00355845400903800381004619503407005a06810f007001c440d840e60440009003038403091048044010a456800b450080c00940e50b0304d4180002c0d590103a80e0941c000000490801110303e64210f07d40c030601c06108040102a55a00003030242c1d0400e40058030f50500e42d03650 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 624428075 1250 624426825 624426853
    0x15090402100c05301e0a03060906120201030506010806030309010c11330a02060105060c1005100f080c0303070618120207170c0d1704050301020d020c060108120a180b0c 74
    0x85800d10602d000351a515088201c1c010104041400345c200c8600c003c046402410349000350024000f82100503002c01c002650f510441d14440c2542e0405e9020918200c00f00704103512800c0268419040a402145000107020045070948806407094540441030714840c24155681c40300c203082c0c0f081c00250b030603180858200300d0011144a0400350340c50081089041000d90300868654115041110300548920051100c94149403000400e541d07068074020030860340c0e003410441041175030307141000c848031141ca541d24150b441000024035541b642c01440b95000160190300000441499038040c0088400550380b5002c03102c00c14407001c0d026800c251810710802038600402c0c07010b101c0c0303d8000c0c40d05806010102c1d8200b140c0400280041c0c605100041401500c1802c803402000003030003c541d16215480304000a400070304a51059002c0c4100010700a000050000100c041d91014140f4103c0b8010041d16030500b8049010102c8014020004c0e266035142e000d40083d09001024010300451445 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 624429325 1250 624428075 624428143
    0x1401050708070806150d0504060c0906091d0705040e04050319032702030319020a110d1703090106030206041401020105010911040512121c0515090402100c05 69
    0x110303020409908108628260700001e020340000c41901c070381a1203400c0680e00f650300e20500300c15601d00c505160901040140990003d04800002d41ea202c1541d0384406044444c8801c40c4110700c00b1940c001400210001285e102d65040a49800c045250642c0c40308281c50503001168141c5003a000452281c001c1490442c49240d201800d240410010107072884003c07405503149800c0d0840f0540841d00e00854a082088400303e503600c0b901d8204c0c3c90b4400c0e1009549112107081100c01440c05092a001c03070401108d0b849510764083d0380d5800d1040310300090461a000107015000540d25401c00001588031000108042c003829030006154080d0b0200181c00d58806070b000f2042c81707160041c610300035940203042d1010785004440240b04000c400910925040c108102800c180c7c80c0010b07504101d0440000012303400880090500103076403000d105180f00d10b030007408641c00c40d000e00009001032030149000403000314182481c080904076515124540400340075003150280c040d460740c20759004814 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 624430575 1250 624429325 624429331
    0x7080c011b12050c130e0a14010807030201140307081311061323011d030304050315010503120c0604030e01020f01050a05090c0619034205010206040f1101090f03140105 74
    0x30b03843d54940b8186402c10070309841c5c14800c0250444100010503648040785d00000d8110b0302c001080c0c942942c6070443c03141c4410300c900c003ca0200d91081100030300241c01d5401c2c0ca104d0016600e4140ea00d580d920380c2800d84001e003142c1110003088244000c4182e5480314003a05103803d0307040101d44240d060031465049105c144900c8400c08040800118550b039001c5408180f411b03120300c1103522b004201c00801e103103000e5600141e501d4003d284031183c400e60540d0a950403985e08408039620324404041c0390900744182e9010009035000500010080303805003080100312a03061044541d40c48414464031700b1070300d090300d40206440d22030f0140445900700b00100c5501e07072000c6400034a0042d580a1314855601049816824592601040d001072407801e031300204c807540c1d54100000d404010040a010319003607141700e42c0c840d03042c502002c40c29510020301d441c4103682c018601c5081900e59141c0045150811001604005040b000824007060303800b030150007180300300600030000f901d4148107402d541c002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 624431825 1250 624430575 624430591
    0x1c0512031608060f1e13060308030405120a02150c0c0d09170304080309120c060c010b13050c07060e010615020106030c0510050414060910020a0204110f07080c011b1205 74
    0x684840e92680d580d045ca01440001e9040382c0a4011303800000300b07808050f685600d0950314a002800014081054000c41c4500c0c4075000365002118025045070190040641003401a0f000801c0d0205004440280c10303008003100c0c124a0404140754a9a85420100707415900082e0f107001c0c0c1005490000d0038a5814041c0e00400346041c6400c215100307682c0d0003400348540c4a0060115aa01c121a003400501c8582e980074220310f580780c807003210317142c040c22510704903d0040b4882d40c3d038501d40b000d807413040e140a20404103140c2e2a0070090344604003c0c04103034622580c0c0b0355980307a00040341c4008210b130601c2d180b0300350000b140b154034600701140d10f810705610250041e09100050981d4036402001c80c5c1c10742e403002c82020300000c004400b207982801840c44035500b0a40b1007424404594000401c0115644200e8060100319014212811207000b01115065144c5051007540001203041e405031682d0032240d0000140301c42d069001c2d0b0803800c4001a094080b60740080352590109050044076449100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 624433075 1250 624431825 624431839
    0xe0a0818031006150e06070506090a030e030102040303080c0c1e0c03060c09091906210209100e0601030903021c08040c060c020105090402031f03050c010306060c021c051203160806 79
    0x2400e004c81001a088a9542c0104119410881d503255541c0e0180c40c6019045070480b8400e161a840e0180d07602440c0e441580030600510490300d183c86d050086a0541c1e074141d03640c601ca41c507000c02d6546160880007418420f030207003412009003282070701c030383c0e40a507540070f0000c10300c000b614414903007050005001181800c00803c50700410707498001044d504404024424181080090b0004004111603044464250122f040d02401c603400d00219440365402202c259160313485400240000c9046849a41e5030419a83c0c0090700d00d40c041d034000c03903015000c1e0069490950194901c410000d807511618404079010ba81880180040c1d4815030000e800c4a051800250070f81d600042d2590084e0303e1795900c125000030004080001c507841030030300380602041c020162a100c0c40c009842d102041c0b00d06001903c0c0c1074001460500c00d0000052158028058900b5851511042014000b031a20107803442d10030b14480140c810003001c0214801c1801c501c05c1d040b544d201c214020721304c41020341000e1180034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 624434325 1250 624433075 624433079
    0x30929060f030c0a03120507080a02160816061412130b01120f0b072109150b0a090f061e050108061f03051b0409020706140c0304060e0a0818031006 65
    0x840511350340c01d40c1d8101030010790b41101c81c0011182842190340c001c0410b40301280b90404c0b0b94001640582c04d0108c08220044e46072100711282d55842c20003a15000d10a009004204090150414400d490040c0c262140782c104890407080001f407003034030200819502c119801050140192006024102215070412280081d03203540b20000000383c406081e540090780031401c0d850041d0380303115400c94801881300814102c1d10340c500040c203402406071041c103441c44078001003901d148905050804020030b50400d803414106802c0040061884e4005103c0da580300105c0c808106280039a0017940340700c5c018005500340000100820300141a803800f800c19450408440003c0752000c51003c0010700d0000349641d120114840d00d03501500804070620b0300090042800000b41d0000c0c03c0c1c43e80110020301121000701c041c2030b200c0508507183d040c1c52005201203000203c0682083e142c1e09905d10841c0d014202e55291810130758030810b85800b030744408086400c03007403c0c14440c0c3d03150001c2c1d0000800c9014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 624435575 1250 624434325 624434329
    0xc0203070809043902061306200310170303010e070c0c05062a06160807020313090507030b040b1c05071e1806050f01030929060f030c 59
    0x2000e00c0038000d005200104031041c1c2c503141caa10004c0c0b51400740b0303581480c01002c00484500b8100e141e03c007440c84149192003030092800029414020f5091120784c1c01908129201d0314001e00c00b92840060088030a0195005d0000200140d400f074500e140c03100c40301c2480d0171103412640042c80a9045260070034401004001c080507542e030303403006560402c1a0481020328080385130070f0302504aa0350051012404141010741070210b00b68120008804e010310011281d0306565451088a0034a24981c10b40ba04a4901d8400d540c80c3c0e422002a0040768180b8481030003220a5a045411100c64645d4403030810000f80d038140240c4810044c103442c104055003000c00420441812036200801ca11207141080081200400000008000009500c80759410800041900d40018402c400c000e0008101480100d40030703200d580100c3c3c800401a81c2501814001540a4055040142c0b500074440040c01c0520203401c400d808247e03101c0d00540701518000041140c604034130000345020f0340c410300c8415079903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 624436825 1250 624435575 624435577
    0x6141f090612021c1401051806041119090903050a1202161127070807090e0f07050c0d0206040b1005030709020304021512160807050a080601091703030a0f0c0203 71
    0x7958050301c0c0b40c190113103000312070004003d00040052200f5080c001d002119501940700500802500144100680a03210343c5a07880c00c00b514040c1c0020300c1218126154075124401030780107141002108106035640652200726641e030a004c0d40420b0000403481d13140303a4050055684c448142d1411401c00041c10391401d10341251a00061518528009002642d51400d03484541c0605100610040c00c1e07052002010140d020b44151000c5040e00000c01c4000e4080c0c44180c3c19900016080a95603440d210304c08089c040c060422400d2140c10406403203801c5c2c0510140840880d0f94000700101c2c1083d141035801d503d40244a15514084098180700c1d640d00860300c00c0840b904a180546c4946860000582c07603141c1d40040b032540d48001810302043d940304800380d4422030361100203007114058010b00750340c102011aa104000303001046001d400c6030003007081c01d4100c0810301d400c203219501c410400406110841c00200c2d1a4400b00401075507004070f000d02d01035103255440c10b000301c040c100c0000e90741e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 624438075 1250 624436825 624436859
    0x312130f0e0412050c10020705160503060a0203040309031e1401020903030f130b04080a110603060a030f030c0204022a030403030c02010818060a0e0c010e0108011206141f0906 77
    0xb01404214900790f05600c40e0056406241550060714120a0843c40d8440254803e0504035914041c05c00480010320040300c4e04d200b150409000b4100c941d035400301a400950008008a061082588000c800300d01d44551b803030302680c8424a5120710f0082410001801d8000520803030050f80108007810040e10007000b80c0d942c2d59000311007944c88030140d400c2c0c250618415007080c0060000401c1c00030301400006003140d40381e8010303a400c40c8a04004828800c50744000c0341d0707041d0410040342040000902400b8403240032130091604085481c42680014181e03808030701e1b40f0b0001d070030803a030700020f007aa0340c80d0045a01108a00541c0b901e442d41e90701902c013032840d50010f4107001e4a82d0006030000c6907001390200100b41842907840074601010f00000610181a1040c0709210b4000101d0055014075440070780761b0300585600c0390981ca405100103d410135000c04032aa01e84500307501e030f01050300a035524040c80d17150b03061100808010000c0c0010b0703d00742e0b10040c6d9480c01d0000411047c0740e10b00207259 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 624439325 1250 624438075 624438083
    0x904080409020f041e18020901170402030a05060703050901110c070905071103070c0f1d010b030a09020d1109060105030f061003180b040b09010c021b040b0312130f0e04 74
    0x1850f955203012210450043d54409030068035070416080564080181c44825207002e03450b01056405880c050314224040c140702540842d1050b95406c0c0482842c100b8158410701c010221418140c0c10380d2010704020040d5007000100c3d485405001c220b40080c0a403442d9030300d501d0549070401d02c08100035075842c402c910900410980d6440444ca030769208a040144c070304144411250707030b0340551501d422174203914170440600048644d00485c100d844404011071100c2180c07800400e0382d0a10f01806810b610180c0f00000199488a54100680b0b0350140c4c195224081c2904d0000900094180305c4180c000400c0103041283c01c1041054106401c0c40c001c2d0042c0013a50304d0039002005130815001800d0382c03003003490402c0d030300d140407820844000308282c0319078410039403202e4a481c4c105c101800c0c0c540d03900e544800b68110151624594901c02003030201d0700c13802000800c0440e08040441c1c246900490082900c250000d41c0044205605041e40e00905d071681c40121100c0c80c142038241102e6010300000c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 624440575 1250 624439325 624439327
    0x61008131a0903130f031101030c1b0507030c0501050c030d090828030c14070201050304150203131118040b0604060e070f020c0a0803220b0d0515090408040902 70
    0x81c040c0301d420911001050862540341828658001d0303a59800501d0800f0040780e1511000c540307048400503110841c0d074415501500c0b9280100154050004502c46004005c4600703014042c0400d14500321600c540194050700903075046042103604d12a00740c122905011040240716031803500001140c60403091a840018101542d00d40380c211840344085502840058450418003a0400b8000544c04800c40d1020424540350703800a5440158281d805074100d0000c0c0056005540240001e681c4548501c1c01d280125000e0a100422a002688d02c2800700e40d4544408040007482c0e102900000401c035030325004a042c0c8074403000400d100510003402040c80001280d1181c5640d003210740940b00b0120810120300d00342000900f4420328002d01c81c0140715541d000101814130100a5080d5010380002d18680100c200203041403602140802c456020496000100c500c51040500442c542040000c280b500f00b40245170010842e44503690b00c103502e02001c0c440020210b074101c07400c9071081c00d009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 624441825 1250 624440575 624440611
    0x903080a020309150a020105130302030a030e03040801110a0207061b030e0616380f04020a030807050a02151804050901020d050c030a060e010b0d11161406061008 71
    0x102d0550148940f400e4120340d00040340b290034054180604421656640200319a60f10320500702c003100b000d104041e000d41c108000c0c0d0f4034074070300c00d030042c00960891f0740442c3c0c42c15569401d0182160301e911000142c01e480403a030071448a5060080e440245024a040c1c2040300e041c0e50003004011a03680c00505022084640405a44941061344d001000c400783d0720440300014181411050303004c52100001c1085900200002c500c141c02c0410700500301d4203007043c150380e0014041f48405c40500180e074005010040000040e2000b8014907041e8850b20280401d5078152050004003d41541031054002d000e02100005d96031000d490010700700129400304040d104d00780e409009129405a00b6112030800d010400e080752808000d500910b00c1210411240781d03500c020a5050300280100d03900c4010411540c0c11200554002060b403803d58030b078441c60305840c03a0000c050100590800c65010801d0f2000b1400f2000500000d0390200d4180e58410841e40240710042c140e510042c030445003c901100c503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 624443075 1250 624441825 624441827
    0x90b030403140c0109120c03020601090b0d141606142b18050c120613210e18060f060c010e0a0302060a0609092415091d030a0903080a 59
    0x6007090308442c0900c695a81d0b640001d803400303417404900c2a01c02d17030444040c605206100300c8611010540650280440d40d003816003a10150226810550307000000f21b0304880403c40320242e005008110f1001401c00100f40c0b581441c203542c243d070100d000d0111207108501c03d90310080881d00c01000d0242198038001c005030001d2811181036422041c900e252010354944007000d0295100307042c0c000c1080710343c42c00035003040094101701c207040c0300035a400210110304040c103803490200c9010311130729541021400b5440030340e00001d4006952400105140b64041181c14080f005020030400071a071041203152942c04684541c00014170305000381400103540c0e01181d020b41c04840c0001c003510940782c241c440c60400955a450a8a002c500c0c107103881400980e049082c81004c0496030701106d0300510564084200504462000b115034440c1d480d002e04a040700001452207016203140a00040d0005000c6552240001c0c04402c04005a1082004550440c1c1110000c1e04599000c5100b40d6560300d2240 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 624444325 1250 624443075 624443087
    0xa270303121d030a030c092117070b0a06030201111617240f0906011206020319110a17010b070f0f060204030b0a0b040c0e21031204051c090b030403 65
    0x5180d05481c0001304074a01d64591540188030110b0440d81c8040d8196211036821702040c0d0b0360b1000300002851510101c0000d529600018520030034202c185040006548484d003140c041220103186c1e0550714082401190b801540411018011000800c5030002e844c3c0514102c1c0090b01550030039441c1c8000c00003201a0420030000c200149507802d0744100c2440107550a100800e480b000c00845070180011280038000034030a04813890316140d02c2110080f600c4500082d440030b001903d403103007902d11031031240390740d405400c0100d140c003404150307079880d2140014401d200a01da550000d10000e4010400a022541500c12040d00904001c0302d00c0d00615003140200148a0001c051034004280001401410840c1c588910b07034614003031210342c505504100486150610030303000701d00c18081c20609424820003c8640c10894014440c000c4000d800c102c0c070f507070840e080000440f10036008000402c101884041d1002943c0e42e8011040119007001030680c1001d8003400da40450040001018584114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 624445575 1250 624444325 624444371
    0x10e0906150f060705010209040501211e060e0709050c0a0c0b07050c060906220803070818010f0b0406140105040303450e060a050909120a27030312 65
    0x14080c903031300e845600d4100d001c1c3d04415040340c0b06030701c3c00c000069502100321400e214a802228640c2c618402559500c0b51420071030813404040c01030103070402c00a8014454003000956440092140a00e01440034058510041c02c810205030306001224015801a4000b00f90f241d000802d01c00950b20340c0b60440f207900892104d140244204400c0c07008000c80411050b01500f01036108982115450704400811025504002e001b00c000b0000140d40300d200c2c0090740d4001002c588883d81106c180c00c011403c1d94107607444050035696070704a100b01c9103000d01c10700000305107010700b11a9601e8040d00107401402540b2014081c8500c0084040503101000d40f00862070300ca401014030401c0d013500c1481ca0101d0200d44440c5100340c1024040f441e00021540c40d88106c82c000c1012205a0806085c07060120001d0400213841c4144000c1d006e1a6148501515000e5400d90300c80101d529401d0f207019500039181078200415083c2032091010a074002c518045001e50818023003140c403c0f2640f036450700c5240d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 624446825 1250 624445575 624445579
    0xe0f01050319061221091512050702012a09051908070314150c0313020a0302210d0302160807030e0306010303030f0c0801050307120302070e04050312010e0906150f 72
    0x15004640c04c0c0d200d03107418068500914600d21980040e801901180b8184945140828540a81005001d83e14015402841c0c464a80301d19080b401103503250940724140c545d0301c0545d44449030410014a04285000da0503400d808015121044101c0075085560500030f0034020300e40841d2140c1110320720034080009000340c000315031400d9500e0915000b504284100f4560390700270280254880450030041c81c0c090081c200e052403468440c144040d00080d22540200d802045a140020250b0740d03003074080d00405030361554103103454110b0304c10f1400c2a038814041010301d40305006c1c03545000040722900c00d895510000c0e46a03111842d00f4241d401c40c2514a81035407520551001104055040c2c0120340311109091007800406540002521080d10900810390540c1c0805800c00040c01c5400240065a000e40151030441d51542c12184891504aa05a030b00380e0000aa0005191201014078010501014203112905080450725203aa501408001001140c001c0d041718030781c3e80007030951400d500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 624448075 1250 624446825 624446831
    0x180b07032105040614060f210717010608190201050702041404060c09092703051b03130614090f0303041805090105090c01050406030e0319110d0e0f01050319 69
    0xc07808031a010b41011a004c0711090708262000c0d00c2d03d00341ca40c0c103901400004040c100202024803d0102e0070003c2002585800110340d0f0710044220144402c2018000840c00c0c03004064000b602d940c2034688660001d800c6501c0190040004c0c1c5401820142c2c50b40c0c240b0f403079a036a50750344c0001001760041c00080c1d612940000140000c10500354802910b01c4801d40781d0340c070b5559850b0413000848a180c60314503150380c0418018108100311241c604541d44c07203410078500f001c04115010410100280c110101d83d0310000c2c0c102c0d521060852070f01c0091110b480c10b4000d0030315420f5524443e000f4005005d01a600c1106804c0560ba03041c000d48020703041030010305481008103107980c0050b26080e00c0588055181202080010b0350100c1d50300e04c515010303190149006c0c5084000c034020b200e0a880c40c615804184052000d14025165400d040b0714181da401590b080341319482810000d00751020414043c0c1047d195110f5115100d08803008002400d003152a9606c50ba200c6840229039070004181d01e103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 624449325 1250 624448075 624448127
    0x7051c090306020a02030706050108072702070f1a010906150c111c060624120b03100504050d023d06080a03020f0f190f052b180b0703 59
    0x4d4000047d21040d40105014400341c0d90782d151003500c6405030302a45510500300f50000b00040e2001c0800410020100001440d061850700c41d1024048082c0080b81c1101444180d11100e08000c4a11805000700a000b002040c0c40c024140351461540310300081030100001e4448103100040302d00901c1e000001c8c000c0d804d41141e410303440322290030041c42207030341500e0700d9000b00d000700031b04c82102c1c14442428503031000c85480b00d0042d43d2000c150b2450054242d2584905011a2802d01620041780c1d007444002c44c090800d03103003241c144074040c002003007158020038000841c074079801e200d8030201485e00a00c00280d41e2038504031400e0b07603502d604c002c01d8a05000c400030325200000b960060650183d400c1e12403148ac00540241c540c071007081404001d900201402c0d5a8006086154a80740c0c0b040c1441d61862a01ea940c072810040c1803901c0c3c00c0c030400304050240803a4003503010001454081d01d00901d4080c800b0742e01c00800446801420326440d00440d90740708140c0031300100d509441d62000120941700b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 624450575 1250 624449325 624449327
    0x9101223010504060f030203030906092b0b090c0a1703090301091119030b01150c02190501030c050708122a07020f040204051c02040f060905091207051c090306020a 72
    0x14030203200c0c0c0b40c040c038605800090803841c803ca02c035041e030380c0c010003641ca00041c500c10007080782c1104040503802100030f1040c000c11041054050142440e49140048045090a02080b02e08005100c6c01c4140c100c40801002070703580400403000d1322282031010040000d00c0890303c2c5140288007a00d42c06601e4600f0107001e001e050700f00d545203008c1c01c0380c406c40b83da0110408282500c0881c48014400e1008000511000030f06a0301500c0210903842d01d04442a035580000c0d8400d801807440214041d1041d07418000d550307040c042c64100c515030341002442c00b131155035510003510580e403c4c4003014115002042244100c1c111107080700004919030700340360b00c500c0c2c1e084002e6444900200d12a00441809100c1400c260094604a580046c0703008400c13a94081814507400074000c003203902651b28000b070300d075008440c8142000780c024003c001810f0f1409810042c41c1c0701d00407940a04801080c2b00450010300c002440c1540001003270040d26022030400c0081e14484400d400c028034072800172a22010107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 624451825 1250 624450575 624450641
    0xa061d0f0717010e0303070311120126032b1401030302070806060306070e04020a020c04020d0f0e0c09061203090d060f0c0f090b0a05090901030507060f0203091012 72
    0x2d242c005600c0c5141d07069900410303080b0382030307400303042415002030002031071050182e801403018109026a4615015804440d01c6d00d01e0000d801c402100185010545601c001c070401640d54104184020351800150351181e900070604207030107103c4e1889800d525100c1d1056030704014401200010900d50950b16803030080c2d29071069006103c8248944000503905180c0019054080c43c1c00780c80d00c5842c2819002400041c0d0f21007100070055201d5503070400d1182d11707988010711019200d07040c0003881d65034014014017640c14000c881c40c015408203040c200d0031b07581c45007500d03040441158006140101c840c5000c5c00c5002e041c4d940c59111004559402c01c1c0401500843c602015410742040000350401c0c0507a005c42ca0702d07441e440048c40486003404551610801000901c40c40e0501c00d04250694001450250b000d0700f04031850f4001c0442048207680042203600428030350700142d420080483c02084c203078088031601004219940380c9811000c400b550100c0345101c442a504500c0003c0d000c1c2c04101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 624453075 1250 624451825 624451829
    0x30c0717030c190e13020307020c0a140102070801061d27010203070905060720030a0606091407110c0f06091f0f02031c02030a0e0f010911120a061d0f07 67
    0x50302e1034110b8061084c3c4100c070300044984008220b50000b0401030158002500024400c83c19031084590340c0e1110703900c507802c5a00815100c0034020500b039801c40028101041c9610441e4141c0c140401030000a0b20b00206480110064074068107a030344910002044141420b1003011a0a24040040c841e07401034006620812050f2510307184c955031503041c01214880c441c009410f04802031240401216a40e02400d1440b0008040ba9181802511800b04890591b0310080c52290789038180191401c8184055070301c2105800d00c840e0b1880a4a0442e888201c10420b05100b03103140301410850359180000c0c2c49900c1d101822804000343c070b0a054419400b680740710300010610440b44841e0044c400000c461058030f4600401014a030400c0c042c0d00031750009000051055250548d40c1d519120420103694601100c1c8008030f40743c00142440140c111880c500729004042190502c99191400221001100c4c0d101800107005040d45031110b030f5803041540000c103240201c2c0c40c0d09182810000e07420341 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 624454325 1250 624453075 624453097
    0xd0f032a0213090219090f0b01031b0302030c070b010306021b010506011d13020f0d0501050a0e16090b0d020a14130b0d06090203131505060303030c0717030c 69
    0x25808040300c1298566400e614002580146640d22070121407071107030046000341e8800b42a42101260140080c082c2c020030b5003249403500d5550080300340e192500d01503c42400028241000b400d80c400c105d4620082c0c0a04114061540020119080d181240c04680d43c840c0c200c1c10601d43d550b101d22300400a540281d400c803140303c0201c13205401041d410703c03079079000b0790341611082d509016844c410580c0640104d6a6a4803c010750320110f108801c80c0003c000c0c400c41008403650b070f410030701c02c5081200e0060f0400342c0650340381c00050080001440425420034280c0325003014a507040002121031040f40e070420002d005012034000f081c0c841c40d802901da00c20107900d400400010050103c401800380d850111006041000b0400030080c1c2e1000a094903000c100002c10300139140c2601005a0b403050b651b005909100003d00f206200030001d01c0b280011311030b1010300c50b0b403c0000000340d4a0001405085200720300149040c1041121041564182c8401000c5520b0b40380c00740c040c42654100c11403940c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 624455575 1250 624454325 624454367
    0x30506270702071203050403120305101403010204051e030d110a11040228030c0311040b0903030d0204080a0c050105120a020904090204051003061b050f18030f0a0302010f0c0c020607020d0f03 84
    0x2c0c012710302a0003160321540d000d20a0400341407034010f025081140d02d100054055508200104050702d400d080c604025141c141c034034200e801c011041c5442c0c04c1d104100c08042100074030120301001da010075131203c0950400c040c2e8040c00660f00028000b0710801d000c03203541007003a05414100b985c181070541190301090714104401184dc01c4181d050300c280c0020900307600720801c002d01412075884040d111007500a4100da04065104220308201d80c070641000780c0300da0002c0350540c1044201449580644001c0c03808504000300075052105040003c3c1407035a690b600813410020326143c50780708440d0190020002c1c0000c0c1042c0f00000085041c2d400141c410300c1c20101200a0104075405102e07031009159119480d2184107140501d2640050848031100740d1341c4900b010740341e80c0422070a071008100c0000707030503c42070703514001e400c490100c085d200d4074a04100c45c01498641280e0008607264068031010784c0c03055203100044000700308101c010300104100038140203142e4003402e082c2c4030800204402e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 624456825 1250 624455575 624455603
    0x30b0d03020a060c180506070c051810090207080a031e0204140f0103020705060a0b041401030623070e01050c0a051207060c03060b0d0e0a0b0c070201030506270702071203050403 78
    0xc45d83c2c103214500700070841c1c0d641d01d000c20150504000401004d0f02800c407200d003081d12040000c02001c17200249001d0a07114074184070005600031840700044c00c1540c8214907222803035440030528040d00101c0014150f4132079140500c5d4045c503c2811440701404070440d0b035207440d40c0c84407a415014a40c00390007403c404009600550007071084850050700880181541d0399122024006080c0d08600260483d4690320030211044101c02164041d62050b1f03008110210315554007194560381c450080c2d00b0311002c00910074107a400080790741c06240f007860020b07926594400c01d07510b80350030308100420758400c42440c241203c1810001d0720343c1c076103e040d007481060760884c401c0301030780c607207014800050404000c075118001c01c40c0e06c0070300c0300604881030b0340701c0c42417644a070407600000701c0740364183c040005050000c40d80d041c400e4a60000c8119071324541074038646030000001c0c0440307140448404001c8041071010303000304a02c1004000e0746440006000c0c4074540204960041d220840b8144469400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 624458075 1250 624456825 624456827
    0xd0206060901030b0f1503010906090b0601030504080a03020f071e02010210021c020d15060905120a08030c0715050c130603140402100302071a0115020a03080f07030b0d03020a060c 79
    0x2000b412a074010b2107680316070b142c0080101040b0340c00340201c0c031100c10141060069480a000b00304c0250f004180000d40140981030411000300c000b4011410185884104030010301c40206452490589140060715200d0401307600340d0510401e4400703019180c00c10803180228a600d064000c08510030703429200b09900118540b01039004250703050700c40e408c6400b0740c00c00c030040d16406030914500d643c002244074050f0ba1042c0d0440c0b030071a0030600014a411009201c5400c100c5942240f81e80c008000740500030894807261030700c1c0130241c0800a2041c0018803d401d0012a0480d00a08027803050104001d003085602c2010a601458060013030f205d8420000a00c54000d102c2c5040d03402c0c0440d40c0c2c030025542c0d0790800421810516001041c1030303007404154042201100700f0f00c109042d401d07201003194106030324074005c0c9582d82a070354215030102000d0000203900006487d04620a010503583c2e5841d0306c0d409030041c200c0c0c5401150856002d8400105060340003411594030760041400f0450181c00044c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 624459325 1250 624458075 624458089
    0x5011d0907092c011a010e0a03150207140109060c0e031c0908070605041409060307091517030702040615090b031801020a023909060f040e0d020606 65
    0x40e00c409035800c04036040000001a40142180901d205414609103000031076810440c0d414440c2011107a41d184241d08072001d01c080c40d4280340d4000d0805000f030540c5000014240341303035800003c00c1100c20013245000321401d87c0540d00d03001c1c1e2152500d0488102c03103484900070458000e06507980b0342040c0315400803c2c01180000160103024014142e0050500620026844510703c00010001e51010024502100b4440754000c1c203201d54030103035214a4451a03401011440818038800c00b24031060080701e94000400c0c0048804400340440c100180f1200d000c4000710640c00300310304070302c1e4081101000340044002c0456034802c40d020000c694880300003c80d4403015400d202c01090b20a0340600081400304d010350781c845a200c40e80f10340111090240c50a9800980919003da0701082089034a9490721401d00c030451203d0b690442402800c100782c11040b64a0541d0398061200003001c41c0a0780c882c0010301040030303801741050014040203840e55903203103030000c88100103021302804a00c05251001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 624460431 1106 624459325 624459331
    0x1e041203110f010c0f140a0813110303131d1b0c0c0a12030f0806030a060c0221180301050103050c01030e0a21110d0903110301060902030a05011d 64
    0x129000c1c10301c00c0410f46c804441c540510480050139030100929034403801a07070076030088034100e00f0001c1e00d2070303d000038070364040c00001044005824101c44100c01c880c042402c1c0030714a40703480ba607016200f0050b503050f0450b1404070125151903d481014003220071028041e0b6040d60382000006403004020341c440b2180d1880140500141600608500075403009400e00301d400342f41103000691141c0d00c4c040c005020755545c50701191294400c01a000c0b01a40b25102019030858145081401d504203a00300b40039824403c48880340c0c0d0906000b02c038101c0342c0c030000800f40085201c1c0198040c0508010381d4400d48628862600130500c5100706482104003032500e5598207900e4800100020080904102564000d014020002c3d6204040104a0317401031a035048110040d1700103409411070380c0c80180340307070300200c00d11a00d030b020f503070006048800f601c4071900100c08102400d4000c480031 = true := by decide +kernel

theorem cover : BRFrame.Cov 624280575 624460431 := by
  have h0 := BRFrame.cov_init 624280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 624280575 ≤ n) (h2 : n < 624460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
