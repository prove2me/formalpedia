-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1552
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:32:40.046743+00:00
-- url     : https://prove2.me/submissions/32a0aa84-fe5b-4003-b11e-3f10a7bc6c7e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 278956834 ≤ n < 279136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 278958084 1250 278956834 278956877
    0xd0605041401052101060e070e0a2315091915020703150c1e03050709060206100b030c0f0408010f060b070f20030114011a0a120902030f0715 62
    0x101da1340710804100d0305a0354030114074101205503a020020919a6844151004e88542621600000f510f1012a8905400e1415004000b41001d41c03116024002e0006200100740a003018144600f00c5612180c101d155001c040d1402a04014092018288a8034850315024014414181d11080350500c840341ea0740049100c0c412030790000e48210410300d0b021281c5006142e100c0c881401d014035545c0540004071800011815403c2c15203000615061410011700940c0480d40721400f1503101d80d0800c04000c0300f003002042101c020660320741e20303074039031050078000f50203905001100c82c1d0007c2000503d008054116600c04500504100030315038448243e100c0b10311844c14003030012818001e0510004012495854507900c00303900c3c0d202c0c0d010b01f0302c001a080d070305582541490494650700602c100140c030480d045460b800703610000d01e0032000302c6000d03040744100218038081c590f45907168001c0d51000c0c40900b6003a10180c040d106100d44541ea440b6255000c007180700300103020403d011801084d400f1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 278959334 1250 278958084 278958089
    0x10507081b0a020601181104062111120702120f0711030109170a05070605041b080d0e0409050f240105100503010302040b0d02030303070309031209020f100c05030d0605041401 77
    0x3801341c20306a08080c04000501c1e503401d5001040e5569501d46810f050418003d030010305883d035a6005001d10307400804901401c0c550384000d1302d5180010f0805551b0652044602300300c04184014841d42c0c030000c007a8146480081d0461301c207040019118104021b0400510025105090247d070749030300b40091501700c03183e282d0000c0041111510f200e01030302080e000b40c0100c024070300c0c1292401e8042d030f52782d00580e00c058500302d500c1c010482c441803010000c101d4180103001c19400034020b911043c4030040084402020060240303a0b15590101845014001440c0c15070351242221a441006c802c40c40800c00074070f0403c4c0224a0700000401c403890901c02c00c200501c8195912030a5074210713000c2100a0a41c2040264010307420b94001d00145c900b40302452040d40c031918001100c07601e5080142c0840c80c03d0f003800000c98540701c01d0f100141c0c0c940c034140d48a01d009030f4808000070402c140580b403d5102d0300025050784000302c0c1242068000b034102c0015540180e40174845c11012849540c4594070a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 278960584 1250 278959334 278959337
    0x3011a03160f0608092e0b0114030c0c0a06020a0905030f0307020306150301021606020405010e010e09040f030c0605040b060f10020d030b0d080c03030a051609050f04060503010507081b0a 82
    0x140010060f240c41902d003141c00c42e030050261035020800320340d02081040311000810510800346403910103400341d07110315003110100303003040c0303040102c15400d014591000502c220007562001c100309aa000041001c0040c1e698459002c540c0c90b2240c0300c001e45610464841c04e403180c8514400080e07464004000e880c40603501900070700c00e1351601c4640003200c140100b0002c1c1c1640d401c2c0181c03054a480b03500030418880c000d66005907602c0c103000c0010301c942c12242d40c00c1d0521855420600c450b85954050380d60160704452003070f10382d04040c035040b610105000c0000d041641401c082c4028800c1082401e401880e084400e40b240520743d40a21010190000c0c1130005a00b02c0c4c10301480c03c1d402600140882040141494440f40d801d070307a4950183c200d200d000e402c640c408020055800c079244030b2280c100d0020070301d4559100d05240c00605e09070710341c0241d034002d1040d405000c2003911030b50003050103418000c00030300c500d1820340380003007905030f0031503036801c0d6464541c08a41010700240c003183c9500005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 278961834 1250 278960584 278960609
    0x30b06090a0e060a14070e01050f07030509060304060608190f110102030d09030305010806010b04050a06120f06080f0d0503130227100911090a060c05070503011a0316 73
    0xa14040160801004001400e11a200e00181001107030510403688030390010080090482e0f0043e41452010000900410511540480840302a0381010544000203100248075943c1c003020b14046070240250700400c0d811290202c14402042842e401000035030f80c5c000c08a5120b41580c2d40c1c0c0b180721490070403014000101c42c1c110700c000b164502c110000c615406004592405548220034822a4600442580040e070340b20014060380c03400f4018580140012800c02e4182400c0000159540c61144240018805009440711079229982c010910502c504542044250395a1040f5901c68bc1d08280d0148607000703114030010101d0007401602d0058000208090b900300c03da609000b1102c2030000c61441030841c0078455100140c200e22407070b10035034007049660302203840c0c46419010385411000020040c002480060341c80d440b41d480b40412600d6520f0102290315690802da03003021500c1d00810b403d9401d090708c10a082e510380402007107640c025011907444401d200300d454007000442c0540c4428004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 278963084 1250 278961834 278961841
    0x405010e09041406162319030b0a06080610091a070302280201090603020703120902040f0f1e060e0a1d01062402010c0206041b0e040b06030d0207030b 66
    0x1c0800060b503001d03100f00100440b41141c0041e95181c154100c0e80201e102c80480b040c04d5001e039004c01030040d0070391604525032a070241b081c0311070b80c140103807141c1c9580002000c942e4015940b003900980150700f000b070841130b00c498946000401c200401c446160144600e0807c41c00c0307207845a8000d004039241945003035100345030354a4000740d0b5400008290210702ca28140c10b90160700021400d1002d58207020303d02000202e03403001500340105540038106052040c8004000f1a8000c05082400c1c11607400008115159100060013020040142c401c0549052030040c0a14400d501c03841c1d0541501d400d051805c0d00c0b01c5882001c1e0b80c224011074103503140340800b05901c1d17140303500071816202e4026014240ca2200b4810a030031102c0c180d0044042501449808252141000940c2042100f0784028440d030070b0141c1c0043d40d20100504000c00e8240f25100402d0166000e1f070041c409040043d00c01c20007818141406910140203070b801d64840d014011184c80420700001e0304400b121740c0314803c00960b54 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 278964334 1250 278963084 278963089
    0x807151802010f1103040b120103060507020d0806040b0607050d080a0522020603151f03051518100f060507112b0215070302060f06121207140319030507050405010e 72
    0x488181300f4030503803000f0320010039182d004034041c21a440860f8030a1a0a41c9141402420743e400500075005641007644810b215560040b889a4003c000b5200402c007040351501141191044203c050103d002c1c02c150300d007286034030504050240c021403005210310303212a0301d041311480d50038480c1010020000c14080050810201030341e44940c50244022891803894041854400040d56400c2082107504154101366090f20030946c1050325a0030500081d03d401c00840c2e01032030a04d60802c8036207801d9000a42541a09200302d02400101030748050395603952002801c50740140b01c08891400714800e04140703902f0149000c5e0061200e1b4170000141c82280c54514031144402d4005a80060a0307400c519120f02e041001003504501c2076000744028580710b100300c2c100f558044c1c03003144940c40c00c4402008200340016600201d02c210100c4a5980e0014600320320b0924070001d40031014000802c49203c0300090540300b0034845040e440c10300440d80c130442c04480d00e00c254011203001c03d0316401055020b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 278965584 1250 278964334 278964347
    0x9011506120b040b0d08040305070f0f0611010f0f09140f21120f0406050a0b03030406050a050c0114010608102601150905091b0f0603090a0807151802010f 68
    0x6107800f820000744100303a0070200d0700d142c0d42810b05413030000700050f00300304200d42041140c00404076201c00e81512400d0a1a00c80026214800c60080001c6d01904010390071083d400b01e0744040e04138004004180340c5540710000341c40401c1382940c00f010400c0310441d0421000c59050000044003014095050740c09454002c114219612045800e9007404015440c0284001c0903020358090951001d462806241400c181ca0000308030b1541d20b030a010f2101c620b5200001134509071610790400030344502c0714410440e01409070902c104140e609009254080b54120f0801d40e0580c0c41c2039513000840e6544226050b400d110901c1000c0d40e0807035441054606100e5495800704080e203490010840100c0303100d00500d041000e400895030b103680c0300180210402c08002c1250760442004500d0498611040092a03041d82c480810b40118400000030710409070611000d20050b0b4030002c01900c4040078204140c03407030804c1c1086000d991a1403880c90301c0c103040005014103aa416592040d55144000d0704640740c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 278966834 1250 278965584 278965601
    0x615070819050403061e05090102070f0803060f091e06030303040b0c0d02071203060503010b0f01050409090f0f030804110d020d031d030703050a0b1003080313020a050411030901150612 81
    0x800c007043c000480000d900e80200d283c00320501c0096040584454031120840703401501c042c56982c4100030b15400a04100b802d1900b80d41c00c816690384a90f19130000c03c040c1d03040d0084a0354001008010815001448400e04c5a11100090548150399468007899500e03c0142c4002e06517012110005102d000c2c610010054101441030250425400e0b5403000d103000307c81c00705240441c1e01c5081c1030013079060901c200c5010000c100c4e80e5505c4042c03881c0020f000e9100710f0240c0000c48c2d48401c2c14a05204601c107100841640c0410316034003010803400c00a2422409640c00c0f10003128903c8002018640742c5032921005400a0a6022500d01590190703101302460703400d0322500c04e40c41c00c8810a5602884418000c0d402030b0f005e45000d81e03c034078040b4601c0d40020100d040d0b461280030240702040703404080e654060881a03c0580d40c0800c1c0c00040c2e0300c4462688815441402c0184c0000b01d005444040d50040c01400e000380480510f9200340540d501260141000003051110083c0640c0819040200c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 278968084 1250 278966834 278966837
    0x1a07140a02100629031902070b06010e10120905070b161a010608070503040c0305070f08010f060f0303050711060304060e010b010e01020d2f0706110d090608060f0405010e0615070819 80
    0x10540706d05180b140582c2c1040c40142c0340c24103440200442540c02c4442084880c50440304005000140400030303201c4191150040000ba5803211800d00b0030908001710005030254013900e6448602c068224100c1d02c07543d04085444050081045000740384030302209050b81c046d030301e5845c480c9c0c0d0f5140c021a243e4200810640740d040d40f440001020450610414020f0300107401041e03003090902c40d500d400d4031000c1e103030802d5141c03034042c0800c00d245111010f001130300d3307051070f049559181c82d0410181806000891590000c80002407004110403940b020341612000e80092011181060042d101040c0251102c0e006d6089400c0808071244621911000d03030403585041d80c0c0900e651030916040e07e00000301f03641d0a6004610500c240e07038100e09124245190f59004000305410703580018440304081c4611014800302c0030105042e5500c05a1201c01d460307010300b08111644c0d40f0f0f003007108810400c0c1c6080c0c0c060324803401d440c10406006011501e00503000041e5a14110310b0154105080e81c001a1600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 278969334 1250 278968084 278968111
    0xb0a15050412150e010f1103090c09060102070305030a02010614030a0b01030305090607050708030d0b030d0f1404080f0a0c05010318020907090806040605070306050d1a07140a0210062903 82
    0x183d12605441900000c41c010307400001e441102610306011912454104206e11304180b0070006000c5000510307107080b14080d5070080030390b258200182d1800196801c000c10500000c070300c55100701d60562010341142c1d000004240051301060074075469113100305000c0c20064a0000601c0460f020b01e000b40625880a4881c034a0304043d616903606000503900702420540000604409514060058048011085010b4045031040303a50151012284a03030403428070443c8075900ca00b5460f10b00548004200081c00e07204882031400e0703800c0d1100380340d110417241d0384508071000c2481d510034490325442507189110780e20242016001c10100c803c00810b1881006009000132843c0c0609100c0540070b03900c5030f100442d0505007403001406640340c07904a10f002e115008280c80102e024010f02d400070302940e980540254851003001c445042420b601503082c142c0004e07201c10020780c00142d14450a0300307078034100051510384040e820100c2082c0c45003003980c00d2001183e010100618025030b003004d203803007455 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 278970584 1250 278969334 278969363
    0x1c0e10050f0a03090b010e090a141005071e0f0e0d0f050d1e03020f19030e1204081e0c01210612211d0109050a03060b0a15050412 57
    0x80000c0d800750b82d81c880065200c81c0300404100c141c580680c058055012803440921300703c0212507540b01c0302c520192005031064001211480d0921950140b2801c0900504c8503141c1010054501c01520003100025806000a240721074480c040b240162052559030301000c10f0714500300030300e8404001c019179440005100d5800080c001b0440601001020307100c428500e106801559039038043c1907099010b041c0108107000000c413484003190200111004035014006203010118001c1200030b400e83c0309032141940c1003c07007040d120080c1007200c102234104c55856000c045000d0542c4104600d03110781d40c0c0301d00000602c0391300440d89004020400c89006c50040114a103c00650301a54485001c4074401c2c49003105115105100840c200e80800040d1840d0000100042001d4450344500400243c6902101d03000d0707100c2e29016004080c0201a10145038581c00c0280003410314450541c032840f5a00c800150329240d9411460941c2401e840b55030506140c03c1c280d00c0350b440b01078812280a9480c0406 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 278971834 1250 278970584 278970607
    0x60801060906050117040f200d08030a0608010908030a0207081c090213090308060603060d1b050301140f190f1a03060a0b09010504110c0a0f051c0e1005 67
    0x104801454641c9011800301e1410b400541002c6942c9040301c0700140c100c00b000301041d0904100c04082c0c0c1d20074990110346174213000070385c000600e081d8074a504c40b500c0140c1c04240003495000e940110040c0c40200085959010080d00325290f0f01c400a10014091000a400400c1e580c0504280c030b010b0045d170340c54582d101d500c0b40c0400318600384500c0d0640c0d54100754000d41c2000350f214070711800200000c01030362180b910050310060008109622030400000002c095403280c500740d10400c0c2c0c2c0502d0203a02c4403181c40300281c1c0c010080c01050301070f43c83e001c000038010700d40340301040c000c40403802906c190b40c4a007806481c0202240440b051200c0d25001403000d501168801d02c0004055242c00700b4080d400c82d02010b041004c06450300c0d030881d091008107605a903c0801990445108a03400190340c00c009220741c000b07014856201105015400f900814080710300712034221749102e64207550b14501014441081c12a50034034150002c0c24030030542072241459265003081c3c0c662401c0c000c1c10300d0400f4a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 278973084 1250 278971834 278971841
    0xb0f040510081c170c03150102012304050609072612030f150105041505030604090803130606060516030c050f07080c0102070504020702150d0e101a0a0303020718060801 74
    0x28401c010030b440e6041c2a40c80e40d4000703001130075803260707040c1d00e042e6080805030304500d800b024184a288944840003a241c2e43c1c002d50041c031031100304144964241420b20f190b048026811a400d07a420301031107000400c1e82e40085038074429034080c071901d05031303030300240355903840c6501d8822040280780314021540f240600407501035481342d030241a81d840146042417400603000b00148041c3e040c80404c1c8024400c04e000d4020b4072a02400a10340252203540d0703800001d01903c01c20070041c190030000000e1084a050031000048040e00030a401d00280d40d945404072010302c2000650404060800c0034240000e02c1103040102c8140141c04890712580600f40c00c03030a14000d94481c50300c0e51f00c0254600580c1d40c040c440355000b0b01e4215011814800c41d600445c0b101d0284401d107420048001450200040550340308940200140302140c2c03c0003c14a0f28070010700c0e5010400c081d001c12031003000c5042ca0003036000800c0d42e074558040c0081c1c5148c90031b900d0007402e03400681c4990a031200c2010a02440034031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 278974334 1250 278973084 278973103
    0x3040627030f1b031509050c0405040606031704290c0d020303100602240601020f010608010507121a0402030613020c070f0f0e130c030204150e0a0b0f04051008 70
    0x10b1038401100d00320b01d007116500311a008a07141c180700e00c501c1003000c03d50010a102a4038401900818894010f28007242441809925298010700c3c0c01e0500040c40450340c00101500d2080e9841c00382041b200c11070b071606010300d10503040e0200801d001c001c0c5600c2400c0b10b4a003903051206600d8142464100c000341010403080c410320041c4c0c4040100815004103080040007000302c2d002411f110051911003180d01c0d0700b03000e0750b01222401030012502c0d03a482003103c0c000b000102d03c005c000482c0c40703007800350190000341c500c10700140105588000501052162900d80f00100c00c4c2200b004440ba4280700203501700a020369400410011640c81c401168001850051a000041d102c3d440c24100345410300401074000c0c100207031701580c0078048403100e00702442e00844540052800b4020714a004100800640c100a40250420140082d001d2001c10010140ca4905010042a0787d440a207402200c5808591603404890900083c00038241a40100d8003c8a60240b207200f168440c0c940c1480d091000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 278975584 1250 278974334 278974343
    0xc030b0a0b19060507081e04030b09010b06031504050402010e0a0b0d1406010c03140418020a02070b0a0f0804020a030606030b07080f0f010e060316120c08010209030304062703 77
    0x1202003506900d0a00c2c01100485416040800c03110704000b4018140d01a9200082040100040c426448070900d20308000f00411581030075682c640768500904801c4041d504c2c80030660038100e0071f0555140c003e0030380b48103500e0b1215140550380c00408010242401070407d07130500120b18540c460703d454650100c07000d001680543e030390301d541f06004042100d0071008001e40070032000d0144010b03681d10240c40350b665609071402079841c50300c8943c0c02c1030f2480359030b025204490b12151801500c020a0b0081c058520b038540a0350801655402e1100807807041504020009020040300710340e4a0040e03075925080760000e0540716943d9202c0e550001256881e4000380c68101d2000c0070096003da0000d15507a00460b960215984c50400300800c003130025040c0100a0516a000c00261041c2c0703040000c650805e6486da8194062540c0c0d480d520310135204403d05642002c0c20b80404031f100c2005000300c4448000280003189031034540301045074014411680703811134042000008041e401d0144124000c0d6026 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 278976834 1250 278975584 278975591
    0x4031107170f12071412130303110d080c0a020c060a0314070c0c031205160b090705030f060609040201090305070f06030e010e120307020c180901060602060910090c030b0a 75
    0xd00d4241481c140100c50450650307803051080c00c04000343c4100703440c0450b0703000e0800d1641803064101c2c541424813180406815030f9001c19490b05200c00902120f0441e4065180c600d0090b885240d01a00ca094408150001c1280341c408a0444c5243c07400400354600c55105980f80300c5450700001d030a036848009800000b0361181aa074040302d04207010680c00c10403604000504c1503440d030f2a40019101703484007134418000c049403440c9aa004500b103940b0100240340c000b01c2c500704d900c1d00004061050369200340900c500032000c0741604000403958058082c0c0c1d00180410740c1ea000c10403070604d2000704120704010030998000006013041180001910305528200ca4160038a41d0003421118150141c0c0f646a0514076000307124100810200404692071080d01d43e280e4800c8401e9180020040b04541c000344441c0e608059208030012180c000c440c80d400038800541c0d9242c0490346c2d0402980c01c80a5038010360401c07243d034100c0f680041e44140c420002c218685503641c6844904d82400c8a1400c5120349 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 278978084 1250 278976834 278976869
    0x2090c0304171c200712120b030703020d0305190815040b09070c08161112060702070608040303231009060803040b130305030c0a1e03080f04031107 65
    0xb8040503414422816940c2418070306488640c904110082140d00003003542c0d05140680301d29403d0340d010000d4100400a43d44e404d0605d0b082d000d80071590b408034001a8202031010040c00c850051000203c0c0060080525a0658081001d40c035000c00b000c406000040095018030020007166042a0801340c4074a00d007854004621556910385201451180e03242c00852101c07070380e036840340580014881c03078031980300d00003440c043d5440e10030b802039641e0b043d4808890100b007144820015240c0c4105035840050002e94a40896581406031500c0e005600011024810240b1410802c2d901c9406841e0205110042403461542d003010000c0c00443c2408803020007400040d030320b5000c0003d060048081045602e05000c450326401940100c881c0c070180012032980c1e2010319070b19000516046005e4980da0f410410345142e0751b0406e00703012600c80050300542d2034801c2c0c4144580a840707806481d03ca205949411107045640c0000300114280300440701050360020040002c440a0308480c0034a804401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 278979334 1250 278978084 278978093
    0xe030903160905060603100e280f060b1305060703052502091018091a01060206180601030201050a03090503070606060509190f0330030906110306011706040902090c0304 74
    0x114000e0030a400b801741007040c452944030320000441200c010701c070001c01544401c1402c84424100c0302d200e0343d2031b1546d40303402444080e040d8029040c0c80c0f60403404203c159030720407040589004d1484440c1405201400c100034900380000205401882440c05900e0940032140c04000a4102e45140000b50702c47c001520440c106070001c43d822a140c080103125240c9414005042081340c100300c0d4800640b221118000c03c8a0320088481240e010500c0d40030540c1c4030b01000b5610310303044440501c1c00816265113080e032070340815590305807a010b07034940d8030b04543d80c40c01307a0250445007000c462500c01044041c021801e04d11414000c1d005580d94680d6802c400001c00180c40d400101c002d2014001c40c001308030080107004048100c0743d0244150103483c0509000f0700e006041a00111720104135400c00700d140c1541540818801d502c110710421004503c0c4003902441d02080311400d021a160b00c41002c81058640700c501c3c0c0c442c0b40104045a08200d582c00f2031003c03001030700c0c906680c020100a000811 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 278980584 1250 278979334 278979341
    0x1b010e130209150d021c020309300705061f060806040902130e1f02180f0409050f06010f061e0e04020c100906061d0112050c040203070215060906130e0309031609 71
    0x8400701c807402e504505011004a490ba01d4007010a0180f089141c0f0fa0310030001c0380c590602039002c0ca40304058445c400d90a010381c5402c001c54140da40101c1c40c203508441031040d181001c050320140d80d101d110d035599960034400180b8030030b075007681c1c010324440d924140e950300f90142800c00044a405810801c03811040c001d580c0842d80030340f0b0103d80c0117019914840c0b8082442c680c1c030305401c94a60048144070070214004242c3c40c032010b0458011010300c0d107003040c40001c00c07038105c2d07809000c401444c135a200412142d502d100207010a08207800c020302e584043c0314a4002c07030806002132006240510080c001c51078180400c01c440d00c0c0039181c03804042402010b02c06d10008042134220403c201019040281e1228414041c1d040e02420512110082c40002c01c0145241d940142c0700319038a0074651000380d603c0e42e85090000c8010410030004d03c243c240501c0443c000c6a001c1c0001c2c000e820500203e070023401e9894005055803000380001159075804002141d1910168242a07007210308160150701075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 278981834 1250 278980584 278980627
    0x50a15170115080c130609030308091b06030603120c01061d04031704060b0a06320409200703080118050106020604030f030b10021b010e130209150d02 66
    0x2a00c41400402540514035808031842c03009260904640c1c0d1602d4250b0034500940303801c0500d0101d60031011619507002102001600d00984400140380d035403400c2c0b140e071001c511003a00c0d0324019100b0700074014180740d030246800c042e0080070386000d0010004a03540d1b580003074200b0400daa44920040180100c50600180c0f01c940e40702980f111880e045d203001d400701480d940061603414004000506100b6240d010044250009003450160b036034500000700b45a15101846e00b012442c075405590410112210501480d00d68010504051411070b201e001010001702104144e142a198039012000f80d500603d08240b107910340e10603030350400e0250910500900802a106850440140140d0740c000805c140e000758540380000040180d007104901902c0d8041d81d0f1500b0112918550684c41c0c0c02048141c000e001250020181030f001100444070785000044e02a041019004074029032030043d0000d00640001030b11810484210300d00d45402ca82c0108100420a076000c14045880c00303400507400c25 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 278983084 1250 278981834 278981867
    0x5190c0f03150b030f040c0f030506070e04090512030601020102040e010b13050a030804030609080405130507020606100c140313090207150b0916142809240207050a15 73
    0x401908243c42020203100c013a0a90022803907504c006010400c2c800e000c1c1020b003071414280e0a44a41d24500903036240019a4400007250552030300d041c070b50515102d00d8503203d41180003400391102c4e00540156650014082c0d40c1155000c00c40490702c440e45520540c001c18107284455500c02001c60354203c1a1101d0300014422000d151003080802d04103800da44c10340b40c0207080017441140520344041c217480355601042e0031413071046410103403000a5100312b1107a4065029140569603803010481902420407050303005ca074465452002181c1170044d100111800042164a000c0524840c204040100d0f40f003c9009900003078088200024559810a100085c0909001c24a030060020b0041c0c00000c00f000c81d19000c07000c41c101418802d80780c042050403001109550341c1d07000c0d00c10072400d1a120541e540c44540f0101102611403190508400311610300b203003a581140da0208034015800d205440760300314468948081025a10802400003c0c0f011b4104180c0880605002910440d12010100b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 278984334 1250 278983084 278983121
    0x20f120303010b0a0302041d06010e060c1005090106050d080d0606020c0f060703030603150207060e0706020a0813081006090b0a0f06112d06090f0304030605190c0f03 73
    0x18208100041507a064030504807079913840d450041d0044000340500d074400b41c0c0d269a00480000b003100098407a5000c1c4100780d03100d11155010009010380c902c02d108014006c4d40c020481254840010340c0302580041c0508004200d0aa44a001911001e0301060554010f000024420300e0340710781d0312500b0300821700303400035102e07032090f0100165541142004241c021400069104209131181c3c0c089406580c9c0209100b82010b4041d4003500290060030040303030210300e884c40c2d03c0c51104000929100302c5690368010950b07001150346045240d04030603c8440805403212002c5252502409598402c140241001445610380f6000d4020381c0da0021031a401103000c40c1d41031000d14000c02c242e034152992400c0040070b5410301d441491422902d5a451110405044071500e00c84442c00f003501100c48807041100c4080d102c0c030101540780c094506994204e0f500130803041000500b00d80041d42d10500d00c48800603e8284140400240c803440543d03500001c2c910444c2d510f0040e014031401204400e94540c1c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 278985584 1250 278984334 278984359
    0x22a0609010e0c06090d0c0e0712020f041403070b070308040b1513020307050c0105040606170706080610030609240609050a09050c130b0a0306090b030d0c02131404020f 74
    0x1e50321080103400c80f034018040007986003070a0326800c500c490070f1b80d8880f00001c2d0b202c0c0d503090310381c020600580e0340e040003503001241d165400c09107000b510010448403d14614103441d00d416400c0d400420180103406002e58280040c15401b040060f10250b4040c2d1101c140c28502440e09105209005060700c0b218081c04188842c242ca40407440300801c00f60290050f81c0e52114202902c0b18015501990303d00c0d828141004100030301038015100310341d86481d801110300048c08035035803141401e02844000804840c0014494074200786826900a078606000407001d07160a00d0200303413405410f606001024140120200b551040f440300c000707020a2400703142c41f0b4189000a082030340203101c2c102103d62203201048280301c1c0301d012181c5510f4544480034086030307219610301445c2c2000310002d010034079005001580c80c01e20701036800342000040c00741404d5800c4010644841c9400c0100703070380000d0429410980d0309100e209041c510005c0034040000c0c0e28152042000d0405800c0020380a4992003940 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 278986834 1250 278985584 278985611
    0x9021206010e0f12160e01060503040615030b1312050306030a08090f0306070c1202030f2b05100f0803070c032003060a0f0e0a0b060f0103022a060901 66
    0x26160094424038103500480c44100004990a100e1425194094480c0705140581400040c6400102c03043c04a14940180c0d42c20b9040f210391001d00c1a03201044017000003a0016a807503001703140a440018440da89542ca0b40c960b0610814101c91200c0000f01e000641c40a020b10181600807408107441d0841c6107160101c046611200c0100004125a8000c0740030b8841d80c0c0d075100c009281030f4018003126568a002e07270700203141d210703a00c0003950700440d0741c0c2c1d440c41214404000c49003003080ca68101071600780b144864200d0780381e2403640a052182d6802145109000500074280101740390107a01101d9410000c2030031010300c05901801c0300c0d40c0104400400070341000e6038075048940200710360280d05145035034400440000070241d94075000741e00401c152110907070b000c0981003141c28402c1040c40c4061141ca40e0358414810040c20400c00040040c0c290300e030940306191001c0c0f043c54054100070b50402d040c2002811401c1c0701201540003203000400200402110790310605101c002c1c815107004124 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 278988084 1250 278986834 278986867
    0x4020a051210090305031008010b1525060c0908010b09010e1905070203070308060f091501090915060f080c0403060207110303120708070302070308060409030903020312090a0902 78
    0x4280c000c80d500c0e40c0401d8281030034800d28640307480e404001d101c81ca0542c42c005120751310440e16a036812944540c08101e00300140302c5d150480c2000382580c146400c840700c0e81c85003034004000e140e04903000884920307511408078030010750700c1e4410030020600c5219044041d0000307006811082d1241c0c075004101d01d035590f42940c85030440350710105805a076221f40310415004003140b1070911a2a062005200c400740d070020050040c0b502960b589070041e2904020001d5000690140552241c0c0600c0450107000264001140052050601075030640d0f44891000c1a2203105c05100da0020345000c040000e0707500044d44c0120f0084501c0d2450305441d01c064070320014042e0340030103401c03070741c0c089003600030401004403e007130182d030013000c407512101c0e505028612218100c8465000465450226220074002d0094544480e03047c1ca400707a1540c0c64100f400020100a48143c00f0001d0b0004004051b032010321020302c0340040032124940d0b800c207110a100354800b641d404003503070717610400070000358024001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 278989334 1250 278988084 278988089
    0x4020d021807030509030f04290a0804020907110d030b0a080706082502031c02041809050106140a0311060712091e060804080a03110d0218060307080609090a170c0f0604020a 76
    0xa100400005000c0e009c00091440800600303081c1c1d0000444a80d101c0d00111040c0c480c0b4808c0760085d96555404170300325802c818100c80d0141d180d10150b0448103013400f94020b00704907000070b003680805655520180e4507094040e8032100204800e40f05205981c0340304145800207000c1c1d01da0306829403449100095903441981200d128440d07030240e0b5090803401c65011640144000c2810a05240748c5d510440000c06c0081411226036103030850006146e0124101208400b000a11010b8074610b151904022003000c3c00226510140401c49038000510700601a00031390b00c903588444410b810000500345001900060000803070000b4002c0114070340c0a94503951041c1d1080b20306884000d9101c058020303201026030850140b41c00714000b008001c0e81c3d400340c04010600b2a01d04040c070315403030031b104040c0b00c160f521200082400780002e41c5420016070740c0790044c032001c0403180303151140c0d1140700320514005910487c040c8001102ca0611100700011208941c4d03c4c0e01800003400c00c0d9000880c001404d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 278990584 1250 278989334 278989349
    0xa14041203020408060406020a0f02011a1e1509010216080a140c030a060b010311090d03200d080601092310050c03030f010e16080f04020d021807030509030f04 70
    0x344504685548a0b806a500400742c8a04440840c11300f4a403a8020b0340000440000188404005c9150f2034414010300c011981140c13000c2c40000e5010040c0080d4480360035018070f01445017401d074801c0d03440c0d005600c0c1344000001c002940b900c2800b8002414450b02403194100021400c070305012400e004140c0c0c200250384a03141e071a180705219452030500b180c183e14594180a403d5001302400000c0d00420fa02c54400d036800c00c4244c2c1c0c41d40300c0e03894900641c170701c051700001852a4800080d0040b00441158940b89030f85090041c3c0c0308a54502d04140c02d40c61030b0000c1e160506101e85540c000c48901e01510b20030301c1107080ba441d01105981e1070380c0942c940078803881003031442d20b030f209006200b03c9080e8054182629502e1424000c0086040000c0c810008401184030005200d4046c0c004005031441d020354401109480e54807074031480900290099034042140d968250040c1c1c1c40c0030a599000910101d080b41d18548407001408454004000c1c1c0903940040001c00b52541d0000708650030394800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 278991834 1250 278990584 278990603
    0xe160801061b14030a090807170304033c2d120e060d0204210302101a120a120827010e010513060b030102040312030207020d15020a080a1404 62
    0x15080010b00c3e0b00d40c6451411290100180384003040b42d00c101844240c3d1718400886103d659503080e0104086070030b0100d4851500180414800141d07007406075402031011011105d442c0c001c01078180c00f00c588180154071300f94100340c50501006040071406071240d0240c10016820400c00b15080300125580900034500c03e80c4d5201050480d0041d04514225040505610340751240011680025802070080c05d9490701c0381c40d900d0b4022400d13817420402d4540c1c180d000e400392060084d25200901182482203150a0141200c0005601c0364408c204040140800500070210030381400c080c3c046202012204200c00035041101a040c51280400c001291200e01c584c0030022100a9004000340394a0113019403c00d0140451050301010016109014503001c20007100703410209400c0b8410744c84018030780500c003444a894140694081c00d813060016000a540703032000da40f02e100103100c003407448026640c0484c01c100e80c154086005a4000c1b24000d040000d00036405641070038100040c0000c00c074405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 278993084 1250 278991834 278991887
    0xf0e09090a050f0c01020c09062b020312180d050715020f06010303030b03120309100902040f050901061406090d02040e150705030429190204050a0e16080106 69
    0x8007040191030060300001503a00c9038003010100c60b110103150b006036006210781120030b034051030f0120259004110060400f0b0800c101c0a00c0d13021400f46c03200c283ca103988401c1410901584081c02209501083d0b40c00c0300d0360355072211020f01d140c242d0b0b4412040c02945444508800a000000c1030341c25034100000408402998a4040380360181001c4807074072500494000108040d0144c001c1c10049808030152061240d80d00d06080c0203000481e00481e503035101c0702e05050148800d6000350a070b18009400481d040304035105c1101030ba00c1c02c0e1501261f0760b54421081101c00c1410549501e40b00045601c149030008400024200440311703003010b88200c1d0380d82d0b0b002058850401c40407044c486a000700c50014a0144005010350300200c130269600383c014403d50340c0e05062201c0401c454990f158003210701d9241d16240c0d820b80f00e03c0300d1b42d0b5030685500b00000300d0155590f541440081ca000407a4481d02e02e40302440a03504049500b44a007404900c0c0010300005400048090040c80001400d2000c540c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 278994334 1250 278993084 278993101
    0xb030103120e0310020d091b06030c180e13051b0909010603080f0d06121101141920190203010e0a0834060b090106020f0307080706020c0607110c010f0e09 68
    0x3c510000400c58072300880d441802001c81031800c03088800c1d6849c100085200240c040d02c0c450f445074070150408030070540034003100311800d15543d0001c045000d510900020395445610306211010f15200303031051405041500c0c03821030200359004032000001d0029910390b07a5020780e0b81c048c0c00704802101c280072800044403041c69210300c2c000e1112440704c2ca68500036080c80c0030088000c1c02840c1c0060205004000d04816402c112800b40d01c0f41003183c10f0318030054070110340c2d0310301800080281e5644090203100390002044420740f4400e0018020540c080d0310320400d03003122510320600d41290403480744480030903c698250742c084001c10034130503904208001a504082c036180158424540d4489448061200c0e5510900d506001655246e0942e40c07210300a03640c8185c2c07241e401155a20400c0a14001404031000d880e559102d65405800c01901c04000c5082c000100c402a0004c0d51080b06020703400b400300401c0000341401c2c01c1180c9014510f01c8018802e94104522501030200d1801103003043e0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 278995584 1250 278994334 278994341
    0x20a110d24060e1003140f010e150109050c091c02090f060118050310150305010603120f0f0e061804050f19061404090201180b030103120e0310020d 65
    0x65070001810601010714401c1c0505450644404070000340780c5140800c1081e00a00e0701409100074040355004146035995500541d00c43c6c0c407080d030843c041e42141d506800002d0082c90041c11001011304202107070401c00c03507514081644009c0c08903080006203c4003101100c00c661900000b5181040c0d400360b0403c40912041c1240b400a40001c10503040104009244080d1801403c09995407040222050000c0c0345901860040a6058020281070f500d0391115600500800024080750f0b20b5451341e940b103075800c40e0007584c815074403840324552201203e81e00250a900900031400d0a50448407450b034000c111440102000b8043ca00015901e011824402040c80b0030880081040c400c0d4a40518500c08100040e03840c001c104104441d40c40d4200001d000f424182c03490920031280e24482d403010032000e00642d0400f44c1c148140e00c540900c00990310158003018041c40c907401c0b581c03540b40d03187c0a0042e54440e1081d00400041000009d1a03542c0811400d0205010400142c2c9404002c031007030000307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 278996834 1250 278995584 278995609
    0xc0a030914070b0417160e1503070305010204030203011b090b130312020703020f1c0602032d070206060405011404201314180a0e10021b0c0a06020a11 66
    0x35200c0c0141c002a211103143c002c0040c0c0c1c000b072444445c07007040441413aa44003c0034031440c102050651003400382031003030720441e40d0041104142d0480130341d9420110b424500f50b904240c500ea5000101403080d802c0034000e1b04040100050b82d45c2443c06001c03002400c60440c0e00030014450300000d1105404581158044050350700300c0e202d50840601501c001c2d40d125071a202c124040c0b0101c0f4800e400c1447c001c01343c01d0300249610344112104400c0c3e51424000d61001344070259000c80c009022803035002c000000201d0b03941c99411200c3c2c41c03d0924020f031610b50b000741000d00c141c0c00c10f0010f000400800c40c1e034842501050303c01048040100b21880c00340700070701e107074131840d6607000c6543c0031229841d0344a003003203a07003c0b103094100c1d14a007400e21481103540903000d140060000042008016143d0015030850319038800e6490300312503c0c5640d426070307005003880e65100d00d00c4103004054420501481003410ba0031501c41c00b0051a2940194071082021005020855200440350007a21001c0c450080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 278998084 1250 278996834 278996873
    0x50402010c0b0f070807050a020d1101150602060106030510030809090702010605031c081509070c0c0308070c0e0f0928020a0e040b0a05070e040b0102030702090a0501140103050c0a0309 81
    0x140c2d071400b286000c03041e0008491001c0091008404904580e009070100c420f0900154054039000c281030030143e5403440c03850002e0782590358800010b0307035100c40920010043c241503409801035503d402c000600b5104050018102030081900403c00610600b0413140c40c01400e54810510b540c030604141d0040240383e01103601400b41c031701d03503492a20f45007500d003100700c0745911485101d84407100041001c0c03907003d80d0342d90402c440304081590a40030b10341400a0a12075003401280035240da40d8002987c10030b010884036802c061703200388081180c800d40980d00a40041040020b4944005120350b15002d1103482403804200c0c0095803101c02d00340c01d1a500c410340240c400007074603070b4940b111341c8480000c41e42070310184030b180045543c01503a80240d60180486940da546243c1540e01000700410b4625001815407004004140c01a01c403840070303e1058849040000300c942c98a1510015000c0302e801d0241050725040800070659402c0f8296010b5000c180380010304121146000420283c0e24140d904 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 278999334 1250 278998084 278998103
    0x10f1704080307110f0a170403200411030601201219090807030302150a06150c060b01030603150b0d0506090d020d1707030509010f06030305091c0f06050402010c 71
    0xc1c80300340e01c000d600680c480d0740da800e51040190201d0383c89010307568900000b5005410082c1c08200c1c10000310b02d0583d440d240c62031400381d40e42d03602502051030881604614851003031000c91841d080c400c50003541e010085542c079610308480020014030a41c0309202d080015280038a451407420455040c40c8400120a0303550b07000c2d0100740f61840102a0340400000303a043c040030a00703100c080341980417aa4160000c00c0e420303900241143c009103004201800171541c684001885032000d21400003000305980342d62440a4040c1084800e07a02d1040400b4149410210300b000020326441032082c203010103610000d101003c032800200981c2c90000d028040303120358010720400c098003040307020030030b0300b6a001c592200c0d2204800b951301d02c030f2100401c40c80780100000140c006009030007181d40305e41c1ca10000221040e481101c0303401c0300c0182e00b00350000750020a0701419030801075107500780b00e125442c86950b80c224950300c16584504031a4028112925200032404590240003003601c1e840e4000031a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 279000584 1250 278999334 278999341
    0x1203160c120605240105120415180201170603070b0919030b010f120b06130605130204060311030108190c0e0406140601030c201e010209090c0c060402010f17 69
    0x40c0040c1c042035450855030581d09520501c4404c071100030303010303031201a15400d08000c1c004040403100c0e50018015107010065420065008a60741700d41321042807040c511004411030740c000100f420005c040400f407a240210203210340341c1c0d070000e07948044500c529000caa95888440105002c914030089441d02512503000100c09c208051124078103985145100e460032654403c0e24a440b0b0100030006404450000c01240a81c14188040f21609580000100d8050307650300100700c0b440000040466815400315040c002c080c7e15008800b104001c080b032160965041c1240e0320745131080501c0000d602a00b2682e4881000120b0010a00400000d800c5401518150602501416409510047d506130344000030301c856000748100c0750b8a0071185c0d56402001142d126510401e50403d01c0311581c3e200e90708900d404001114401000c1c0c41e481c0001503200c802c1401444035521005d0080d103d4810140700c00084110000303846d0398440d409282c010310914501c1416500c8218140e10800700300400d4080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 279001834 1250 279000584 279000593
    0x12c030c150612030403080a26151c020310020c0709050705190309030c120516080702120a05030d1d16080c0114120405030c100504111203160c12 64
    0x486100e12030907941c1a07008040e490740c03d900c80c8201e020003024000140207100f1201d1103210211000e00700b84000d0415040c0403551070258034011030304a80b980c2043c0120034903e051021801c19001a5841068141c8407a540080e071034115812180c02080c3d404903159104510800c020001000a48070821182c01c0c46240102960300c4100602041c801d18010400e40a1003403003110703c05a0581e464078125946503961400030100540340a08000c014807034081c4a1613518800324a00344140404e0f50b40d002ca5206002c41c10200b0702075a800c0742c208101c2c40010420220441d9002c070042c0e0800110b041701b4000d03481142200012010991007904c8200c2d00000300c41490109490005040b58803c062803c01107508019910541c4e20b010420300c844900010003131200f98000348980b0680b03061980c054070485c80e04550b8041725802a40311002e210a0000c01c4003d031090340020360380300c1d5400b050342c80401c3d9a0321072004010484802880980144900000c5001c064503148415a8601245051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 279003084 1250 279001834 279001873
    0xa021b041401121b06023f0c0705030f030d02070501090b0708100e01050a090504081b060f0c0306100c050703060c030e010e1605130e060f0a0b0102012c030c 69
    0x80858140c0140d0036981c6130420140f014004a90b102d5000b00308820100840c105084a081c0c1d84007030017600000741000c8035413003207400004d00f1030040116072101040c200403440c02c4a1a0701c114040e8101d00d5848034a840080700712b4440a20800d40540e8070619490124018000c455000d8400b0030064240070150b581f114245000f58140405040216200c0800c240003a000b0711601d40d0000041208214208242d044154810300494980b03080052840c0c1c504012141440c180103d500301104100040515098407504014030221250a61503e280840c42144210002c0000d1284280000e000c0150401c2440040d40e0f2004003401031007001c2d6000340250440300c15511003542400a2017804e90000542c1c0c00c41d1a0154803010035031850714050042011420214003a0035440d414004900581048a903006441012505000e40f6205018004071070414503440d0459041604403000c20211605d20620700c1c401e446011900d10948014502e1031051602511041c0034410029102264882 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 279004334 1250 279003084 279003119
    0x2102061204030f08060a050d03110102191b0c0506030a0e1006060318050703030e030a051c032403031b020a0305070602060c040b04120c12050a060f020a021b041401 72
    0x4a5020004403030f190241c884580440d941c5802240c3c19900f0405840e00f0105a81d10382d000c2d0401200550203100c150382a40c3c0a055480d0f880c3c0e41607840014000d520400e52400503d40082040384d00c003081da201032404085101e00c503c1100048042400d046540e404000259003010868201070064420200985400e101c1d00020929169a102428405116501000fa488400340139414216541554010304652007030b9018443c0440000001f001000410511211c00601034001c8220399001000d0b83c0480f51199180c4812840e40318400e90654840000d803541800c01c208031802010307010030448034540001e035008040c11000000c0c4403001c02c4260a6030031a609071955541c074440309140754800c1d0320034548442002c020030841d51394400b41c80d400c6203204441c5a03401d5076a8040300d2004914070702082d40e45400c6181004c007084003030b1140c800ba20400280035410001d80c1c5202a40b101d04502d413060b048076260000328600d650300d5104031300d804081617507021156182d0204040100210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 279005584 1250 279004334 279004337
    0xb0a0e0402090903041a07030306092c010b150706090b0103030507060b1f080402030111070b0402130513030e06040b04060f0e03010c12050a06080303090a1208011a0a11011e0b0f01020304210206120403 88
    0x30310cc8a80e244410b0082d181c0d9240042c2021036002000b1001794075540c40290f0503241242d0329107041d80028005005240214001d0b920180c07a0601d0b800d01c841210b0041030041d125120b420a050000740300c0d00d09010489010f81820602652140080b9000d4101080311101c4110001100c40070030400305e1415000b02d000340c8184951038000c1d038241044030401d98810302000c28001d010000607201d2040c0c4610740c02e002d13040da820655034181c0510315400540007100400e500706a4107100c00d81c080402c0980d1401180240021581a00040c1019030582c01100409481d000042e4500c640c9401c0140100704103801c590350307450140441030700c1d141c8608007102e4981d0030303080c00c0340c00c07911840703c450603540c0180e40c00094044916101c01c0075400781c00b10a041c07000c101103040b6600ca0a200700901c20941d041d910800348204003414040b5000030350158131918580c44403a04599001090300c0c00d80b840c1c00d40f00342c01100307500300c0b10305035080248000303511040001d0303c40c9100031800101ca01840c030a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 279006834 1250 279005584 279005651
    0x11040608100608010b0d09060f020a021b090c13080d0201050f0a15050409151505030706080108151e0c12010b07240b0a0e0402090903041a0703030609 66
    0x8984020074014014400c180c00500080300511021408400030048054510800540040e04e0f5640f041030303400f038003050781c0260b5012500c4d400c481d406000302103000b16810343d082c014000f20f10004001c0000a0442c900740c141c0840d4104800c900c0d800440c0c05011a20f04840c1c4400e81c846000b406030100300c2d00e8a05080704140411400039143c020140341010b00c109054441c2c0c20001804000c0c403220209462400e40e1035900c070300c412024031410480302131401814130b4503800e20042c10b14065442d8070400c203304c4d003400104090f010118001d40900143d941203407944d00c40d1200e0441013804101c4900c0110b00107400c0c003124040e0100104102e0441e0b803010b6800740c0c3e8138440b04402d4003980c00042c01d18036804103489018958a000a02c0c1c0c692800f0f4001000c0c03c1c0e02c40030500441081c4c1000c120f601002052006510303007040c2c507552100c01e94000394034050404d0700c8910641d00c0d12011807070488000ca540020940680c0101018105a980c00c000c10319031480c11043c6821800c1013106600c10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 279008084 1250 279006834 279006841
    0x71106090f070b13121e0b070e011704110a0510080115210507050409020a0509121c0c240b010905030c01051606090507030311010509010501060801030305071511040608 74
    0x507141c0540c1d20703c030702140f80d5440c014079000015411000e00d103000c4070710300c80981c0e40c40481d50f042050000d01b24000c43d030681a030f10b01004c015104220b0328000314140040310303420000c00d54842c03200a9009a01c500f8904454546401151000101da00101c0d4410030f8103c280700714643c4912001d0403110020b40c07403090000c2004044d2901083d4200c504001c03800c0c15044400064150070003a0040820704d0304900d45076684021304120303045840c0d450009040018a5034962800064003104040d440024040c00c403104118054650505c070003030003d028020085206125410b032800b40c1c00a843d003209260010403190107001405d11a40380f6012500c0c610300401c042c180051031044a1006840e00d07450507541c2c0c0b400a90708440e8450464009459511510000e0024006e21000310320903100c20303080e01180500d060940c2c2d001403182d07640741c0c54076004011140c1d0140710503044030740500300641d0f40c0306141084500f0790100320305241a1420300780020010a602d00050003200c90f0b680d40c0000544 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 279009334 1250 279008084 279008099
    0x50705060c1c1b0b06010e060d0e01110306030705100201090206040609030b091c1202041208070314090105030402010c030c05150108070e06130b0d052b0c0b040b071106090f07 77
    0xc0e031543e24901442c0300c4943e0790300040080c80078a4100f01c050401308403183e62100052150303402407880042242c2c8a00c20007142d104240141440d04680000c86030852a194002c02d40c2e0b01450311450b80720b03410200300020103500071743c440004103070081c01c01a65591075201c0038003428a80e110803035100780f0010004000900200701041c1520343c0c101c030810b02120801f0100c852251140c0c805100766801c0100080d291034a0640400b1144140f86160300e440307442c2005400f001039103041e00c10458080149220f03903a0300c10200c030350050342401d00303003810003a80c00d08031184030310341900a00e03078070410718002c407258020a00c65040b10b10320030440740600d40b50390350302000c0034054502540205617032110101500d8150030003000340794081d00011401d0541d0b220703a4030f0f11500d9540d80f04034a0403a01d140f4030303034004817070000203000715414600350001e480c0d42c41c15800d80c8020300240c84080c1c180041160705125840b000b90541143e01181e800d0f0030f0180026484245e0300e10180c08078401c0c0540001d041c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 279010584 1250 279009334 279009347
    0x11b0507030804030f02030c0a0b061c03050406050717070f050f010603021809010e0d030219030b06070204091e060e0601062102070507170f07141c050705060c1c 71
    0x640c15039510100d0389803544e098a0060365501c00d50150300091042c00540c110070000641407030300a102140715070038010b041c01951030b10301201071a040902130008011a0b0804100c500715000c5203420350b030b01d10700b904180705412090040200c000e01d0000d420418401c1d1040180040b9000e8000c3d5141210842d28413403c0741c0080c0f10007034000307007903441c4c0001d035240300d0b603005030301030b40c45d100204d00c44405458590030718107000b0b1004007107940400d0480c0318a04100c1d40c050310082509040140380b44420002e00306000f14040280b0558a500d170400403c03090344843c0c1c4410220070810300c04005a0302e440340151400c0200c0c0f15051040d0800001c07014480c0104c2c00c03040e525151703004141441034541c1c0d0301035400003500f980d04e8451480009001c092401c0700007800c0c0f2a42000e051481100460142440c2c92175100080c880a504004c0103540e40701490039045510680300301001c42c01515051b0b09005417a4071456211001142d40c07542d40002180d25500243f0040d40c3d80c003603204141c016a4030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 279011834 1250 279010584 279010597
    0xc04061a09130903090f0501080714130b0313060e0105040b070f0512010e0604050718180b090103080309060907030f120c020d0606170703081821011b05 67
    0x19814010004151008000402903060042c00300c0c08440c10303a40040c0d080d601d20540880018201107020880300d08010042d40144c10700740381050907414400802001a1010702117075a58000003d030315042c107014031940a0042c01c501c1442034480c9041e04c3d9411504070090b00c01d8804c142440d0b1500b414050600c00d45200325404400c407074668407444d50450704000494284018020100309215550000003103450003020780c02103901c000d1a001c8284800e50314042e0082d424015502c1104103071001c50740d100415544a01c925503091022640c481000c1e01d8450012500070909900100600c60190300035841981d0000885100303446000200350303150a903220182c020400c5102080c001017844003400200d080d1441c11610500464002600d01415440104c03007559442c0c200300305901010710741e07410078402040070703040c203500c5e5440b0f5152074483d002e100100d0003004410048150303550031075141400c1088881150030070420008900901c14000840172a110900c40b540d08144524100c03484c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 279013084 1250 279011834 279011849
    0x605100509010908011a040b060a0804260d0509010b03030307020607081819020f150702060a140c010f0f18111f05070b010b0a17060307050402070302010b01020c0406 73
    0x282621148000c98080e00440d060358100203211200040f1030300240601c2285800f0110031005110466042100702ca811640aa001e02000e204042c202c80e000010a54446d400040c1c1c007060f40c00b5000ca9044501c00b00072a07d410110208282c0d00c0032030180c1c0801c3c80380f41d0000003044060071030803c05075240000c4913080300591000300066509803080409640083c0100040c41402015018060402c5444114a10130f100c480b4014000d601e0014509041c90a0695800c8400403040c41d0032040d5100e40340e0040d005035800606840c0c03680c0306920030980040140445134540a00800542c040c111000356000c000741464068480414180300f6891428008030074030368000f445541d42c8600c18503003002c19a20500c14508125a100325005002416560b076841716510031403842e00500e12013040e0042d0040030014800d00354220b80200006084a07191030b1100025514000060b14010310b0b0f03000180c106001045050401d50150042c6640c1402602504e090502600521013104d109108108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 279014334 1250 279013084 279013099
    0xf0905010e0a021c0e0a0c050406260c0406182306011133010f0e0403081312080f160e040902060405060708131a09010807020a0b0a020c070602010605 66
    0x2c207010b16560041c08640c0016010310700542c2400455000c880380782d48207068640101c00054208482d001800004c1c100840d0108411810042c0340ba1340410a003811b1210341c86040e09030000c649080120710f6500000138424412a902d5400031101d00c0c11100300040050b08007490000801c49118048086006003c1008441d58459004445010b000804041d442c06a00800700020803007810ac0c0529010220b0901d84001e14240c074003c1540050303006088040076a0b000b0302405c0c2c050440b1a40086d05480d040010340c13240c5c0300a006c0c00810300c400030001d0101c0110a9809030b04890340300c1c403818100b8915112540d5010300c500e91018144c41031070000e080840c41409920f40751b8802004c1a0000d4245810300e034503038000c02d04940c0603039401d95884d0000f04643c0b0030070b1280c5001c0d10203070402202040300d5407100c00e0107104c14064031002d54140008400001c955510822072290340d282c218180811908050036204001d62001800c1d4115025540002c00d0144c014001e80040740c0c030240055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 279015584 1250 279014334 279014341
    0x20f07170a08280c0201021c0216030e0a15180509060907050315030f0c030607020a03050906030402010c0203100c090b04050a0e10080f0303103201030209030a0506010f0905010e 78
    0x4500d000000c03c62402000d80180200e618428940b040d0b00c0003010035000141c1d29002c46210450084004032a106d00740d00401403440d21401d030014440d030080d031505013803030f04281450000d8421005a00316003070051070013000d4660b1a0744410942c0320b030300800c94600d40b40e41c0c5400c280a4000303012030340142c0181d81c1c8004100214866002580d10941d02c3c1c8044003401c17458400242003190400d03400300154088580241585000c3c1b180903000110340c001001c5c3e1175110ba9000e031150240b000b5840c450000480044d09590203420620340c0160700506880c0b0a070f4009070b103040201110034604c0e00040d403801c0f000c580d00100104590584000500c0c1e100e00324600f038898080c1841c001c00301c03c0d101721005000a40c100c010001212650341000145440c0e00d0008005415a4541d90010810b500020004280001c24008800407441c030140040d031203d202c0c40050700680718100880b40c0610507800740301e00340100030881605a581c1ca001400f100d694880f22002030725000c0c0140200c001146010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 279016834 1250 279015584 279015601
    0x5061507020d0b0c0412031e05040819060603020409060510050901051503130b04120f03020301051f09170c090f09150702070305031801180e0109150801020f07170a08 73
    0x550341d000044984c030301c0c80c05458802e02005500f02400c00c902203124000c050103540c51101295420800502d805803c26203030610059031060390400c7c80c0d203c0c1d4000802102400540e401220245402400901c5080100d02d0300400416040311a6280481140d10100b19480d000d9046030417510000c00582c11100b00c1462841d1550000e8903690f03540b18284101c01c00190085816031145020302025200804e02a2005e441000343c07940d03c4040520400050100341d9036111440c1b55825403081081d00000f0410b001d86980c1080c0d04101000c1c1e0411012034514240024401c0290b081030b12a401e00d030b1600c003125104190151070108964020006a031400c05da004807155100b801d80c4100c0d08074a50b2516440e0665010303844070114154803190100803940c100c106450031717400c1c40703806a25103460314600d03414070401030040c8803100740c4600d04183c5031075024509030b000d812120002c44da900e0b0f07140c6144820360701c0a20100c0c2d0780b074041c4003074030250a0b090066900e801d50719150035495031755144c42d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 279018084 1250 279016834 279016853
    0x1103071e020f0705041802041b0908150109270c08010e010908040b0918091506030a030c080d15080d02070b040b0702240309011505030a050c1e100305061507020d 71
    0x240b01b910f5800044201580d1039010b00c005240c1c504244000c0650090700003042107070b660300301111a6116804030001e440000f10343ca4111143c104001498002507021140815070f000b001940121403c01400103110303188600030222417400c800bc1041a007800c18050990320b05130b5002d00082024001085803204280c010b10074034800420b405100c0e030002000d0b088100d816a5503407069070242500c0d0100c0500355442c980c1046e02200100f010460654000384001701c01040281551310100b90240d91051503003021052045407009281525203414601d0b94a0307140002d0040144142100001e0031986001100e0541d480000b04c07030301e004c1440d02030041042040c071903042076200c0729485082d0003071008065801014810000310750381c061300201303902c540030300d0700807910031b801000000d8001070000850046070a03083d194110f801001015404110250010090300f14481c60140201d0680c55804513206410407100c04020094440c0011054050760ba0029042125991711001203000e005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 279019334 1250 279018084 279018101
    0xf0a0617030717120a0603060605040212070e15121006080402031e0a0618020405071e0c0507170d0807030c0903060504060605130e06180a0201050d1103071e020f070504 74
    0x40709030311388403110040c8600c0b05030031507081302c240fa40d40b402841001030701d01401004001c122010b6043c1440c01e09501c07100752010340607400b13018000c2c001e58030395100c0c038542115485521406035110340c040561564109000c90b0004060301c010a80464907500906425000300e402400505110071000e5508d80c0e039465110f09051a845190041d90000d1014000c2404045900007110700414142c8180015100041e000320180410042c202c551003000ca042400070300101e00d0582d0310342c006410002d0800d070b015040f44c203079981030000d02c96442900241c48803521410381e40c1d0410030365440004408a61289130000b00042e01400b0400c0802c1c2107401071508140180e800241076655480013608140c07445001d01031703207a1141e0a031a0b40754004d000b515801a155406460840c90f482c94460f21400710440003410b122001c20080300710701e41c960080303a004a6501a04d40c0c1c0742440b100141c40c00701c000c20b880b00c002e0441c514180c4007502c080f511030507403c103840040504500b080300300b001410909 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 279020584 1250 279019334 279019373
    0xb040804080615100906080a0b01120e03040f06050a02060403051c0e060702070e06030604020d032c131b0f020f0610050a050a12110a0504050f0a06170307 68
    0x5000c0422468402d20001d4010322a08850b080052624014031129003080e81a80013407141c024002c206a42d08030000a920840b80c80c0c0c00903500c945200182d610b00ca4600c0341069031841d0402006220701d00100400036146013000385400540e580c83d0486080c402c148100c0016001900407800090040380038282007950860b031040c800d0b00c44044101103c0c1ca03a0f0301014203612a205002ca281d0b01408880d0242440380001000c601c0e00c840401d68840c0081c1c402030144001440c80b00a00d4418112a09000340000b0002c4004900d50358240f08015000125403207142007401885203441c0c80d1091904d101c0303d41c0b04100d03802140c088182c1d54105040300380030070360281019402e0300008c00e0045600c00d01954802404c02403c140074002e5010650300300a004111100c802c2c8180d41c80680170500320f950190990b5a080c100e10082072201c90240d00c20764009041c002400303002c0e42501501445010700580401c4440c0e03680440e2140340440c0390751240d03290400c20550000c0340c01441c00503500c9406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 279021834 1250 279020584 279020587
    0x105060c0c011d18010f0b090a0312030b0a0b0c0c180403140409020d0e01050901140c0306060d0c030b04050a0b010c03050f19020709150506040603050612101406030d0503040b0408 79
    0x40c0408101c1c58400d1181d0481c130400c1c044014010100450205c402070041e41ca2000d092010b4100890052440307404040d0101020303510b0030302080e110740c20019800e680070b0400c8614580e81c07041c2604a40250440b442e113030142043c0040c69040c0b420921903407056400c00c44041d601c81c0c0d1000e84501c0da01d8001191494410840031401160b83d000034401a0304103000080e4040c0c000d0007050840b04080d259550a9040c5200c990460590001e0b540d008012801741640d00d07110710000840b28400c46598042007818003c0c2c02c904150158011200c41707905550900c120354880040c1806c0354a041d84943c0415804452000864454000740202c0361804080600e000341090000784807170790341c45004005900291007442800014098a101c0500310074652001d2802d10002440364080c6029034410190703500000b6165945400a00440741c074a0400d84600703001041c00000034040b4000d0103a000140e41001c00e0250400041040b00f0340010350b145411a1900d80e0f8210118801901c1620341190 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 279023084 1250 279021834 279021887
    0xc0c021c0b09070608090601050904081309180308070e100e010c0f0f0314040f060c050a0212010222260f06090d03050c120118020f1606050105060c0c01 67
    0x20400041e40c003415420004250030351074000024842d0070f00400302d6a16070440001003080e80c403040c15540c0c1003584940d2403511240c44032031030080741c04030b03500010640e801c1015240f580d080c1c042041e10118002d9540c1165541c6001c2d007541c50404405455810071149000e0580c07892181550001441c014074204107003021584038094060f440d000b080d02c5807030700c8030026020160070542d1081c0c0141d0501c0d41900301454890201c3c1c90050903c1085d00740480d010448003000010b0041c1003149500030700c0843c052131100004c40c000c0d000710700f01000105d410181d58429401a020b01000c84203820380490b58a00a9180c000444500074800d040a00c1505842079422a044c0901031003120003070018076000398410801815181d000e022600464001c0042010310f507000301030581594203c029a01110254007000b4000b84a1342d6244200307564003107aa9400c0e8182540d10b000b00300c3c06070100f40220707600c5504125080c4101c0c2c8c0c0f480710b01e6025007100030165005002d8090b062980d982d00d0f00c40d480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 279024334 1250 279023084 279023093
    0x61206030b0903030f16020703020108131a0901050a0b090a0c1e02010b100302091c020321090a050603010612180f05060a15050a090f0b060a0c050609010c0c021c 71
    0x503090b0303103204064102000f00034100a40701d083c80c2d40302c01504601c9100f9036000b04040d45a01940c04040c0c10480071400268038840603041000d0740d542d02c0110003420100c0492070003101c690a8034002919401d000124090010a015850500038010710303404054445d0b1465000400d001c40601003400040451031080b0f0700d05211450401b400b0780c001107842001c550802180000d03c1d003403081454418800c80c602500c5000d04e500d00c080d0101c04c1e101d000740701800080d2800c107600b038078101c0c0040206014406001c020015059102c81a24001c1903591101d042010304d001c2405a08001041c0078200fa1100603035820041004040c60340318110501c56446015694034412030541c3c02d41e00c12420301c0001c48a85c07260220302d40101c0b201c007410504100000308610520321a001c81282c840542564103d8541d0144510300742c000c10050391480752080c041c10a0403c44015100c6024a000040440a0600825a82d06001c0da28240842580e900304403ca507200c0004000c107000800d0580d0000d0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 279025584 1250 279024334 279024353
    0xd090203011d062d06011713143c06011211030604020f040b01050c0114160503072312040606080d020a080702011b12050d06170706120603 61
    0x84000503551102c001c52509040c0740041c05010020741c0200404030155044c6441032015124030b0001411040391101c0004031455001200f109141c41d00361010b112103c040f08411460542c8600028452906c144500a03103c4581c60444103c010300016480c0c2c464203141d10b540c000150600c411441d00003040b80251514a0036000203104141e41a015414061104011010603008600510040c6000d5003c02c01c40144101024056529480741c074100ea8007071429500104848030080004100240607284d0321401624210020310300b961651180074840e004403131094125840f81080c16010510703003c0ca014485d0100700a000e41882a10100241282e4150155015600204046080446241c00e00c00151034000543d400705ca140d01c0010142000d4030321030740d0242040d0804003130070103e180c0d00400c0e0310b000820f8204032001109100c0d400c035000e0004034440c43e40030061552591040c2d1f02003031250306200195803080b00c040021510480700d8403d03d02e118038012504c5640da907200c1c0e424 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 279026834 1250 279025584 279025601
    0x203010807062d050a030216060b010806030601031e23011e020403050712141c020c15030610021009050309040c0305010b030103120525060c050309030f0d09020301 72
    0x8540106408000701a440030076840400c52aa040f14a1042e098001403108018681c8003002e2000c04640350f0b0006000342d043c3d411500c01d403401d06883c0d808910b0a440113052285500e80802c4600c0082a000d0400064140c180d0750300c6881c0e00d21151002001088c08403508000300e0300b01d01c8000c08121050084800c42804409076000402c1d1988071840250881d032500c1d2100c40a81c0c0305100030808070300e000070030900b03e07260440f28540051203820032145107400b001c405125803140594102c0030805404107003214800c10307400e4590600c03860b000c00c00d142ea410610b1200000062000c01c149182040d0841c08820040c0100c96044001c0003603242960f00400007544c050304040f80c150300908040c0036a803076002c800e14040020b1340c180b07914403031280810700028110260340e03c5c114a00c1c44c0140c040f06c6806004160342118440c0241c002e000e80d81036000200c40e0310382401c1d4491502c03030103201580d02851554000e5801e102055201003150780110440803200c5441c6e401d8040980ca0a04c140e940 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 279028084 1250 279026834 279026849
    0x60301020d093002030f090d050106080d090f030308060609010c0605130501060b030106020d050708070516170111030c0a170703090c170a200a0e191a1c0501020301 72
    0x1003003001d48454290a01c045054403414a10b2003e2103012070303000c81200c4500c0d034244032003030315844080040380803100403e60042c0150b282540c0841c0c8050b0000c2c3c00403103005c40b5603a40c012103403a40b03004242d0070b06520008010494020101e00315181c01d40240c072400310180741211001089031141001d03610150340707034641301220032004000d000c000c0c000c3e00060160320a03264990351409900a40d241360044480341080700204201041000c2801140d51031900700c42205e03074034810ba0009421a40c4144143c50b04243c03e081c01080901060050000140b031018003907081d961416031450700c540c4500c000030100115825070340103c2c00716248460081600d5a00040c1030300f024940180280c046800c560301c0350300850190580d40b10001070707a26030503502c0b01100c0300d81c48000c0d9924510100c2c901c0d007e070740200818000308210034100300c41c1e44680f0661040e0340d0940d52500c492021142e41c00d189014071022400202c0540c108850382c00444c140103551090520280c2d2030f11400ca1302700b80c02144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 279029334 1250 279028084 279028103
    0x30f14042001030905060105090c19050301154509090204050612100f1404031106010f03020108010510050903030c01060927060506031c0c020328030305060301020d09 73
    0x1030900100d100000741142820200004890303034450541d118014407580388980c1c040400543d41000402c185c4d007030742401c00c4070047ca104c000d07030300a0003c1e0001d00811591212041c3d41ca940b0234800c1b000d40040e90020001160816007150111000364403100180e801010180d00c0c00d80c515142004180040c8031043c80010307083c0c40381c410030003680c901806592086000e079580000c010300114403c5101c14035414001040440000003101804185481c480031080d41010081410b8000c0441c40c03030202008255166a07890713003203468114920b800b0181c00144058014421410014108a410b8045082c018201011400001d03d9a80035000c1d9a0181c1d46903d400c00c68034100d40151050703002070306c02240c6000160502c02d80f8444200c403000d45941e48613000304582d601c05211100001458000c80400d404103210f0190020b09201422400b0f4420f030303000d41c2a1103040e10484068848440701c02e004e903103580c2d10101c0c05003502031300c40d0394075560030404000e15005d5840b89a480c81d101d440c180 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 279030584 1250 279029334 279029363
    0x30902040b0306010303090b0c15090a0b090102030c0d0905010207080f040306060b030c03070f0e0303191403040c172d0606040519090f02030105071116050d03030f1404 74
    0x481914070340103034a8000d52007000107000003a040445071082d80d1050310b00c41e0720760503d605a2172030302201e60b61003584000641d0038070402c1d42c00414191140c07409100143c10710b8070340c501d08900700d00c021900365240d0b1105000c00c60004d00203410034502180900005410701358540c42c0d0040c40c0d404103500c1e11014400003810420000395006620081040c41051411450235181c50180783c80010b201d041040080030800a405009140c88169100081c04030307512003e945600035070012044007030801080e0350350340c40040480700d0303411240300701ea0080401d5201458000c158242101030700c40542a17007e0620b045c411010203ca61210b2561501c60140b92040050340c154100382e4041c042030301a40c01c00042145c0740c104007100d03a1203c54404c00010720500c1d5410180540e107d05030000b03500d03500f411b06224100e940030110280c0a801801500c034501541a1001d8508099108a540001e8000d44100200b406644048030280200c5400704544810169282011600304d80440d4202c0030107404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 279031834 1250 279030584 279030589
    0x40f0627050f010c050102190e120c0a030803091e01020a09050d03230409050f06030c0105070507090f02041d0702060a020c07140d08030103050d021c120c110706030902 74
    0x6480035015510a8540c4450802000c601d000c0000300c61907040c000f9548607002000800d504031030b111101040c412a100703a840100400600507259031a209a09080b0315904000d40420f40045400e4000e040c000414035540c0c2d02000390704020044c035100d000b861903103120900e600600ca03400c0c08607100011381c0d41c1c0065201070040403894120600a1141d141d5040c00250048240313458408204650314407254142008501803090b070308460545410b08080c04840d4a45481803401030200302c065400c0d00108000448240c054000c0180580d400301e503080013120680da12040940288076030141ca02a111348065100d048961aa84138004002c8204503905a0503c042070300704100001c203500d418107444000d5900d012034021a14102c00c440e480c603c2960740d45034010b8825500c088201d48030741e500d0034107035224250f18082a01500903900c1251042c26155030030210f0a8464488000c0300102c400301000400f01c40d4218820322180d2440254000300c100040d40080c40c01b513401040c000b07014410b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 279033084 1250 279031834 279031877
    0x60819050709050112060b0f0a140f04020f0708070203070f0303080702010506010504050a140a090504080a2601060c030e030616091d010b030a090804060809150f010b0708040f06 78
    0x2d00d071a8500401403044880c0d0384c1c2102126070b0071003408581e00704d14000040c0030030355030441113521000400c000111001c0601e00e040c840d4030200d42c1c0f000025545802c1c80306a10511126002c180c408001e9007001510210107050114000740c00c895200c0c3d22410707920b8400005400c1600420002410072601a50900440364030580c203103061410285018081490100b40e030060440c181c180034111010390711565100002050541d4050243e030900c0d0800703003038683c0300081e82000100700b41054032401e04a21402ca1000c4128201c040310f81e8a040b004461b0f450305c4001c00ca0820101d031540c1d1190740e90403c00240254500098103c0742d80d203090015208441e55401020b40c421160000140c601460403050f0440d01691300f400d0303584d9501c1c00c3d0000245a01e00c40205250750100340802c403940e008050b14441c2624904541e84800c20121700d4803c5070f070440340441e0001c03c0e50014040881c4000140107814804c07030328103051903110202e03988511035680298000400710040403046850489 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 279034334 1250 279033084 279033089
    0x40f020c160e0a1a04062405030103020105040e071106071d0109030b0c13120812010909050607140702031023091519020d0605040b1801031101030608190507 69
    0x8078400c449616004020310100030042002d240c0304c0e922440c149040040c404241c4600c540144100800c41e180c05044190860061400d00001402c811002e0680c1c0500c0071241600e80503101da07810300d07280014469007551300426081c01c000c000341e0a50b211060810229000d41c8a40d10f03550f07070075184404a2000704090480450400040f803d007000070514004016400505100c032940d40c0e00300d100317200740ca0020180c2c082c24040d11009800010300c80c10201801142c02880500b14490341d882061405917820010060929000b54000ca0300c0d80380120040140c11034020026800c200c0d02e500001e042c1201c80804007950b42d01c0c0d6020006543c074800e0100c2120060801030b003070605102e9103d40e5681b121a00c848075049181c00801c0b04e407109040d4800142d540740381d0030b550b07402028045030040d1005229282c0698100f44a032182031a08034003116054000e00c4400c07117a41c3c070710388840418210a07103c0b58145a41d610f0042030340001880381a203409411a21107000000500e0302524015055 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 279035584 1250 279034334 279034363
    0x114040606080411010e120a0506280f0b0402070503041502011b181503021308070506090108040813030c21020108011502010f0f0b0315040c05060315040f020c 70
    0x352051003120303007000c115500650001c801d000b0700f00308000141c0f110310398405002d61103455448030f800b4000c00001c80301c40c0507210b40305699075030711402004400451450101440c035549080d509110803450ba10403002d041a1100100d04d918148010078101e0744500e90988003508002400d000784109107407058518001c0388001c000f9114240da1013415108900040b004100f50490604444030f4880d6890300504a4451121201c40c0c804c036000e0001c2d4003a41e00744013800d840540014921001040210445402030308062500c241d01c0011692800010411100035005000c55102c007402c0c03400c464007451140400c07881e1b05e800d02d03d00000e0701c00c8a401080c0c030745042005000050340d11418141c11a03030300b00c0741c103c64107450304416405840d031401d0405402e440c0400112000351b640c0c1018860250036015110071111954007000c11200c01c480107004a550000104140e040190085501080701c043d60341001554000040540c0c0858000700c0c181034000c102e4500400092200221000c2103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 279036834 1250 279035584 279035591
    0x90a020604031b270b030c031209010915020109021503060d30030b0f0402040f050f060c01060303050405010305010e0f0105370f08031c151508011404 66
    0x650006865206500000f480204100480d00490f54080c01d00382c041e0842096a0648030781c641c0050f520100e1203002c05440c54140554600c0e01c3c1008a00c001c500d120203400b425904140d80c0d00041c1a0740060001743c1004424040002e12140e2070380086240010b40c2c0c00803d10f000c0300c0c01000001001008000c2c4008030400500040c0d0b1341d42e4482d408a2640320507800d4800364a5080060b040480d0f80c4441c1281081c110100e07495a0f26a100001c4050101d40b0f07401c0e42a4000d060104034001c0d402007041207100500c051000d850070b62203542590100412342d51070400c101e400342e030a40302e11703901c12004a100420144a150b0700342c0a03003030140403003411000d00c520313118030824080d40041c8031301750250035200e50081d2010031900f580041600b00c0404004a445140600100c040161141000700350141c1d102080380d22022080325084101035507088040d1804d00024402004103c0c2c0091800c8000300000401c0c400786400c0301003a000740d0b141c0513110340c504010f041d50011108400d41c8601c0c0b9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 279038084 1250 279036834 279036853
    0x234080f1e0304030b370e03120105190f03060e10020f0306360103060507020606211014100f0b0403080d090b09030c0d080105061b010b04020c010608010509 69
    0x40001920f0440c1d42055985c0700644601e142d11070b4030540d0781101500c001485444d01d103000740241e0310280200c0000c90801c20415501002a224016440c0c0c003101d22110703070010480c915005985414202c88182400c4c0705039a140f06140070f481850380105c0d50152a40b82c1c00007158030034400203404d0030210038150702d004d400e004011040d21000300007a20441e042981aa00c0d0300520b95200c0700c001c0081e000501503022520810b0382c0160901c400c0310041c0c01d100010340034505c0860040c2c01040c001d00003d00c02c00000d0300d801e0390901d1500c0540068883c074601c00004421f80c0c043c13a14098003044503150181000b0360800221041d0b500043c00c81c1201d081c040180f4808041180c08803500900f070551200c40384800781c4042c02c00781030003504c61041312003400040d1170007100511039000700e0000c64160300f0b02e441c42601d019200340700d210381c80711003440030310b0645407070a907000003900c3c0c488000110036a134100000c049800001102c80945e5643c40c040c00074078024401c80d5080f100300b2005240303041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 279039334 1250 279038084 279038143
    0xf030f071407080106060507060609180201050a1101050f0f0a11160219081f060806010605160605090c0a0603060509010614040e01120b060409030234080f 68
    0x840d000c4020440c4000c80140ca00460003480300d240034005800007802a00e58440e40144640c0140320240da1440c506000010f00c0521446403844844601003501420503544d001903905810400c0d00c031080c001074500381c00c503041080c481c1c40e21071604140c1c0b900e03103030429101c2e4891050000301366240103403808850800110418081d00c84190821b0301a0950780040d1000c51510030441c40d040c12f8401400c1c90100d8210004150103d21360055000c0c05081e00540140ea003e890352840b40e03a000f500480014400244114000c05001c03103040c00902281e04a50b070b0320b8089901c116494103144d08580005001481c05403091001400c070b07490184013a40c00e04001550303040042c4150014850785400030040404140181c034014070064010b134000303680d60740344c0032030018042204072103a030300c01400141945480c0c800c200b1250b41581c02000307070381d64010504c0a03000c4c000b1418806485655615054003421b04405006018101c0182000b03445040780d540c0741030059011840c808062800002c4500c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 279040584 1250 279039334 279039337
    0x40b0c09010804240f06150216050603100506130602010c11060f071e0c02010201180b0f040203010b04020f0d1d0a031404050603010902090f030304061205040203031b0703050f030f 79
    0x1500911115190501842080740c00342d10507030584d118504004c444d26a0700015404042201d251504c1c03800d070140b4042c0c04071703180d00c5242d181c8000142580710900280c00e1280103142c0c44100801010b0341c9030b8841c00082c115800c045448000d800400009000746542030003500c903154494104146025600341205840b154020501901c02c030705800040c0400b407180500580b6a000700303060b065051900d84005000468850040e0301541c00d00b9416421a402440c6142c502d5030401080c09080d1500071040840c0c81015100381da043d074072250202c2040e0340320310042c00b40582400d0fa031a80e50790341004040988444070342444004803c01d0852919100c0441c5015800d03505140070078032900b2a00c0c0f2004a402550400c2c1e400440220022500c502c0380d5000f030241c80e104130351580d82446200b082603602d228a001d00c5001070500031031252155946e030000d50f0414401821340e0b081c030440e0300305841250f0f503480700c20a0383d5020050410500105020280c4581d0680005c4c41c640140b00c0841a00d0303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 279041834 1250 279040584 279040591
    0x100921090810180b0f07080c03010f0501050c0f2d01061a0307090321020f06160f020a0f0305040e070302030c090f04231503060103020a05060a020321040b0c090108 72
    0x1d585403c5280c1010183c1480c03094010752018510070107041c6843d48086403402183c0b0440441c414001007a8002085d000b500e0485060a40003214a424500111120782019854181900c98070480890307140041c000303980c0a10008400310f012905902001101c5504500c00301801d03490000280545064100c0280300001c0d61075520396241c6507580200d03001d810680c0003034040341403140341601c0036203140c440c0c0e188800181d08950452034406400ba44030201612260a643d42424044045038040c40c410075600d00c060050700d50300522904d80d446410910041100000c40c006024040c42c40d0364101c080d041055442d085045281104404659110790340c82540b2400003214017500d1641e503030b002076192800002e000f01c41e40c1408415240a150140c03035200d19500d0361442103400c1d04000401c01e0489400804003200c01d031078107080c07041c83c2c0d02030382c0c5981c11400200600482d40d12010214524101c410003131303282c64074041c00d041d03140d000b01034580143e050040122207002e0ba44412110341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 279043084 1250 279041834 279041863
    0x9010902030c070501020304060c03050a150302150c01060f0620060a110403050a050607030b010c020f240301080c0f0d080d0f0e19050c19060e01021009210908 70
    0xd50ba11168120340c0b0501401c0d50007842e641c000401c0104101c03841e000503540c5042510188001e403a5100250107840380f203074111710285403102003000580385c8140b0324038410710700107800d41c5001620500c40c1c0c291580c50b00600031607030f4504010003000358440c200e074140701c0d011000f50241c40700d1070406a440c0c11015001c0b04038213171251801d0450714040070485005680c00000c80310403400b503141c070b50746814040741c07650046454001072404e154007500140b440d481d07008091600040743c40c030800c403002082d01c1c0e079030028a085040f0503c515120740025406802e842c402000034040080402922b42e50703409a180c000c0b00c0c082da0343c0001132100c005541315483d0381c290210f9a0030307108007604001c02911101e2080c0f8410071904090191811b8801c00845000d03000762020b44040300c0920451032049001010a07648001042100c28402d4101c1d42c41c1140500c151140c280d1210b11603406d80b10320303200540b61125224905242e140349041c06070140e503030600b410560140344c1160030b5141c4110f54110344 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 279044334 1250 279043084 279043087
    0x20d0c030201061502100506060c030702130e0f060109051b04150c050d0512090708151308190305070e1f02100f05040203100b0303072d08032409010902 67
    0xc060003900030b40042c1400c1c0340910000359010400039654104031aa02d40031074a040007281c007a00381001150030740d04900d07000314901111381d42442001414003a0000001d9520f6000013a000d00a200c0c1a030648001002400c4079414260031904650010705820803005003600d00300107c2207130744142c0c0c0860701d49580d580d5001e064841c05554161a280c0e0003410341c051168103801c265041409404540d00390180081d9a07a030381d0b05842c3c0e4600f568080c040c2c0a511040701c660001d11902c2620303500c01c4207194a040c4201007941d0300c070040d03080f10103503c00c882110300350782051030327410301c501c2d0792041d80d500e0f10b0107290703040c600405c01807440c00b50741803454078207582941c0d8100e000304130004030103080e400200040d1b0a86585900103040c10f5400303e11902031401001c0009071680612400d0050082c040c0d03103003103142da680e01084181c4640759030748a5000c1980210b291401001040c2007409415026682c1c540290443c0748075001182040f40a51420b5a00000c0c0c0c45044805040d10b80144006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 279045584 1250 279044334 279044357
    0xa1101090c1520160e150405100e01090c170f011e080703060213120c15030e06040308010501110a08030a020a0201110f07060c0c11010c230610090606020d 68
    0x480d0820000072006071610f0000c2e9102c40c48500014140792001481e604c540b8000362581030000c1c0d855403d40f2030000c4440d00d40c103840424509540310503042048840071443c0c8a9841103002813401c4240e001c03046482e07980582c0c1051541050140403000355620544043c0c0c0b40c610f100040011040c00342a40030070001c8800c400c0090a00480d4014207802c40440b0007003a501e04d801c00280d84401090f50f262101002c3c0003a4011188231b410340340d20790214a4580007814002e014400000c060000800c05072140b4112a4008050241c03d020b6030082d940d031100c030340c10007002520358214000341401e503501980310b420102d144c840c2566040030300aa00580e82e0303403140408a002d801d103000e424020303c00004058400c0c812001c02042c0c0d5520689044c014181010000c0d42c440d040000050142d01d200c000c4520380e0342c415085012924840c031820411130307012810b0041402011081c0040650202e028460101e00005010005020118080c0b140310700300300001b5101c841817181c500a000c03c82516 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 279046834 1250 279045584 279045587
    0x9150507140304051507121701060e030c0a030b060a0506160312090812070e030607300608010b1503060102150c090904210f020606011815050a1101090c15 68
    0x101c03001001e0040c54210464000f005c140308560208008440070300d0401480e58041e4001d0542081700c10004108418980c81c0039025030300b0041c0e000b180c3d540b50084025948080d070310f10340a4005140030b0a5040081c0c0b0b840c8e01400a400025040184940000c0c072000842c01d9292400d01c1415501d0318250110703001d46e020f0f0b4009800540e10040a11902094040d15410582c9140d0f1054800e5500d01842050b200103140c3c4608017610719800140300c40d081200540b400e031440d004111010250540501c071391f00a46000c6403c103800c0500541d468091840305403500460301000300e401141c43c0341c5503092000020303664001d04a0820a4001201c000030041010007043d0307a4101030181c096105407070546420b103150f90003402d0707080b80300308801b001250170303403103509640800c900701c0e00200320316115000103644c200302a0a8501a0b4940b10b14041149400e51600712a04c00c0c030b0f40c0382d094694403050009040c21484001212580e0324201103100426802c0c940b54080301c240c0b1103408925090403d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 279048084 1250 279046834 279046837
    0x40f020408030304080a0801090515100e100504060e01090f030b18010f02070c2715091118090c180609100c030e04020a3903050703091505071403 64
    0x2640300d0b0001004100500140c40e00034090b184070b81e82c4610445c2e0301c0300d400800719070069030300c034402c41d11040030203030745051260414136404c0660038024804c91030400050200b07400c588070400041d00101d4100001d54102d4800c10041400342401c2d50742c3c0b41030105407800301c1e115210140500e0100c0300450b0104050400c86a42c2c16407490084c0511502c05040a01a50006a0460b00c071900c02400080c1c44002d81c044042d580c164407586003105d005041907601a1940500c04607401e003d001d400540c41c1010703c1013400303440c50361b0308a039166200d0011102080d10300b510752500420481041044045080c41201e400d22041c3d8800310f21102e1000c0030821030300039040c2158204135007000c80c00b04c145c0c00455010360580309503241560008e12005120a90050b0380d064004540d42090119190030b00588450428140c0e001460b0200c1c4142280000d1414059080e400720b0800500302061641c44260040500301d07003070ba83c08118505142c010041d20903078401a1170150494504181c1210600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 279049334 1250 279048084 279048089
    0xc050315060f0f090f100203031f0503070303030e01050a020301030c150c0b0a0506091605040608040f0803010303051209030403020a0b130503010606020c040b0f01020606090403030905160617060f040f0204 90
    0xb142900c43c075070b4400405059002c000c01c4c502c03400e0384d003a440607a450000c00750f403100640e99010710705584640003030000109903040d030000a61f280c60070200b401d49003005030b800214020f960100c2c0c2c10f941000514210f640c060001003a03070f40100014408100ba4108840481c6d08d1102c0c512034000040310226a00c10146000030100c154941c180010815282c004501812b400c0307414075401d40340e16000c640022050502600801c0b010f10040040c0380c0220101381c0d209011b130701070026110341a80c847c0e55580c400d0b001100440c10109c1c0082c4207840e99104107920200c41001540b8140c259000900d80704854402c070040300c41c0000d541d503c0705100119200c018403029000b401500e45903400030791079000504034940110324100200100340303854090045020700680203443e45031603240910802d080002c105030141900e8081d41800520100050805d05c0103558125000c3c0c1c1c100100203180310070400100c9500c841c004107104496840c140c06801403001184c0018411944040b810b000e406180d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 279050584 1250 279049334 279049357
    0x1204230a2a1a0c010501150e010201060326090d0c0807060c0c1701020702100905040b0901030c030201030e0319030510060309030215071107120b0f0903040306090c0e070c030f030c05031506 83
    0x320480014107587d00142c082e11460a00c80100004900701d4003a40720245c1451701040c104e111013868842035003020b20030380f4104c070300d030021640c00301d081110182002c03142d41021070130411000009010781000341156203030003c0340a010380c40d1262079100720300a07012840070201c40e034159403109504940843c1e901510a5840d00d10f03800000e000d86425108490240f030910070151101e10b4020541c0307044c0c0364803500c0c60b1011829034004500405416110000b40d11040240c0444403c0d030a0258403e000540e6002c00c003031801280b21107642d0441e9002000341400e102c06080040e030080790400703d24504950862403a5030b400c0c01160714009a2894540b20701030721501064a240186001e20381034001d1403822642d45a4120350b500c08681194030842640007408140000780d800d4200f0b00c14035007c2d030300000400c6e483c0d03441c0c030101c1c070303003c0d035120021400e694459010180c201c00c0001c002102c40c01e04020a252030903018280707200040c0000002c9c8408290510f503540c43c0c6003070340d2018031031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 279051834 1250 279050584 279050591
    0x50a060e0910081f0c02070810180b0103060209041a0102061b090a06050310050303190c0c0e07020d02011413110d0501050702070611010b061204230a2a1a0c01 70
    0x41013581a60301001044d42160b42417007610a41140000b4881007222461750081608450f074441d088020010b44501008511004c04400003140018502501031170040b17400590745e020341020403045859851100c034406010719403401b88c07a0b0300452402d03031200c41c24903c80710741400650091034620a60030882e42c4000341110200d465684140650712034921105040740b495103800401d07599000e01c5040041d0340c140a10024642441880c07a65607852040180c07201d181d48440c254012030720102c501a00507804004440b00465090058001c2c1c07008156680701d80f030a0161603008420200c0c4005049003600300c0000f2440d440e01090f12107080d400c44c000300940e003803581c8000d4840d4054428100001e1000554008620040c410201456030092400d40342491182221941110041040e45c011007000b80d003441460b2144d1180c41103440181c080e2500c10342500c1c0450110040c00800210399071a100c1501556000e003d502c4290349401071450407040ea001000e00c1e4034403031036200b003980f07500303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 279053084 1250 279051834 279051853
    0x7021b1306150203040f081c0f030f0f1b030e12070213090f0c0e010e070309030309060c0201020405011709030313050a24060e060d17070803040b040c050a060e091008 73
    0x14044060020f64040c4200300341c0c055a1f99503641c0d51102c0c411101d03400c884080203107d80a900446071561180d080f410701081502280c4810790490b01c405803c4080381307844084003441c0402d2200301c585071103428101000032604280d0000d81c3c415000401210144000441000f50350b20200039010280c0040f8040c044200030740723064007001030224000c4600d001520340106003000340c008403505940502560442e90781d01c10b4001c8001e80724091041d02030681d20074492011409902600b201d00c1e60a80003d40e881c0c3c50900010301c499490740c1211250101c00c4240800b5020101c101c83d089070080031014174010103410828201000030b80002c0200c0b46510900305c0e020b042d07264407104a0001002081001d41d1030511001150701103c940b070340211581c4005000414041840106400c003140403820425181d981039860390080d1000d95200c02460100400c120f550030fa9030000e07180c00e6034031480c0b0380c1c84c0170380240440800c0d40419110b51070030b100080b0800343c010059001404503030119111b20342d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 279054334 1250 279053084 279053087
    0xb06041403070e070f14071209080610050a030b0612030c0d030b01051204030818030a05030117030702090411030321060108091b0409050c1f020607021b130615 70
    0x145045a00c50107030203200000104103d5a40041d84107075465290701c0c1001c260030000b191401c280c81d5407101800790a000000214500c0c0e102d418001c000c545480780e00a00f4406c000d40703410002082ca680340c9580560074001500d5500030319040365404401410180c65000004000032035282403e405844007203202c41c40c5100024003c0080303c400e8400300701c080c1500303004684d03900c1505c98049100b0917020200b00000c6c413442545038170030b185000402c0c00c003021200040c2036600010324440050804001800352664000f02200320b02e180100842c80d0000b50b9000c07451101c0010000341080d5403004021007192000c0c001c4072802c040000c003403284000d401088502c1240d05881e050f001031403420018202010015020800c203c0c02241c80d00c5682604c42000080c110203001182e203800b800a000f6800c1d1140c1c001d0ba800381c0d418030a1600c03d918025002883e01034010107400440d44074880c51262074a2a808649a40100307031298801c0c0c0003513880210180c6001e0b400340c0013004a03240c0c2c011080c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 279055584 1250 279054334 279054359
    0xc0a03050a09050a032102161d0f090607050c01022101061d0f0607020a090507020a053a050c0a06020d1805030d0509070e09150622050a0b0604 63
    0xc1c94107454110010b500c450038070400c400701e0301008050000d5550744201800c89500c0f8544030342100d10448120b2281042520503500307407644480c507004c429101550b81c0d0b1401c54490341e802501c810450140e0b2410503481c42d59060054080c40c140240001d82130007400d82901240c086d40102c0e03076020345040102512000b212002d11480000a60900c41c08079101c0b800e540c610180c000084c12503002e02e9010003042400e40c00810100d0b404401100c00090700d204600401c0d125103035a802804920b1a9824080d04010b0801700c0c5242c4200302510340480d109081d4402000038092098120300811402c80c10346003445550a5103610f441a0043d00b0700704101500108400317160b440c000c0c454512054000b2006802101c001081904140580c42c4101200c0d44082c1c0d108a0030345c01c68211640d144031a400f4400c2c01d4a00c1c1c0c940342c001540d108110020b00f2407a071b401c004160343d131241c0a4071210080c80c54002900050361110b80315030200c2e40310505504440105d005c003c019036a555560034901c03005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 279056834 1250 279055584 279055597
    0x20607030f0209030a0312090209040605040b06100c080319140115020111040302190e04030302130614030711010e031803070f060801030803190c03050601080f24060c0a0305 76
    0x2070300300400071110066500903600514000b030b000b081c01343d480c0d0350103950303002003070811580c140c0d80c0303161610140c0e54030420140240e018420000d00da0506007443c00503d00001c002e90f0160610711910102c01d42c1c815501c00031503401c2005203407241c880d0540c001c01e0204030315018100d03a08050704407030002e16180b4194121204001140c3d08580000c8007030742038400c0c040c00c05c000b0100a11017000035042c0030082481d5040c41458641429480f0311400380b43c100705490660000e0783c049400001000440800c00240509082255071007444495013040c82c80001c1500003080074101d0b50701c100071000d40042601c250890296600e0b401800032148101c1c0c080c2506a110340310710400080c0007118408120b0980b82c2c265500c45e81d985c21900c1d0b40001d54400707810703034003c441418030b1080d010355207101d404180c044031354001ca1a801d0001c0010804000a00510340724185007050043d018564104051420311030310141034400f44400c002880c600031568003841c54091820a00101580308009081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 279058084 1250 279056834 279056837
    0x5220917041d061504060e0f030f0a03080901050c07140a0203061503120f0f07050309030601090905060f060319030c0803010b03100801060339030503030105030f01020f0a03050601050c0d020607 85
    0x420703035615010011842d000d9250103134100810082403042510903000c500c800100a04058040c80781000800d00c0c0c41103181c00c01155802c50712402c420150f02c20300281c1c000c50510028042828010302c1d03c6c07814400c448000307200c003125809100c4140c0d01405640f90344c41d0000d09680d802d01c0e003400b5980102c24402c4002c0e10074002c4019144070008000156064550758a900742d00f060010395001d50180c0c0050425511488240030b00c001a0740c003048a00e000e00700010002c40d40c50740c0e52030a245014406010b00c628214450200000e43e14005600e080000d11040e074904119803609040d1039240c0e841034040d180ea0000030010458048020046001c1c0007250140841c0954a032025401c9034014003006240e11001d00120640d0068680c0c400700701e01c6003020070205401414084120064141c0c011a0a6040440100010302c0c050014240500740c0000079460441070056480a51051502140074550fa440204089902c2801520a5601d84004aa202c079036201e2010b9641c0104848080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 279059334 1250 279058084 279058139
    0x1103060109020a1701291e04030c140f0112020d051303020d08090a20120703120f080115030204031a040b1302011d010e03030d0501050a0522091704 65
    0x240c0242600c5540c42c102c0e01040310405001503031040c10881e04440d810741e1212000140000c1e114a0748540487d00101c004040c015951071443ca46501458583d5101610fa82c01c2d040c0c101c012920340342c01c20125408246080268801e5894016009000303600291942c6442d19080144440c01040f03100d060a000303801721442c400300311404607080c0c1021070b0683d846801c20000800020030610209260610703522a80c01000304071804103c44200c010060701c025800007408100303000003c480400c0c80301c4503103410b1050b046130040207080440e0601c10112480c80b102c60b4003041a10950680303020359800725040c00c1080c00709881802622043d0303001c0da07a1544500104031841201042004802c0c5d06071162000181c28880252199005418280c1030001841c000300d40c6607001c1c03006000c11174058000150a504107014402651300704d81125001d400310315074240c074255030560307000980500b903113020641e04414580402d8039082060102d07a400070100e408201001c00c00c4015011060184286 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 279060584 1250 279059334 279059357
    0x1005090103030212070203031204050a0210020607092102060f040e0a02041203030203060a0b0a0c03081b04030803090703060914100b0109060f0512040b100f08191103060109020a 78
    0x61481420720005015900010f4841c000144190140074514001000c0d2070600c007001e0700d0780c007941404403011503c0d5089403822100318038124207000c081102602c001d1425140c8480c000d0000c1c000c50041c2c081501d40e50481c09268440b021030714001c00d0f0301406503a150280082002003940260180a100c4413038400002e60100e018403d80d41120000c1c41d0440c207050b0581c81c2a4002d40c00600401d4002100f5440403940060501c018681d41445558240e0101440c0c24010600f00c4003800c0740e02c0c00c90a0210002212540c0c0041d03500303994108070060f82e0f989a1401c0c4600d40401540001d01560030070420106100d201580c4090320b0503e0b10907a4043c3d20f00200d064200c401c1c80103050701190744190700b401382d02d100300d00c01d4007440b02c45d0070700919148070041c034031031540c0c0110ba085410721102c1c410024101820b40c001c40042a4092542d0400e90410f10f2507034a441c3d407003001d0074550365404e01000c02c1c0402112440b1458101809552180d61100200c8010707502000fa1080481c1460f0400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 279061834 1250 279060584 279060589
    0x118030906030506030a0204020309031317010f060503062d130b0601020c130b03010603061e0e03030108031c021c05010e0105010e0a0e0c070b1006080f01030b0f040501060f0306051005 81
    0xb618804c010007030192054250740d070700704030080d080070340948150b12090200c0001c044c1c0104065018203c4110718503014445641e01d04e0a4401d00c0541c00d030018180700e0304100c00e072400030b1000d400403180d40000380b10307200c40c601110000142e8403960700520601803e0040d82c0c103600036803111032030082c0310700f0102c0d640f45001039a0310480c49038201c0c1c0010300f4040f401d0b030103045d076401005c10141c01000415041d40e25141c0f441540c24283c10b140800c0c00d0045a002a601103200b8104030b10290b602660441d803600d18410b0f00d0b401050003000c4a900f05002c1c1740b0008426504a6110510700b4501203503440e080e50641c8020329090085091506170b01001248660088081c3c80c81d00c10b005001c014404d081070711191007120003508143c034844082c0103e000140c4c0c1d12032114400d080c50b480c03100003a8640100148000c05c090141400e4500c407400501c0816500d001640c0d10510301d51131544907031128a0b149004010583c4000014034512102004004441e0040c0313012b5178902403944841c07901c4904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 279063084 1250 279061834 279061841
    0x30f020714090403120b10080a060602120f090406050604230f0a17070e011e0b030f06010c0302070305030f090909010b0303030103170c011b02061f06110f011803090603 74
    0x7000c1d0b0303200007800d00040c0041d2194040c5815865401008581501c220300424841c0068000030004181c18504000c21542140f042900500d0248028150100180d07040e140c0d61060b42607981c501d102c00210502070380c8031500960000d0802416860385c42d950740040304660100a101c489a42c051840040d01a02d00f240b041002540010040d00843d45000d002c811202481c0705803483c24050204c0025000c0b2981002d00d0080145c03000c048500703c15072803401c074954139940100013015814402e10110128040304558807500038240030391000d0b21810141c3c83c144e01e80d40018000c4c0703c0003401c0c0185c0c3c904c0c00086d280400301607a031410644c90b40352005098456410881d9010f5100303000410104184040750949400b44001c464a0011b05003a100c2c25120303107800d007801c0741421244900c0119410400b040d802004a903403c80804081202300702550302c2e0344186c05c1001802c032050402001e0601040340b410b14090000c0101121400c00a08007a030b0f1718006a000c10109000090494000d02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 279064334 1250 279063084 279063119
    0x30915070e120111070c03210509040b032104080c01020c0607240e012007050601060e04152309040507060f05040312030906061403070b25030f0207 65
    0x71102010a01d40741c0c1403260201d031807091264259290002406500c4d80b0b04014034001b4090410030b20364a0443c1030050180b28104441e0a8041c10f00c8101209143c0c00425550108000c68000c100401c1400c0081d19205202e0113070341c041520b1800c50b404ca641148001d0081303514400694030010a1240160f89802c032007144241c11820030060f1000051b00c0c040e0111110640c60200c1008502d58200740c0100c4028100801071a9555241c0710b6105100c4020000b9921000ea01140f4080540d502c2a031900c030306100340d01c1400f80a45460801e90790360b40040c1c1d1210402408803004640e5020100b1689404c00b001040c0b81c1210079241c140c81c1440f41040384600d4004c8010450245094812110440d0a050341c408000d001d02000c80001c481100150800e0016900420500e045082030401c5407a182e01c044080c008544402c41300340c401041c90030450f144078400580f505c800322115a040e00d040c1d41513032044a40903440c1410035410010000c2c4408441d42180c0000361101c0300c400c3c2e11240300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 279065584 1250 279064334 279064337
    0xf0b0d050a02090601020109080307030903020615031009061e1e02030f01031e0b0f0609010602030c07050f0a0801180311060403091202130204060f0e06040302090609130c0b03091507 80
    0x6101e2101500700240305940100041c8000204030340320307403034444003900140c402900003500c49507907030141541000100c1e003011349403c003c4565034482c0c0c0000c1c0d4072094002000000e5884007003903c188071156015624120b43c0002d4081c1c59000d52000078001c000d845040340340000040c4410210b20b9162007541e21038140b074003182116900395180d15002c80317419a041041d0305101040400090082126980110380b9610303070344d286041c0301c0200500c2400503004102103500900c5005959000005d6003012103c06640010310f00c041c10700070a59105041d0041d030b82641c00c000700e0300190780901320b219401e2406966000340d070b903c0d9642450f0710f921007501c0c00350000301042000c0c8000500203406100309032005088400c000b2141140c0300517600194404e501080303070f0808440301380b03030061000c014643c42204ca03a80b90900f59800911040c1c800340007940602c0c01003000a150039042c503998940603400400442d1400e6036039861240c1c55108480d20f807194001e4000ac88a136241059440307000d151107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 279066834 1250 279065584 279065593
    0x10209090109141807091d1903090b0a0309060905060906241e0405010626010e0f180604050d090e061008270307061103070503070f031407030f0b0d05 66
    0x1820000440c86544002d083d0850080100000f03e032101c600c07c00d1a080744902c4014031851485800c5414526640c08200010000c81c10500000f540881c1034002d843d00d1002850320b984000004800a141a50b40144814038144080c01889000075541d80720745407200c100e84c01a5140307080c0c04001491004103034040d04e0480d0342c0b9480c0e4500721881200b00c000254400c0c801000807000582030302d50a82c8180c3c0400d8042c91090503120b106600c100450480000e02081540f4221030080c1c1d0f400000e0581c50954444008280d907101169000c00001c441078049525a084c54101292504180700e21a030200c0c11050300017943c00c2400443d94400e100040480503200425101030b621054010040c441d0440c00f92102c044040c402c0c2c4d0002140403d030b100541c0c4403191807402c4421500392080881c0700c44014020456401d40c0103003113a900402038540090715120904095000c1c2021400904c2d0f140052810014000d034942e1120481d17606075038090000825060030700494514648011300240c22 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 279068084 1250 279066834 279066841
    0x50d0906020c040902040212040f02040b0609010c0204050705130f09150303020606041d100504050c0102060105030d11101a0f0a0b040b0c0f060103081207031103042603010801020909010914 83
    0x20144c4c0b0505109001400240c07506102c01200c0440b201d007114100c510741075100c0304002790f080611078594210003d440d5241f500809a0010b401d5148071035000384219101d10002d00154030810945000c6110304603200401600d80356001c5020b4014002ca400082c03810b01c800301c800c44000007030340840381c050b006440140c944030244005043c02c051005005010362400c00c3c481c0d2000c000c4051f40d5082080c0010381410b00740344c014100810090440d04560019005220566000c03c1602d04500725081511036010046515403d01c00e00320300000206150400620514021420082a12900b242e65006000201d0300304211a6403600800404600030b01090101210b194000d2400d011684200c988402800e4942840c1190981044801000c00304040078060f158a03007064004003a03080500038500c8108040859000061002d40750034055051000c1c15403244011a11080c2c882180c0e40c2e6035a140c8030454080d6005c90096405112604000030b080c409620038419844000e00b42e02c003164a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 279069334 1250 279068084 279068089
    0x6070c080c01110a020114010b030f450d02060103170c0102070606090b09090d020a1e0b01030308160509090a020a1101151d060f01050d060803070b04050d0906020c 72
    0x401c200464002596a01c503641d50103d51100540711140c540c1d0f0000c200c1c0ca00d84d08080840da041a884151100801e01c00e00c1801c62070505072030b600c00040710f00b000c40d0480200c1d00104071440290300c0010101d103c081e00c890552083d0803a45000054421507682c051040703400c03650382c1d409100240c00c00c1e40c000b03440c08041582c00f0092580b9842c3c0f50016007450f4090700c0c0c0c05c0803501c8503400010410b070351f522503206e00e040900c10507500ca050103010305450800c2c824040c0d10b0f1000280300900343d02090107404070600300b201c104400c0c0c0e40c00c0080e5061968491501034500d4034240c0e400ca011042107110a10202d04c20411207200050181c00c422140e140d0903146c0c000ba402a01031001440385014100310000c1c0244203400c8480f007550f02d042d94480c50300100304158000101d0785101102c0c16820001d0b00d8940d05d4904c51103000a180c142d82e10004501044002d1500d030b0403404050100140c00c0050001e043d0045000d0381c0280c098484022580d5015524000d90340706100158003c840e4044152 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 279070584 1250 279069334 279069337
    0x6020c010f110f0f01140115091401030e0d090819200d050d020a1b062c04090303020d0b01090602100e010b100c03020106052211040905131406070c08 66
    0x298000e0071103003d09010f008050a14001d2000982c3c0c0c0c0c1e54400100c0028481ca510303040c018500d13508680c841b01100180103201c0c602a020b501d042c41506c44803500e240e486644191074100640094420380d210451008003032012b18406c1030400e10500b0f24141c0001e21251f0507074590b55020507019000203d17064041822603190a03120b82c0000a429140c02190b002d00c4202824074082c1c5c060400e0180303e00e00030309800588040e079110b0202c540024407800c4e4000b1024454558042d000c841e26841020b10840710ac2c0740400b6113a0043e0a0801c5003081542580203080403101c2c19405111300700301c4a0044500024502c03840d401607024510709010b100282d407114060301d0140340041020502c040c08212581040d424580c00600c40817240410b056083c803402000e0003084a459115245a0480c0c43c1440d40c1c05c031001a02c199203854814413200120200c03070041c5000a410720003072508a041400d024444201070380d500600344400a0440382c04034080e0b00c01d406613200c11420360304644075202d0740d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 279071834 1250 279070584 279070607
    0x1b020f030c030d08160206010e070c0501110a05120105030a020a030f050c1f080916060509120a11150306090c09041e15120c0b0c0a0f0c05090106020c010f 68
    0x1809802001c45158900b0301c050604810141c80b40d4000d03040881c203141024030648100000c640000d070052060340c002da06100d820030001e01c3c246d080d1b0b021504140d1b004110b00440c0080002000400b040d281d034000010b8010441c0002000c03000d07a90b41d101b03041d103402a6000007075010454a0041c40040c01310a000e6620600232422110004048800b2819a01d020742d1012510108100701c18801c940c82600705510030400805450302c03200e10790a40300c0070380440c0651b1003400004502c0000700e846070380e2400005141c0e8030071903c24081d5420058816000404010301441c00c0c80740b03400c0c0941900f02240c4c06170320040c2c01e107503d076a111003081000780c00035021180c0c05511101085c110b072032040c480e04c00d103410b0388000090300e186041d52284c1f0004640e01400c0010308407600070001c190f01d070030300004545378040c1d004d5840f078440c82140c1c00e004420a0042c082440ca181480500c22038006400036a0010345101c071007030340ca0300000e995420390441603e0001e411318152075045032103900381e13803072 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 279073084 1250 279071834 279071839
    0x170c040908071b080312150f010903020111030706050109091b06050a0c0c09020a080a0c020a2a0e1f0506030112120306080a0f020f0d170a020304030c0e15011b020f 72
    0xa205480d00c03885401d51b4000c441a1821449036010b202d00c101200100c904828021940d4113007502e00c600003e01004102d10000c0c1c140480381c032940c8140300301070003110350541d0300c020100125a1030302000720042140120644000300c20144450602c2c1da90003007041510465154141005400c2004489401b0919000c4800039807120001441e100396002824801c25a500c07205501d24004c2000011034000c0c071550f0741107510410825010030003258110f404698012201e80c1c0500c4414428080105a90302010200c1f030300c94108088075042c41903048880111288101d40b2941c0c600801246010038025982e005555008107000560521610410359141d4240400c02981c0c80c1c441d0b6042440520068854075010f180030000c528200c1100d81224204640d544250041516480000d940c030154452071804005495000680200203071030046a000b80c1503084075403112007200a808050f1000345581c9540b2402d444039600645024900401e201400010403d9a03000c00440340c00400d103454 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 279074334 1250 279073084 279073133
    0x12040e09070902120619152607050d051e06010e030c060a0905090f07020307021216060f020f010506130c0c0803011502190312050903090a170c04090807 67
    0x5010b1000e00151140d011500500b40340c0c0d2600800307004e500d0f201448034550800ca0101c0901000600030780d5031814041b14588410400c81d960181801c900002c030007807900c08001d00c10070980d41d0f88500284400c10320010103020301d841d02d0711030001e04541c0401d865503d07a000d40006a255210300c85e0010840002002c8401036208100814a250301803240f0354001803200d00300b40410b0402101c0039402419a50707100e4610b2503c18002512406194002849100700c0f071301d03c50610100b000700c060071001d0603901c6035186a480308040d18091002c0161400342c051200041c90b0004107210f007074884c80d4003404054400344108090300c0103082401710481888240e50f543c1003ca0690406140a407154070074035a0082c50381140680342139a40305540c48509010380c45080041d6000060321010b07603100c8404074094464603021420b50048915442d00700074015400500540f505840740d0400039041c0980c2d201070081014401960245240a0003402b8100280301c0014080301d109104481d1310804603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 279075584 1250 279074334 279074339
    0xc130203091902011e0809010e060405150405160b091206060a05060f0d15060e101205100503030d06031b08030720120105160302070506060405090c0d050f0c010212040e0907 76
    0xe004c5c030380369090701500042080041202d445024402c2d20b0080007404010182e42c0350590781c9a03903450024600742100e02144001c40e0400204108c2008103800d1410504030280e252060100c1c1a000410788500c9000209010015000003085442c02480003a203d10045070810301072003c40c1d400200d03200900740c02040345800030074040c800e101c060500c651401001030301e0250300611840c50020410300c81c000220803414101d4000c1c801c4200c0848190000c40e4540d284183ea8001c42c2c8107034085a0036010015042c145a2010b51103030007900d2040601c140d82401036403107030b07030b021949000d68030b0350f40d000700310f14004070305801c82c106400c0800e042e490344039207022000316015001880d581c0c0f1481c0c0d120024004480c0ca010707124141a00d041c5411814014951190780e40d4441c05071401d8000c0384e581010941030481484014007030403014143e42040815481c020345da660f0700c1e15072081c01d401171134441c01403076201050100e0303c207070712410070381c240740c1404195003103403401801d03122140c450360000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 279076834 1250 279075584 279075617
    0x628020406230415091707120303091109010b070b010b040501020d110f0708031309021312060f1b03061406091c05120903100e07090b0613080c13020309190201 70
    0x4d07142621929500c01e4240c1b0700d03242c1180100030138020251b02907000079805019034040102c94103e450f41600d404a60740c6054200500703960075440d6031a8005510f4000801c0d0078030980c00508000c1d01c100c0f003840d850313a40d0300d200b04800d0245002e180d0068101018030b04055124445e40101e80e8004400c2e40d54520b01c010000d0b103485140c1d80149480e81000c01d0070207903005200d046d18000c01c45c8140961501a114240c800fa04c4414000c89540441c022241410f10455074024082c0007039040080140030340c803506100b40c1d40801e800190000e824481c0110350a500710240c021240d0001c0e00060800d8005400c004007102241c1c511060164000a14000f240007000340780c1d003440002d04155624402901171500300140c480c81d1841040c200f402c0c0482c418800140401107035100b010000302c1040b6200007407000c1c4225546940d007400c941801081e240b0000c41c0c3c0000380714044600c440b007090205502c1c03050740401c444501d80c40c0c01210b03005c0c3c040b250640c0341c003036000c0c814500342d0024a5400c0c10f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 279078084 1250 279076834 279076859
    0x90c0906070203010b13150909030206010608180601090b0a1a030402040203040819030614120a03080603160b090316030b070507020f04090501141e0c0a090806280204062304 76
    0x541b58440394482c9079010706401c50600441c080d00206c101440a1107032034030040e40d40e03c41803003044200300d0070704000340d10721021109401203811280c2c2070321030b10759480300078001a101840209118004001000841c4102c01d80d800b41c0b4150751000d8141507503160b400b00f1000f904010710555a91404100784094001d00c070700c2c0e10780c3d001100d813070000d002c6060081d10007500190380001c1d03006088150610907242000200c040c0d0840d4141f43c042d44039680ca8000c07030f05103011500036108107011f148011624104a4010303140c04a01541107030031010003003595603a842407620015100044640200d64080c1c418802000c5c0903001800c6000040990004901101c080050548859549412054090108030b215030740103044410124840f1003903001c0301144400241c030480000000042d1695068051004a0000c224460a0b90174500c0c00251510032901d012101815150040c140300b03001400718402d031410b485160743e40c5144102401d0300b05100b4480c0b80995503002c042800002407404100c117 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 279079334 1250 279078084 279078109
    0x9050c03030a09030c1202091305010e0304030c1401080402012c090c07020301050c0c19020f15040f09110a120603061b020c060301031703100914010311090c0906070203010b 76
    0x291202600f519500305014000322680005d015629008884009640c0e011822a00101d00341d80300c0505409510700540140f003801c07440d40d070502000c5000020300031010109000c944d200032030303a101c0080100044900300b0741240c00130301082c08506a11040d4120070120b181d052464a010309051080034002101990f0442d46150060000200c4004504081c0101d80d0444045c4140a051444614280e0b40b5040c201c1c2c0803015100c0045101c0055540750b030300c1c0124402c030141c00601000c022004600da507030710501580040143d04800042d140366988203440c3c1d1040040d040c0c5050503200c11007203600c10b51004004030195152174022000c15910710075000600b02004d0300c0d805982e40d07030f03001034101034400409501c201e0003071004001080e41c000800e00003520742600d0540d2540d89112600000010341c004050207890401d19032402085454030f9030580c0c3c010380300103400101201c200100401d0440701a6074005041c041d4000d5410018007401407544024008605032903901d021030411030b54403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 279080584 1250 279079334 279079337
    0x1e0506130617010e0a0906020d2a0e010c06021b100516140d020903160e040c05190512070b0c010203010501030e1912050d090f0203060901020a1209050c03030a 70
    0x940c04000068002c415404280c001c1ca924030099031501002580c489402403040e001191500d0102c4104217041e41202c2c0c0ba00d1090400300a80d081c0070080000d40c03032041310300605c0740191540005286000310500314203104141e480d000302c150550341d001c02a4101581c00c060070342402d0030f10400304000b0f000c01d0115001c81d490009140c90708070b20300648600d40140040c140b00c16800f4045000400500312a16400c91183c0580d86171800d40c0402e103058070b0117942c81c03844c1038008400310b01110b030000118095805180d04403803a986500810442200007070400300c001d40c03a01420001800c010515900c101010302c10740c0d1170f45a8400c0c0c480c400b1707800002192030036540000184115038145c49511029034210004044c005082e0010703124a100380907001c0e00c0309402c0c1d0080320450b84110b08036069614038985c18810320801c0d2420703402548010004a01c41d00600c0f002641e01d0805100340c0e0001c0605a454166916680072540024120f20714143c5040c050f011414500351000c200818064a50f03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 279081834 1250 279080584 279080617
    0x1d10020a03030f0c02030403061814061512060f07020f0102040b0309061308070f0206090d26130605030c040e1f06020d0903080d09060e0c19050306011e0506 69
    0xc1c070740101100d9000c000890550300e4900a0070002d44d000090b5800d59030b114100003202c4140001400c42904044801080f0030b14130740c1c50020300000070408070300401e942e4446410400e43c4200f001360f410800500f89804e42d205000191030090307240307559031b0803851174019610030550047c0c800e82a40c2c05500428641d04000080c0100e130700e07080040c25400010602c405c0010f00d040d42d2444c5051041030b0010340641113210351042135603030354011200b50f01d078000e020754140c03601c038030700009514940061001005100341c401136168140030f08882520490150000415003414001d864542014020042240c010310001c10710300c1000c0c03005030291449103415500001401d21250b00080c19410000842d000324031641c6180e41c0108c20181520783c441682c0f61284645800080108034200000e48081d0034411207041c82040031458554903501500c5012001d021010810780e80e00051190a4044d0701000040001c10258004c007007074040a40c03805034845036203000241807900107401103c040d19a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 279083084 1250 279081834 279081853
    0xb060315030708030a0915111501030b07030506060406030f14010e160f050d05090c0a0603022115040506121203060117060f0f030a0501020d06170a0b0402011d1002 72
    0x608015160003030440000551600d001050002c00152192241f482003030520000b0040c4035000d004251a0f014440089542448800308820144c0070280310a484c05039500c000b00e41c3c03041c807070f005403803052030040c0200e4603003854404104e008211041003401c2c226030714000e11203050b0881c40e600e8004d000e801111112420003642188880300d01800c141c050001540f20214039a410405488100035005000070701da99521142d10b0411850000c1c9035800103000a0201c2c403d90954040c2c01c00d40101c01c11180c1440030f030f0700071182507003023650340e0499401104070303c1e505d51501d508000e51040010700745118009001402030f01d4085500c02d46000b02034040f04001c03107960f1060001a018031004402000c50030050080303079914203000800d901840a40c01000d0300b0303841c104505800f40761311000031503172b0b2105c05040000900d02405000c00162464450080d640c00c001079003560b880e00503045c48001e440e59801521700c00c1108400310981502d1040f00d840c95900d14011003c20012500501947e40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 279084334 1250 279083084 279083089
    0x50a080a03020d0531030506090106090c0e010504210b04031101050f1e060411040b1308010e0d110a080f0a0f020607090303030e030c03072402041a0d0b060315 70
    0x850703c0c4048410400c05000180c041c0c10710011009080c07164a51701030003460014840f9000d54182e41001c0e10a104080c14010103031815400320044540d08041000706030b400030300c00c90303401480f042d8036800501c0c01d10061046a5402404c0410362151241c0000b8801c5980e8036041c040008071000e80c08109180303160700d4191030a000301c592041c220795141c01c16103048203180003882c00c032075525003a22409000080310b0b80c40d15070061043c01c00307110310b130381e1110380d9640d20341142e901c1215860030400c1070110014071140140a4600c84040c0380c00a043c9080c1c0602c0d00701d403440391400c035682007803003002d007401c010a0f5128020011311229404890b03031898029000350254003403101500855000c0d0b000c12001c144d1015590042d280c0c541350104003039114100c0c092450081148984850000050306010403011034490400c0c420452554061031080718005401ca004503c100303000b602109940c60611805a0b0080c5070249070760000243c08140703140403c2036034004441d0f42804d00401c1954a00c1403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 279085584 1250 279084334 279084343
    0x1503021005072612060d020910062d0c080909010b07110d050c0f0612011205061b0a03020c0a150b031203060d0206071a0906070f0804031d01020106050a080a0302 71
    0x10102503003108128211003c2d9210303446100d4042c0f84100b10030000c6a890b54980b414001030940041110446003808010215241c86903c074020104101185005041d400d203443e0003a1407407200018050544824004d841d819201c0030700701d403007007030410031188941c0d80c001940c0c0c040c100000c0641c2d2951014600820034002c10308016200e408200c154100007000003864203001c00058891001072003000000c94428001c00c00104090690780001140003000040c4200e1007601a138111001501d030f4a0501020304c00c1e0800e11940880304205040301c040c042d40003410114882e0f02256600c1d100c0340c0707850301c2c0210200e280240d03941d01c80004000b1844d0801411040002c0c0341500c1d807860411900060503240c0821000b40101d0010a0402c24083d8129864209088115095074980344c14030700e064480c2d01c1180e8400100e0300a100055900c0c1c4500710b581d04c0303254542c852818143d90515901d20a04512414904541d203030708011659440c2d1070b051000a207010f40003040102d00c07a280180c1003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 279086834 1250 279085584 279085613
    0x120303050601031a030a0204020a05090a09090201020d111c110d020f010606140d050414070603020703090608060105120417040314060105030a0b040b090319020c0117100603150302100507 82
    0x1d4160401350003656601140075080c0c0707a41241c0050b0b440c1191481901d80d03005102c0e4150b4800ca00d074200040c41c800d036400c5100c543c2d20076400d0302d004d0441902c00f501c066a40e04450001544000403412a86246031400340400380c15003081d803454000c52040e00d140c00207403030080c1c0052b04800e01d2540480001d003d668041e10f0241089a0720210301e010081150040140441e004c2d6110f50101d400d000c000002c01c240d030552942a039402070345034000600a54410b22044001503001d00d4001001c922850049001d0341050b5a101c3c07511000c1c142c152441c3e00d001d001a80e0542ea8000702c40c9800c82058010710046100e00d81c2813040400c840381c3c02d810100b0507070000f4001e40060130300c20006a000805198419801100c5140b9501c03030940c407501e1401072405000c900b004203603024180703d80020f8056010030090341c0c1c0700d0031402c03c64580c003003060f8140c0300c2c01101c4002903414094240a6000078401c811034003292590945e1f6500000c42040c24402034402003040054102c044c85000810010f4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 279088084 1250 279086834 279086861
    0x4030e030d1e050706060f120308010807050105030604050a2c1e0d0507080c03120a0b01020a0506071b0203060a02031f0506042714100608150d0c12030305060103 71
    0xc250703100410107030000c00070b0b0808504100700015003000300b00a603031000014042d060300026402d501c0b1000c0021003209501c1c150040741c996000021149000904141600c106944a034110b8032080b0510010348000340080c900c80d074441405007030009400a03d00070300082d258081003069201c0412508146030003844121581e0081c02c443c40c00744000540342240c241c01d00c0c00302d80d58001c41c145403029001e2001038498a0100240200c11040d0b0a0300407070181c0d000842c1008044009801681c0d11030040100912030b402c104001003145003c1d2560031413004648080c2d40d040300711a800a42050310072503407503a09543c0401485044052075500c601c0000c0d0a160201d405414080003828600440c0306d0400d41000045081503d03050458102081080302001030204509070010120a940200d0385070250360003040380041d845100d00075080c0918005680b4011060140c3e0900c9000001c806059038081120309000690080c5e003825420124029034001500d814000e00050071b5030340c0c0960211 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 279089334 1250 279088084 279088097
    0xd031d041406040f0911060c1f06051305070801030b06030c04090803180a0c030b0a11070507151407060522030305010e06090403080708072f011d1b03010906020304030e030d 76
    0x10005104449040b84d01b42c021920070751640c1d400440140341201d050601d58400c194071401182010303031070b0030003401d4a6040ba52151f00b528840281d004444003100e809002890417001080407600031040382d41c00c20409000c1d500401001d0020405582000c507003140c132102c00004001da0740c7c4e29a0302c120008030700b40000d0000c101c80c50b100c900c5c007007038580800f070710317205100300801c81070400b50384100641c0c01000112603c4452908005895080c1c81c803c801d0030003960b01090b91103512072080c02c0055888611840d003407082584a00c070003032000a1000e1101d0040150100c0381c4245000842e031605c4c480c1c1c0d0701080079810a0400c0005000207450240a4841201030100098201d507210343d00c0080d9160668590f52070010490b19422070860b00030360b80d83e221519010080064455480c000e400c40001c0c4003a1b644036000e0614a1380c07401b1250310319005415a41c050f10030005010880110041c0042250311054441c1c504a900a4804401103030914030f414031217040c10710000348c092101d81042c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 279090584 1250 279089334 279089351
    0x4180f0b0117130209090c0a06030213030809060706052a03130605061f120b0306070203161a0f160c050705151e040519050d031d041406040f 62
    0xa0010041c030450070350b200c6090000500c01042c0080d509014035002044041c4c00d0174011040e80d251842e01e0011070203a2400e030f00c045a4640070303000b102d8809081034103502d101403454403154560781011030300c207600201c20401c9901041040c000c0702d000c2e40d03c2e0442001d115003601050500034442079544260001d081c0100400d0001412155280c00e4111401180c50341c2c8050000399119040d138001d900c001c000d00223a00340b480d801035202480c00031802081180e50300300750030155207100866061006034001c20401c041c1d068060b5103800300620600da403044254862008515810b42141c00c0e590250860041162491200f01818004d24880c200803426034020746844c0d442d0704003070080d54010342c1c0380503000903400d0070841224880051540402a280d5007040007440f20b601a01c0381c40c0c4078410070428500345a504281280c102c0348024000c03118038141d82c0e804e41c0e1202070500781480b0158580f0075501541c40e180507414590b12004c1ca904460328103102080100c230440d000e400400d40ca801982e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 279091834 1250 279090584 279090587
    0x60b0307020304180c050301030f0f330510060f090b0403060911090402091501091a0714150712020f07030207060801090e060a0518030c06011a0c210f04180f0b01 71
    0x459040d02e40202b400b00d60404542809003140403001c8000b0013030410700680e0840010300e000590f0b080c0403241340c2c070100c010181081d102900d00a54165491180340d400403c003c50280700c6440580315a81410000141c1c2c1d8a81c06407546c01507403051341c0c51500d942200c02084640d4003104582d900884070500e232400c0c980c000c94801200207020110b003207400010140c031607014843e404001c012000c001807807101078040303081c0c00e60081001107503015460050040341000200f400b001207401c2c0d40318513a50340e40c0d000084031f4880858960b1359400c0da003003000c1d0f00d02c00d4820004101c124080e800500501d4034214005182c4501640000310341403078400803040004000c01d1a9800c1980000d0209140d242d003070304600d50b8484110009042c0c0310000340821614004030354a812030f0b888000c0c40350101441500b0f0340c0301e0f00c1003d01d1072940380c00c0301c1041015407640e500741e40c080c5001c99140301d003000039044543c0d03400d5005070483e11076040f008080104400c40e5016990500207400000d03c01088000700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 279093084 1250 279091834 279091837
    0x50c03090c010f0203160f0b0109091a0703061706150102120a0c050c09011d06060a0e12070302120f010b152a03030c09030d030c1b06060b0307020304180c05 69
    0x4040d0b0410000c903000d03100c403500c02c0064862180c01c22030700d40f01d00c075a9440d148500003056082201e5051200380001000f809603c2050141030b0802095000448510346000300190010600c1c0141507840c40081090004802d200e0a50142e42004020504010786085143c900d0100c20a0441d800a840d10304018880015200c80c2d03541401d00c00c20001d81071800b20b081104c02c404150b00807180800000340c2d1018048010035484c0c0705844802d146c0c82d1502030084038443c01c4442e501245a900000010b81042d02903c0c08030000b0a09030b4a03042d4407a03000600c4081e00c031401002c0c550014600c05000b1000b80f1401d4200755048038042070030982c6000e1141a80074005c2c4159445510042e03100c01c00780303405a0085240da510064a0b500c0c60082e00d8066280c001c0582c0501074421414800d00c018041d1141000304a00e589400c04020f81c86440340c6909407884d80b0403203401d5101d840006509a461002c0d40c055091600695281c1e420644080e164079400004003110900300401e2050f4141c0000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 279094334 1250 279093084 279093103
    0x3020a09020c030927070309110d020d050604150e03040510030506010c050d0302040e0a0e121e07050114130c0506160203031c0614060d020309160f030303050c0309 72
    0xd402688036814007101500314082c01c1c03505a0000002c1c4004000401130303426006a626200032000040d4442240c11422101070314001030510100e03c8081d00c05c0d150600f6018495417008000c1d41c00d1803804e030f0301ca504100068500302c03a60201c40014031a1440301f8040c115000e82803400942c101480c1400040e10003442802c442c1c00d0560310008a142c6900c00c0301e05441c503a80200481e9030340c4080440c001c0080d845485150070001c0ca10000c5072141506016100400c1669002015040040710000b030040d03010000c013408079810307440e040d450940d071b4070007030088107024000005520400d101c0e01c2203617000041402e041d007540115a2000910b00c05a81810344009035101070b1121000d1011074443c00491002039454840812401020a000303e40c05085514070442032003030b60f80d195444c205030345044a0266120106103c200c9513010641c0c00b9544c44075a42d0200c901c1c0c000380500c0f5480031031040d0017801040d000141c3c10710502d070700f60081c1500b107085000c0c41491450020b103066250304000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 279095584 1250 279094334 279094349
    0x20d1a10020d081914010e0a140c0d05190608010f0509010207031b0201020724030606020f19061512030f050a091205070803040b0429030f040f0c140f030703020a 71
    0x4240710603200742c10780c5c080e69a406003080643e41c0d55031580c02c81c4008a00c1240e0a0350602d040100094400110304081030060600342e000604001c4120507090103800020400550b2005040d1000ba0b01502409414014210b40000241840b500140c0c44103075980201502c0150f80100405000681c1c003007050340c41700c0c003c0e0707224008840c1c4610040f41055500c0e81310f4901e0500c0e0156908028034107280000d07201b0100d40f006c1012540d10301d0241e0b158100600300e2070b95034124900f1403400a05213000d0090091007804000b498010f84100e03000c6502180e0042495060b2208840042581003c418000700350182051414205081001004401d1900503d0010550501114100700c0100480c3c03000d00101805d903516907403510b040400f60340051046190001101c00d440a081c0303540e400c0039100104010f2003504c0c41d5500c004880380c018000d841182c40207103400303155010500e01141040034203a0030b2126424031010108004242c404140b050344203400023082000181c1d01c4150314400c0701d018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 279096834 1250 279095584 279095611
    0x90a02070c15034107020d0302180d0b012310050702060d2406050f0a080709080f03030105090c0a0c150212010f0302150a020a0213020d1a10020d08 65
    0x1c104801038012002c14030b180d98020303030071504000100c1201c69804c5034014a03003050358101803a4049402800d0740c082000d40c01c6511241001440790b0010038401c40102c28440880e508000400d0011680b2141505c18440c000014461010007412011104084044010b2240c032040001a001c800710b14460090000011340c3c44115102e030001d8500003901481e0411003542e1205520310400304011030001414200d540200f5040e0044094504c403881c1c03001c40c54100000c0d210140c40c03040010f0004400e00252440024080d03104000d005210800000619201d501d010b080c8036a13014054407205429400740402c0d9001d591015000078070a401900807011482c6101a14009104003800401c043c054a000840c00d081240c05050481e0b10907038002d01da02d0b540c030b400300d6a540100d0425000581000182001501d0003c5c02040a2403040c880149000890903030f800417115138010000d5020301d5940342c44038501d4025441504c0e8003d60000d4403075000c00d10002410003000404a00c0810301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 279098084 1250 279096834 279096869
    0x5030f03040507121e241d0d0c0609030c020306010b041e0b27060a030203060907030605180c04170d030e01050721090b090f010f0c14030414010501060905090a02070c 73
    0x80405001142e407005084086c04000500c42c941c05402110600c1245c2c8618141d21032100e60001150503d483e550b54941c21001d25550303039200070300014103084c1d0402800090610159905100403402403070301c00e003150b91729880d2080c2c0e903034a81c14600e12103e8851030380f00f040169004d02008c40d508011140800c2004400c8101e441000e101c009440303581251700455080d5415030968021400f0700302c111803800726580d070610102d06a9807680146c580020002e12403884035407001032415040010007100608003505ca54a1180404030001d25044a0780b1050b2540308141c1c141c400c0340c8507505058003d0140c2d18060901801043c04141070004400e40c1c0350000711070b078030309034480b4940e150700c804051418108030224540d203c104800d0f00b812540b8103108491104582c0c86450010100e50f160303080b20b0208020b2400550f0030041094880210b50001038000c805e0a109060181140d9129038001034103140c248150218010b00203054148100301100c007041d800b410480441c0c0703100c80540401c02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 279099334 1250 279098084 279098093
    0xa0c14010909021306020606090121060b0907080105090f04120c11040603030f080108010c090303110f06010312090602010608030d0c09090501031110020c0f0105031305030f03040507121e 82
    0x40741d40e4000740740c107840410041c826049480120080303652a508942080c0c50381d008100b1203034401c1c82001080000a294820300100e08090700240900403c40026184424004074070700e030768111080000640c03c1d60060005107004a01c141d04200c201c00e00f80e0651902e9550300780d400d020b01c203800c0140541c030380510080000800c050346200d04080c0c001c0c44019507a20380030346000c0c18034026901090f018400850b42a0052103402403120781982e4400074a031554400b562034051182c2c100030702d030051111a81c281c61080000703a000303510a1a10a09960090318003d101000c00e410500440e41411000c0100d0390000046d122010f403c02d03000612601c403d441511a0046648455102410000000180301c0111141454010103036006140c41c504403400702c0c0c41d01880069154807140c245c81040303446d407051001d554000d00540840c1c440d0300050303c50707502d113070000d600c00d06031044000100010800e0520140307000340407903080c245080d40740350b5815903010241c038007407015440202c04013002d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 279100584 1250 279099334 279099347
    0x320103061505150a02010e030a0219140307151a090c0c0a1505041104050f040609080d18060605030721031206061112090a03020402071106030f16020a0c1401 69
    0x2000003d180040110b82c500c09050544c0000e01c540340554600a5107995000000c0b080f0380f035103121035015054a903040300a560191002107401d4850070b1f803004181c050504100010400c603800350420341c0c5e4410307030507183da41074072070b2071031030b0019048000d1164103203407102d094071600506403070051a03e9083c4100b0740c6181090710f8901620b04c8201c030340940c43c0d088040d80041e02440c0940301c00500c0300e010030240f01c291002039400914004c101340002e40410000d500005d02c180c80346910f545003800c2c141c441400c0d40c3c0300349010020083c0b032070364150401140744070789401000f0903005007000c9031400400541c0e81265510136001220303034550130000c141c4525120800600c2196080000030741b0f4500c024210f91411240d08203c1c85580d550404a858020a40340c62000007401d00c00100d00319824030000e5041080308a17010304855015140e43e40c1ca120295104802d0140c01c0001032410301512000c00302e41c01501c40c15508520584004201c025030158169850240003550f21300444004a544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 279101834 1250 279100584 279100589
    0x90a090906020d050403090f0902030412110f03030115030e0c03060402060c0102040f06080703050a0e0c0d0201030b04110c0d09080c0d1119080f030c0a170708040305013201030615 79
    0x1c0d504c0c02d070400c0308241d00030f4010802d0703c1e0054a5000a2511800700138201c0c801500c001c0c1141100340c03094140321f84125000d2441c3c510010a546400d903000107658550b801c280c02c03401c040902082c2e04c009081e4984180c1446c40c0c1160000c041d01d05029020a032541e401a1001e80114000180d09240d11030075012a80240011052078407001e55410005266107016034051001a0814000c40c5042ca400c0c00f4190074081c039800901748810400c0100140c124500100301d041c50313142c1c40c0d512203d40c0c0b28850ba000c0150000c04581ea18911408401e04154070003082c00140600c4040611071041c0000c2c42090310300c0e050381c07501e0040d207003810000ca044140303841441e40204041c000d064042a440c070640704550b14101110080b00409505907102c2c024001c2c00c940c280d100000900c086201c5d0707a00c11964081e80054a4a05503d82e01c1e6101140d229400a07075050b074403811404c010100e0324806030507180340080030070342950880051007100e500620014207100c4d00d4044502c103001940325031400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 279103084 1250 279101834 279101857
    0x1f110a0302220e180102090108010b3610020f060402010806060903030304050f060601090605092106071e05071109150d060b0f01050705030f0d0f0609020705010c0302090a09090602 79
    0x60095541c003490003c3d02045030382c0745031484143c0001040705814001c0d920a120f0503107075003072075a0030f000075650250401c98864001068011f1131309483c0da800c0c056000c41d4854847c02000f000284024003a12601c0c100041d811940b0103041c02149100115100b90403690910f032064143d112178000a801d401000e5165070706020000900c007c0103000034640c06603080590503520300b40d840c0401907510301688d2050001051007008100e1481c9480141008004030400e92400041e1105d8051071603e101200d0300c4c1c01041290704050302c403607117880b110740d101d598500c0c0c114a054015910000d2600c01440303c28021410a030116140c00410198502c8400c001340203166902d205080c00c0024044003010a4010742c1ca83c00c00d08002c7d40700c6c0c4222aa0f55811800a41c50264440b12200903641315045203801c00c0c3d61481d500140324103d000744401803131818805a00c1d118682009400c5541032030100701498410000600c55440300c000c3c400498030502c1c40064031020504204010307108200c040103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 279104334 1250 279103084 279103147
    0x7020a0c09050402011106090a080d090b160801090c0903030f091a09041b0c0b04060b03150906060409170706150e2706010918141f110a0302 62
    0x51081c0c0250301c8144141c0c000d9860001701d14208400303685440342030f40d018005800c404000008500400000c0018500c95480058035019603100c40014040c2030b2403004010310800004100207a004015502402c10110108014185201c010303022400380d01c401000e020080500e022a140a08140c100500301300020b81001100d6460742c0119a00000e20548110310b0007040c039100d404203800000c0718415a80b11042582400d8440c942c000b44024800c41d20030340c0310118200aa1001c3c0220001590355144840c2e06040c941417050401100805060050707240440e1070020840c020400d17410755241c0d02141e9a21029070074044007070000358014150030703880341d080050109142c08581c0c0c8115091244440320124891080103440403601ca1620254043d10050240f00141c2d4000c00405860b002d003684141200ea07103042001e079419400f40030540000c8040d162a0004111074441d40180c2d00c0d041250008143c0300300c56a0144090220802d41d0124400400034174190161100700203180108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 279105584 1250 279104334 279104339
    0x21504240b04060605120a020c030c030a080601110a0203060601050a03060504090c051008010b0f0a03020c0d02100e030f1902070302060c010b0114040e06010c0303020d020a11070803040f0b0307020a0c 88
    0x800150040381540d5010b01c2c644200003894911540503602c0095407803485015580301c1e44004400b07508550b00300c2c00a03000411610458142c00c000400300b42d910b030b0321050000c1c909a000980420819a98000740ea00030000103401170354041500c0e0380c02074007420415140c1c42180f008800501c1241c00003604545401ca186042c0316000c800441200d20848046803604410740c400c44500000f80318008002c0c00c04d100900031600380002910780d16016280041c20807590303079881c0d07103090352070422200580c100e5400c1e4044807403d400740c80740701e4140303400541ca0090040f0032002a841500c804141c08802003410504162080c03040307000850b00284000c0c1c460b4017082046000b0140510224085280f401030340c000c080d0380e1700940d011620703c460710001070f64640d0019a81001c00d450220200340c3e08000749403020300b4520242205850aa4802142d101016071080c50601a60002080c03075009000030081c102004c0700c1403050319680c1180341d482c0c2d244d00340103a280c40c1c4140c00c0200100c28100d0003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 279106834 1250 279105584 279105653
    0x20d0c05100503040b07050f16020f0a0b030910020c0c0103051e010b1b0a0c03030503071218020f090c0a0c0f0206040303050901030f0b1e120105090c011d01021504 72
    0xd140100d000e0203172041a0b031038006059405104070010280b8001040c480e08a060000c010a0f60225002038107080c00002e543c0005102c1c030020303030070040034002c000c400d00c1030200081100b501d0a82460204514040c41c04090980e6501800d511504041e00c4a0001d001414a901001c01c00040c1000e42003103940c5400040f406504440b4445022049400e03c84c04036500000780d004c03200c3c0d040317118400c0507811030f18129801ea01c02411141070000f03450052034074154600c03501350652500340415806542e284100314540c80b221100c140700c0d0780b0301030600030048030200894072040c85034105010103030340d945043c03051340c0d28203075000e94000d00103d400030a05821100800b24035400340d0b010850a484907003200102c4881d5a810741d00450715040081020b20b007510701d8880e51100402070704070f8040c140707049030950310203c0d0075100980010405200315600001d14104801032000c00c03042c030800c0100001d586004041128005044050101c0c0920048150044601c2d40d820000c520402d4041030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 279108084 1250 279106834 279106837
    0xb0d02030a2f0604060f112a01170112020111120a0305010b130b0c01020d09120305070507050604030305060f0d050c0f03011a0d0c0b0a020a1106070f020d0c051005 72
    0x100e0301d0341036182c444034150410700c0c0c5501d95000300008001030b040c182044402c030340c605180c00b0345005200100003000b80b45401040502560100f01c8010741c40c50440d40d000261800c0b5002c12a03042c840031183d4813250203000c4108506694803003900e1004188540012101074040300415403050040d1006500520b0490005041100e00303614248a41c1e43d0b0f0300201c038000e21601d003041d041c2104d022002e2120b540020010f002900002e40058201348044c4d10b00011150300d99402c075190400b00340c0b4110100d40500889600101d1420080c4c1000714507150305032507400040c801810160f030760b00050348960300d42d141d0038a226809482c801b4002a645840b9030750382600700110340301e08140c044107000b5180c1400350400751f00340ca204ca40242c0000c082480744011080c03030708403039040d443c040100304040210003400608409500828041d0328908103d0841c2c418040c5250040404001ea400811070010382045496810f40381904880741d282803e120b00e2071325400a0b07521401011783c40107080d50000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 279109334 1250 279108084 279108113
    0x17070e0703052406030f0a06050a0f080106060f02033108060907080c0d0b0c070623070f0806100c02120307030206090303010e160306090c050403030e04060b09040b0d02030a 76
    0x11400c3c0074410502d41c03802c0c94459009003903442001000090800c85c0001e4155822180c1ca000101d6021b8556000400b404172a8010980843c041c0c107040002d52424000d03000144054141024038a04480e0001c1d168410144041140b99004138041065403111345803100038044104e820205a458011041d1660400d41741e00100b03100e14200030804400c08a91490268402029800040d080d580d031000d821100600e040b8040310144003400c0819068050440c90780205540b1200040309070f207200403244005007140b810030000d001e10300f41444d044000d880c0c000c10211040c9102122083e0201c0c0d00d0039102100a400132201503441840890000140c44601d1081c0c080c0d036030700d07230b0340001581c0d880c00244551100c0441800104102c1513076294050031410051401040c2c05445000d114141c1c4e612411880000d00005000c10501d68000c00401d0105001c40e0180006440c1000c40c044600403108041d01c0b030340c1d4a81841d5280d50310740001c640300700da024090f00c1c0003512508102c030302c440245 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 279110584 1250 279109334 279109351
    0xf0912060e2122150e100206041a060319060c0e01140723061302090a05040c090c030e070902041d0907061b0f2301020405030717070e070305 62
    0x40d407140709aa490321070219061a44048030358205440743c00100d084114400d03001d110144141d10108081c0400000c00c1c1c001c0740151604410079a56406000140721466404000c54000c41d0038840042c184c840c80320f00d005030301c007034400d926216000000d040000e00504045510b28800000741046010b4024040c0c12107641ca0300d10441741410015105400440596140c03e42c0400c04000000c80d4025840b45003080d400c140703840301540407002271400209640c000703c05504940700800b107150800140360b0101c0b450209106a040c03561780c0d808206800d001c0c825503551505202543c080c032035482046040e903c2800c454440c2d41d80d00703500c0000c0d401402185007015800d41d4015804602460003402070398107600414010b403421500b02c0d14590144044c00d46028140710300760124000300c000480c154000d004c03074182050110502c2100b4540c107032011841340d00500042140b6580400c1d941c040f0380c01c00300c1c885860030045880c00e0400c406504628080d006060500c400e00e03605a10a91191010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 279111834 1250 279110584 279110593
    0xb071211060412020c010201060803120702070b0d06050f0f0112050702030c0a030801180c080408030c0708180102011406150c100509160608040c061b1509020a091104060f0912060e 79
    0x17004012426102c0a001e030a030b16601c200030340c03551120205500c5074032445502c15684800d8135898220314a5004807a0b005078a6200c1200340300354540320b40c40c0c041c040402c944070000a110240003814003c0580d6805600f55030700c3d000200158000d00c00c031aa03545a40054032601034240c607020340001820300411a80c1c00540303050382c80302e60851140c5054015a511040d40c155202d0b9284800c81d4030060000042c480184509000140c2d0070b4054007006008480002240c0e25010009013142c406805000c6034008a1007801603d40310f400302d0407032403410300e101c840c1e03558001ca50092031701c000c1111a0600d689070600704003500d4400f048007107c0c9d440510741e5a0303001ea601c080841349543c0c19500035122010188082140034040c1c03000a0307459020f4004001b42c842251075124071180105c5074017122503110032a0030210b1a001c04240c2c060002d406040144502828004d1001d0280d400f82600b8400840703150340c0d2003070082d43c00c4002007442804106600c94a403810101a01112401d07034540d00c40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 279113084 1250 279111834 279111853
    0xe010b370305120a030e0109030c0b060108100515071b060f021501090218041b0e030a0f030305130b13021e010c110f04140103050c0a0b07121106041202 67
    0x159030a082265000360050401c0d210400e8219101d138041c00014052581e40c80e2520030035682030213039003000c81c000c1d110f51040380424109545124001040c05040081c80c1c0c04000110170382d40c1d00c00f010340d0000d94100010400703078a040003c1d40b1407144094001c0040401c442a801003003070480c02990616990707030306040304401c000d0341d03100c002c810460b2215940b0b40062040c1000c541c060425110000d001c02c0a21540e5804201150140c0982c2c50000d211108240062074001d1020790001c101075000b0202c0f120f9940b41c4507022140c40313800804043d00ca0010403680e04051002c0c001d00c070740185100140d400d06103c0400c8800180400301e0041400c81c1102400c14085d0f910814001c0060f102e00003c5015030b42c0e1250300d44810550240e0040d012080d441036525940700b0003a0005040c18031884a506504080e40f520a460031001e01c43e6001920a11030540708000755202c09a0101210703003160000c4006076441ca41c2101c02411610500d41040148643c891190207864007580030b4400200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 279114334 1250 279113084 279113179
    0x40f02180d0b070c03091205070501090501021609090f0506090705010e040c0807142517090d03121103040506150a1202061812100c0c02130e010b 64
    0x284598040c202c0a61040024080e60055581410691180c68182005a110400780c41d4403511031006951640c07140c05c06121a50300819440d01030b1034240002c2000c814102e221071314194950040c0400d0b02d8489030003900304505512090106980042038a000e49001e8000654880c41d601c86d0301d002a001d070150101b01d04141c4100c600589090b50b500717105980b040c9040c1d90b82000016921502901000700076603050312003004840c4a8480900031415043d01d082c82c502d00907941020034101541080300c1d0115030340710350304a4126945820400c10b00c510242c001802404070502d4038038040800001c0004100740400c0040c8220800501740c079a8242c60414441c01c19020b0248001040000c24104003529151000e40494102c1004074800e400003003000c591500d04422008540d9440302c1c0b41c7c092280c00c0f0b8040d803e000d01d05850122403260581e0001841714000000402d51170365500c070303154143c44082d0411201118003a205107403281260b1051401204011848030140014041161100c1e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 279115584 1250 279114334 279114349
    0x60a060902070210030902030a051608070504020309030a140c031602091608190b030703030f080703021204060b180c210105030309010806030717060106030b061309020903010b040f0218 81
    0x40c0c0c0c001d00301c25060203107504285c004000e284070990b80b42c400d02485c440010810080d0040c1c1c4213041e050151003515040700c551804800390000361240303005004110390542d00006903149130300b05180001c0d00d000070382281042c070307c01c0a500160714000045c01a100ca00c50709050039926200f550130003555940c003281e50101c840a6244040040c40040200d403007005044070041c1c0414802c42c00080d1010000002441c0200d554000c501060f1b0305c0016074402074000c941294461820f080c2940340c42d505007502c4144640090005021584e10b9031010b1094490038004404048400c00b4880141044848803c0070b4010380b1404030407907040046c1082000da036040013412100041c0055003003440d040c0c01515848402403640d80c041c405e031007001403444400704e1910407440c5d00d0f0002d8140d55040c0880207060314003203032003280070f0b00c03041118191519041ca504005c030380c0c03480300c0180c03a2525040081c2c05003900340b1009074810f041c03407103a1961601c50760041501e505401c1e00d58641111a0081c010790 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 279116834 1250 279115584 279115597
    0x4060206060906060703090b090406050d0605070311211803030a0f060b0703021f020c030d020903010c0f1715030d02100b0a0501140c070b0f07020406060806031f09050d02060a060902 80
    0x7e44000010080421000b000d4111070f030000b040411060348503004181d0340c000e2034100791a140c3d1144248800306800d4450b0400c3d10012045c40707868514200083e07103440103940c0c7c101d4013511000c00003580c1c03080800c2c4402c1000400205495907410b003042d14001820b41c2000d01d008040c50311000140c403100600c00c4540b02c60b0b050b0041c180504015400250f01500341d081311845c03623000c200c070600403042800200817103450300600580710311b034a2050508544020304144240481401414072054014000740315040190211040c190358040c0c50103400c6000d0071103982c1512554404950040d004510180c400c1010b0404110079030180003000321481041c4039150200d0101c0e6041211040440024a04040c4c404100c0c1e80251f42d44104001d81e521111001d080e001d0301084510441c81c5c01e000b0800240340b05d250142260905174006920f454042043c081e2440c0008010b9001003090b800c00c1c050207421105941440e0030b00d50000e9100c1c9400c64040802d1031920b0004a1a11340910982d1203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 279118084 1250 279116834 279116837
    0xe10021504020d020d0c0e0109020f0403150902191a03010e040206160c0e0412081b07020d1b06020624040c0c23070905090303070807120204060206060906060703 71
    0x141421541512904000c0281c410b9812201d0380a10701c0150702d54101a910039440f0381040100c4c0b502e00388040f040d525068020101c060b004000384103a81d00d440c1300343d40550741c20000e0510180304183c2d100c0024084690000e401880909115100070401005201210100d514401c0ca42a110141c01102d1100b4094110174201060104025060a80113412103010400314811045601d460300c6803081d409610141856401b00100001c00804020484240b0b0f017604000c0e0042c188582c0c0340c440307030070705030030b007660000c070101e060401d554444106030180358104019aa0300800c0340684141c003010750140e100503106050220740c84403505d10103a841900349103483c903a0b80a4060801003c0d000c022160410001c2110303680000c80c03001d50700c0e40400c44441c03a200d0116200103038a02d0400402c2d6005081e01854002001014040801100d03800000c51410740415594020b065461116140c1d0040c0030070310100d00401c0f6070f90001075450007094102c1c2c1000f61540c3d50010822a803044910090 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 279119334 1250 279118084 279118093
    0x70b15010c1523040506011202011701080a03030608150a151a030405191101050a03020903010e0c03100606090e06010203070b150901050d231c03021201050a03021005031f150e1002 79
    0xc20500080d80208c4030f14414035001c46440c92502601c51108420b030070210080c1c200d000c4c50010550580b02e510000c098980c050b000d0310b40040805e42e100c40d0b00808080102d034407010322052079000e65850201401200440c005041008030004005401c101d03030813207180c0300360304450b10074510020104408a5000044074503401295004447d00d0700700300049010315400707200058481d5020300509020101403001051315401c69010545032810200a03648158604101800b460780d00003016005e8420301090f04c86580c40c3c0c3d0300100d1452040c440e01900c002200300270711195144000d54400000c0003100c20a525913242c0d02003146a03001148003d004402041442c40840da80c207001c04d144030200016100c0d003503404540c1640d44074090340800000b84e80000c82c02c0c2000001481c40d07000d440c0c2610855001411940800d4100c42d520344528140500880020040e13111a4240d660500c90400b10002d420ba45000d28024166901d0004d80400d1740152100c4850070440030348132140d46183d0091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 279120584 1250 279119334 279119339
    0x3020306010b1630050a0f050c241006030c0c140a2102061506040308131a040503100b0112090305090a0303090e010803070b15010c152304050601 64
    0x8200c41da00c00c0c601c4540c445032400120000ca440c1642c0a44460005030307072880a03280401001c10342800400304d0005001702401720500407907110b03d12829200b060304140d0360ba150040c4490345080c66041202011004020602e412480c40300000da002d0740a80003070a080300e40310f28095090f5040005050b000803450070400c004241071040d8881c00c00c80350010b80d0394100700c545a141c2014045401c1520700c51302d4aa00d070008540c10032403035500c88682c0d00038403440d601d0000010400c1c452032002411002c00821000c0c8282d061080c600010b110f001c500081c48155510700000c0c1350032a200c0e41d80700303028146010071a03001074042c5044200c0e0507501c5030000032500c417640d401041180005e8082200521240c1d101d61511100440658006d4945210861401301c40c02d0140e44143c12981c5035810510500300050707004039003a600050120119064418a440100d9543c00700101c050407a11100704131100700110313a401400104200b6681c004036010512a800c0e2006080d40c008220b6407000004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 279121834 1250 279120584 279120599
    0x207020109140d030c080c06010618290c0f0a0c030605131a0c1b01020301050420030c090f0418020f0a030507030206030a110c070e0703110a032c250302030601 70
    0x45d10001482401100c3c2014002c440082c13030440242c02c4400071030465400064599100e100c030a0040040300005103d00f0700319031203004038400480303400c3c0f06040c000c9260b0446100174002441016540c40880780700724468100414850986c0c48203032691450600858200b00418102225803504034070002e030003c0e004d0b950000c6900300100394124800091202d10440c02c940d02d0a4502d1030003001c00540c803941050708000c1283c04500d840400b02d0400c6201c41d210700c84141c20303a98400e071513400d401d4980c1071fa040410540000b54101070790003403604940c5072054102c059141c803041d000f541d10b55030b01a4018144400d001d0b45020250a0ba400140f01700014a0403500079903119042c80400300c2c598960402c0080b507900a01403802070745c0c024000912012030080022948615580b03024080c2c216090780081e01e038803600034640d08140e151020b00c1449690b40d0109281d4a03950f008404e110402014139035202d201402c040e2310041e0041e014076240c8400415000103a9070000e024143c26443d0515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 279123084 1250 279121834 279121847
    0x8010e01060509210a0b0f0603032b0603020a080d120b01020717150c0712021f051f06050903160509010b0d0902030a030806121c0c08070b07030207020109140d03 71
    0x481540150b91404c1c242041030003041c2c01d031441469141d0050800a0148200c0600104014007a91061001ca14040c480da0003400e007116012800c92840088004d614001c1e104a42002c0d4200c054508002014440000c00603001d200954810516480e0302d41140c09440c5c58a842e00d0041c0e1000d8014080d22032002c03040000704c00d120f011180d9049804035078802c1094119003180d54003001041c480140004051030a0f864038647c4058141c0c1120a04040341e01514144840811991100010000314004c101c0905081030061405081079454000034515486140e001c1c0c013030b000c1c41454190303454900030b00000341c0394001c180314016030030040742102d540c00c09007440c06416107400d03031342c03026803003d10001c04664080e540310801454504180610703d40080c8800c021940564408000c6c110000c00e65002d101c46844d04004400c82d604005c0658001d00704043c0c140d0340d14406010f9610381550040840e64801c0e01d5005aa82d5100c2a00c2c28880e0085025a003210841801c000060303c50311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 279124334 1250 279123084 279123109
    0x70f0504240801240f030605090c0d0602040f050a0f0608091c08011a07020904080c0a151406101e1e0c021315120c0e0f060108010e01060509 62
    0x19450610020031441c5415448181d07848594583d41d01c80c0d015001c130200300320404581303841040110740c051405030410b101c10805d03c005401c542d81e5001140c1d0b1004107010181016400070460b10441e0202d00b0401d009602500c1145e01c5606001d0740001c003428a10300c000226001905d0a20700075240240c2130300c0c2504010070380520bc0c09511025604018800d140200b0703c030895845480560404c042942490100b00190168007428408800142e42d10041c060b800b680c0011856241c3e807030f65804a140410482008000f9003900e08030860f42203140d031180c41c08141e100d400c41042d4482000340011500c039005234a00080750f003401020a1075600c0030604649107a0f1400d00809042c0d6180109140e00301504000010340d068803040070761403d5072402e05128800502013140d888040c0e012520314074107110364510080911105000d21500c103214100900b02c00d0b06540c0d251030440607900c0c50900440d81e060100e0583c1d00003007414003100b0b0403241a20415114180f6140c41107080010946084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 279125584 1250 279124334 279124361
    0xa2001110a08070501060f09140105060f07060b0a17060a0605010e030d03050702120d050f090d17040f021c1203050412050c0f010609090201020c060306010c0b15040c05070b0702070f0504 82
    0x50400040202268034a40700400740c4007000101f1829040b005c9c0803070481a0300052017000300b0301c146840c101d9414100c80c51150300250001c0c1c80b5928dd000302c0c0400000d07030b100d45201e0901002d0305010f0301e40420568031035280c120003000240d0301c2e14010b603142c502c0c0320020b54141c1d112240d00b1032503a02a40c400c941055060044480003113110340f200649500c040c92205080344c90344144969001c880340a17a07000505c100240805806a6900415441d8500f0840d5402c80c001c201041c20b01c2500680345081a8002d8400b00000c1d01048007024684000c65040b91041100181c1d040c0072882449454020395000940c942d150000c00000c40f11904150122001401402912040790302c1c01d00c0346900500c1d040c800811100b100d800007904148001e41e5040c01907400f0010003205e42c1e0300505680c241d5510580c04522a04c484520b07249410b4405c2240340c0007440c00408449072604200508205031146098524640ea1494126102c14491113110a050224102486680f82681180d004000c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 279126834 1250 279125584 279125591
    0x6051503010e070504240f090303021b0a05030304080303040c060c020f06090301151e120809120304080105040302060f010801020702100305060f042c07060f030f020c0a2001110a08070501 82
    0x40d0202d120403589a40c1603085403005803002d1b8139001c0d421101126402981e81030600940b0300d551000b03925a0401c0042c80c2d41c185e028120091169503800c20440038083c0a03044944494890080a0f500d0744142c0d826650845025000142140700700030310102c2541c0074107000809250030042c0107a0350800c80080e5415521815140d85d8054244c90040040544114020a004d028860601b40f16010740100c501c500323541c000c40303020500c603030203ca40d500000e6455400307021565140074214001ca0304040019420582807005150380000c03098051141c640201d80e0599890021078200d21550f03400030b4215020a030b980084a0107903102d140d201c0006480a02c4003030702c000004003200c4407580c05110b41c085104200d03051184003e804101440c207040104813080c10014040c0c903080071584400105a15010a01034041c0c1c0354040d21003903c0d06108942d1101440e06d0b19504e0040900b000340020742c2102c120302d6856100d000c80503005081d280103000c005c50103880320301d05544444410b80310782d0748 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 279128084 1250 279126834 279126839
    0xd02030a051e070c0501030f0b1f050c030a020c011d0f0f0f0402040e090c0a0305060112020613180e06240a05180702010e060f011203230702010306051503010e070504 73
    0x1900d41c02000703951300c40e10700864001e0400c8000760884144511840d1041e1074032180c40c0c0b5544071700c0e01c8001506103002e65000d050048007012169445107001900d004c0c0800301340c600c41f035038000a200c54480c1090320342c0d1452000e0791903104140c55405011039070003a40703402103240c10704001401c2c0141071000b5103d001c02e1507403480410b09036031082d17000f24407101c0c0307601c100704c0540000c2c00040c0018200710f0f120b1080516548031181d40710810301030080000b0b00e82245204540e520000c41d8000002c40c002071107001e50b151000d90388000c0c000d041141140c20050010178692000c5101d600c9840e86a03ca0703000000342c030f0300802080d250341c54010382004a182c00032400b550350048000b00c43c1e1802c40801918601960000d095640f2202c200304694404401d000a8110300412a415210111402d006868031410119800408004014004540c04401002c540c2e6100020100c81d800ae0701c0a1164640d148148038200a805491440680c41800140b007038038224004150429802e00d40f00b808c1a8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 279129334 1250 279128084 279128137
    0xe07080d0c0204060e04050a0b0a140f0f0709030302030a0c0303020d0e0a17070203100c0e041e0e061005040903050408160312020d0c0308090a050709020a110d02030a05 74
    0x5540c0342110000ca80c0d904011001c41c5414000d10021300889007112000e42410f0b03807080d0396509030100090407000c1c07402c00244244950790000f00d109402860740340407414a01c11a00e44a00305079241c00301071490400060314580603646400071250b05d980150b180404500c0110380740700d000441101056000c000c00c6000480e42d0046c0c1200c9a895800740600d10035519141c000080d940b039840e0080c1405020140241c0d03004504d000020704442004100010f4945040ba0000c040e41225540540b901203804000482840141c2041c10a01004c21014080440e050b90354032003101d607110f4155115805101905140d0091020248607040443c02e150b01c85080900303090514494107090101020208144406c400f41d0060798511400902030340190307c40e000713145440004003d0180051100410b0038850108000b4141d9504002518012611031180a001c0d601041e4180001039003070400a81000f004070340000c100e1900d030021031034041c0c000d0080e071706504940d48228088040713000e50394505 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 279130584 1250 279129334 279129343
    0x11091e010e090705010c1109070e030109050a0213090b0408090301110c0c15090105030703112b0b100804030804051504030c020a06030510030b0c07140f06070513090e0708 75
    0x3020205030320721451400d03801d540d10b070160b40c2d80020b0401c001a0713071510100d100c0e00317030484041d18161030000031a6501002911003400550005400d5803801d2004414840045124655a03208075540d01d00303105403200d01010b60b0f0002c1d00140c030400300c0001142c00502a0350091444440240000c106004507400c0c0303580c01d0f0070480b05d80c0c0b80c44d081a560281c0c00e15040c1c4038001002040305000d4102800940020900e00004241d0400e044e613a6000c40f1109081500f0b179400a44811391440c840c8002080c041c9080464100a0304414101000001c140c82e040c0d928401c80540ba070743e45200c0d941c868404581a82c00a001610580140c041c82546011040c0b25148214002d45464180d4020362041c82141d020950024003014900402d10030102d9a01c0a0760045039040650380040c3e481c0e050078040e05104592001309084540c0c002004c00e10000315030000420303024015140c1c80c0da40e0600640d0640318100e1924009034828100340700f80c0d60f07d40c0c00014080640b070205c5584688032490980780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 279131834 1250 279130584 279130589
    0x60f0c140f0c2506021002070309090504060b060409020a031a0d0209070c0c030b0403020f0c1003020915310303020c13140a020c071e05010813061e05090a11091e01 72
    0x80e007a81840344c1ca4041042c03c030482c0c000074046103880d2041e100100b038030000b40a40c20010717403104080343c10700005821a40031803100074080b41e0313075035a15580d201c029445034085502190520b0f1245880d4900901e12848000028241c0c4002c0001c0c2c1c0d0801c1b00f810b200402c51018004a24022000309a100004001440c414101501c0ba41002d0902a03d07101000c0c404010139400a44848803e80b240386165105004509000d6101c2c0c00303e500251010440050f204600c0e040812165100f000804185100c0c9007021440b21840b0030095080021200b240006809a40500710500080c10015810084440041c100160000401005040d01c05003520322084564020860000000781441404014032207604c1445100404410200e01c2c40f00c14825107040c002c0740750014040000c281414408039901c10410010800c0f82c140050000340c0914500d9013032480d080014605000014140070982d4011070318269142d40322081003009031f401070814254590900046071b610f05c641440320701 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 279133084 1250 279131834 279131893
    0x607030507270306050604020a1413080f01050109060501081e0604020c0312162d030b100513120b060f030c030109050318060a09060e0d0f060f0c140f0c 67
    0x15410f19506004060352000b0748401c0c1308920402103c000b6540041d0381c90303040c00540b2184e039203540002031221104606644802058010141c100042980c1980414182c4107040b9040003075030f45a074011503003074030110f6100c2480d89028410b411480d04080ba190740c8981c0090016161644444086080d90000c81c4c039504248101410310007580e03041a01440000001c3c41c012202d401c030b2851f8041208000c40c08031425540c0746005610301c40c402e80005222a40240002c2c2c2c8480350f002c4018025801a0105400c0007c40f8901145084001c0f01c024102600100705c450300352601e50420100b201001035155140c8948030300303852103403000c5c000d81c4102c1e80180099511400710b04101c512200200400c244211020000c0d8640b01c0e410100e510296001d6160403101d40f245540442c0c0302c26031400015040451080ca031801300802030f000a1401c0f11702d4202131010f07090740201900e2420076020000d000d04400d0142d0010300030b111002d4641c15a034482161105080600918480c0413034500092 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 279134334 1250 279133084 279133157
    0xa09140f1e090a0c090308070602070507080601030c080c011218051f1103220f0209161b050c010c050102090a0b070c14060304140f1c020d030e0607030507 68
    0x6000e250142030703203510400d190070603c2000200e00008045c0c4446000041c20400702180c6101480f200d42d054802c2c442c0e004085030205503c44000703035a01c5000b4031040b80c1c6020784040109401001050b60030074a035068603034050341701a00d20307020080c065100c80c13040c0c450500d1407002c000c83c0b810080260b642c036400c1688034507410090304460660745070340e2036244524404c0080c04940c0c1038407400c281c41c90f20f81c6417200908009a1030289503c41107004007035842103046003841b41d070f1020f05035004c05182c00f03a10b80c0035110b030402d00070200344e411004d0007504903000446029042c2d4000d02c080025a8410800140f4081d0683c0008954001e02c1e00300d801e4420000c5602001c02203d40001d00260010107210740b0100e400740000743c503502c0001d1000700440c0840b00400310100c41000300700c0c0c501001400fa1034049600c00c050006102d00c5014800042c420301c035035916024042e11918983c032110320702070301b4699134600d02a0041e050140c00c01c0c0401c10f006e14804601b20385450307c0914a050131881a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 279135584 1250 279134334 279134389
    0xd1e0c0207050406150c05030c0a150b1909050c091c02032802040b04060b03090622170f070507060504030b07030b062a0a140d03020a09140f 62
    0xe140c00c80c1c80c1c0285002c1c40c50150103021041490848410b095810310b440401102030f45042801d48c0101c540014891152079610010000c1c0007000020070260040c3c00c00c05a1548002c0119a2003451a02a03248032418000d100300103407500030580c000d87c54401c4903d044032a50200c1c02c5000025903903014181610004c2d401c62a007400140012151060414010100e40240414030484184001d2049548003000741c05611b4036007021000b402c010310010b0322440d1000000c2c0c2c88c0c110403507900140e404c04c034041880141c81e13005000a006d40111110701ca01400c140c0220301039026500340c1039441c800748098000554100b0070080a40225902e182d1a10f00c4d501c2c28200303e0700054034410503d82007010055041d103900c1c05881c0c0120203a402002410746446c026269040c40f03085d40f00050103020181014469000b200b00c002000c1036007200c1c08800c1941c0114101e0051204070b400081c0c14000820240c28200e142100d1040300610410400303c1520009002e02d9091000c16402c13a5001d445 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 279136690 1106 279135584 279135587
    0xb1003020c011e0902180c0f0706060b03010303090306050f13080304060605090c04050a0e1e1503100c0f11101805010507020a02030f0109170d1e0c 65
    0x16030f601503240503904005440c40c51420390280d43d110070701e6500d41c0080c5c980140301d4442c0d206030074100045000401c00303a6004500070385046072641000b080900507500198002c42c8030307803200340c20b0750f1440c50480140d8900500850706214081c040040b82c5041242c0c0c10220b9601c2045956255541e25100c0010102a002150462410000c0041359900d0000800a48104603581901c05954021001200100310340e050400c103c2e01040c08072a036a1f2402e05030300b20095150102c84884100c004c070303140603401040c2c0c44200c0c1d01d9604281283d40c03c1140d245401c419450403001c0d080300070380300300e0392503603803008d07400143d50350b01a03940441c184299101001c943c8071009200e1070401d600000d50b40c40d00414143e1080c0241200581c2c152b00511070361501d240d00217060203403a00940d4640a17260001c0b14024189910f54500b1045e9041d040030008441d00d48440c0041c032881a85070 = true := by decide +kernel

theorem cover : BRFrame.Cov 278956834 279136690 := by
  have h0 := BRFrame.cov_init 278956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 278956834 ≤ n) (h2 : n < 279136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
