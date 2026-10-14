-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0717
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:18:36.052526+00:00
-- url     : https://prove2.me/submissions/2d415f4a-be9e-41e6-9bc1-3695f2734982

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 128776978 ≤ n < 128956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 128778228 1250 128776978 128776981
    0x10e091605070302030d021603021903120906091403120a0615110f0717010e07030206040e06130c0905090601020a02132c01050f10080607030903050906030403020a050c0103020c06 79
    0x201941c86810401d011030641c0024001550354104ca0f10140604000c000c01e012071003a00c500b0080c1c00c0000b10411310703681c5414000300c0c201003500480c144555404560740001c49004a00b0120020b094500307005001d0a0104030300140c7d010000081e010031022803020305a150cc130020103038201c5007640704a07090141c406040022450080c5a45500c04103840706075046014415510b5082c56400d41003055075519504800b515500300b4401c4503600e000f5200244055401e580015501380224410710500510a00006d51941c80310b01c12203160b4040050b0500134141a624060b0005080340100303070280c403041c0001001c0c1d43c40026400c60b10307500540a03075004d20001000401601405984143e5440103050f0741d810046c240031b152828001d05000082c4d18101990450023516000e00001000301d48074009010b081404601550000b9642c00d000402c85694070741580c51b0300468150590040010003004103254011417022000c1c0d205200307844030120050b0054040f8011420030b903140c0e600040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 128779478 1250 128778228 128778271
    0xa050a020d060b03010e07090c050a0e1912140d032306030f0a0302010603120305090d0503060a030206070614010603051905090f030f1309060605070326010b0405010e09 74
    0x101c403009a401014041411000c0801103400c1d96a481c40380c2c205584100f2003009210018400c440900340d1510f0814648070b04020010014400c0f00409031090514100a02450000640040c000c0c030f006000c6100905190401c40e40300e62170300a54081c0b6006608424106510900c1814801d600700340c01c2c48800f400520848421440080c4200d8151250010310351206d1030801c514808103119900124290b8150701d818180d81c5030502001c400e25003003a080c407020020104840e59602064540750752a5642c68002030030300380080d0b00181d00040006580070034001c02d500558880e862000301c0c1d01d550313641e81004030100c0d030048030b0400e038455021480340440c04194110fa0b8103c022003040341c15144850003160300755482034030355565a460004000104210004007000103101d0b2980c1000f81620301345014107a03100e041001000c015061039503551a140312968899a0304600e5640051581c60f03031125001a031040c010300e40825950034600d03141e440c008540c58801e80c400c03500c42c5000d00c04003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 128780728 1250 128779478 128779489
    0x120b01090303050d1d0c0301150317030c040906030305041d01032409060203072003030603070e0720060a0f050c04050103270b06010905010c11010f030b0a080606120a050a02 76
    0x4d8140070100d5152140c180d840150045203a00e600751000151051340e022000b01400c40c4d50401045941668400003000840c9960030072140c14040c03450305030b176a9522405d84008900c070780e8005a4440303203860000b20034140e00031f02a00640e00c80036548501c0185c41c291700848030009110050a503031041c000d0135094403600340b00c2082c10b10a00000b00d40e4107110f64031041a42c000301d40400000b1402e46604a0381480011030311038200d13944014614504209012035201c80003805203070320140b880808200e0051040b500f200782c20301000720069078920140c0645031620300c1520300030011420940f4400ca031400074440e2a004502c054035280c81c017441c110054000c0c1442030712034000c001074140086030b4902c0800300e580459100d810400d00070302e082c0c1d00243c10100c0ca500490b04101414451500040949410740303c40c180900300f41404070310022045001c0e003950b240c26130704910b1951000a464000141e01806080f00303c0704c1c0d007a0070141c007920303030341d1080c5c520310282240d44090000d00c0541410b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 128781978 1250 128780728 128780737
    0x10f06021c0e01091206020306040507080f040807021c050609010f060f0302280905010305120c03090114130305030d180b070503040c030605070806010f26090a12020d120b0109030305 80
    0x43c180303030a4041d43d86171040c0c04e903440c144003074980c07680020400c507482c81d040c400c0d55030010060031b12010078200380b0b507060891003000704010003400e8005081015560303030300c1c00700000c0460744e442103405000502d059071b1a208113442e8030540e982820780c104421410750141b0403c1d190b400040403d02855902040b204d518031145800c2040c048003216030f585410500944041e022803203000c0743d02e525503d0001c0c508520510b508542c002c0c28420a0100480401124805030003480c1c904180b421070b201401d10380c403400585201074030b196600002000130100107000410400c41c01044075891485060151b403002200041a42c900c0708000317429140114091504203008d81e070b5030f0b64155202e507644000c40700141d5654011440b00801c114582da070004440b03074000240d14010760b140c2c1d8404480d048030f00c03006608444072050740c4001480c107101000107612a50300075500f80310007020400c0281d15000074005410005103201c0b4000039106090055070249501030707660022a03813964038211082c0e0403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 128783228 1250 128781978 128782007
    0x6010501030c2c0904121403040b010b07031205100602071403150a06030203121914090d020f0604030f0c06020303090619020c070602160503061015050d1103010f06021c 74
    0x1407000076410f80340c40d03a089551003184940d88114441e000b40c46c0281c01e05110003481660807404004110024904841190458040002440d245e210600c0e081d64403800c0c0000b0981e6040c6010200301504480d103130040708660b1035801b510b101c1078450048401080101003219056442240b4620034090344201c0c42d58072003d40000003501949039130000703003064006010300524420229014031203030341517800780038003810a007082e1281c0005400700c1d40709409940c800501c246900c1d8604c1c42551034500c18660140b00c0100515681c1e03031207103440128003044c803a0a84409105c1711010030b0b101e00010482c0c3c002c03805d21004184651b10703d907402041c007403641c3c004c5d22202c1d003d00c124240c02c1800c00c041d4014040540140c41c00c15200780c030100300314050781d1180c0d100ba40868184030700b0b4110203a5203020f4903c43c402c0000020380041090302c89219141c0c1c0c1c8500c4526100b42c0041180044001c0c0d4165031180c401c145149540d140e080f6030754290580400c107005003801d001b11800b40100f8610007c2507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 128784478 1250 128783228 128783297
    0x6080309090709080a030807080603060403020d0305060102150c0c0c0d0b04060c0903020603070807031a010c1104151202010201050f0609130201031b030906061a1606060b040b07020306010501030c 86
    0x351142c00d00307801d000100030118041f840e41001d000c00d16820000c1154458026070040c1700520342030b2002076131044182c080c401455668000b040060340300b800030b0b10410180c200702651031b0411142904040d480030703001c480d07180500300f01043d030f40c5410b4800003410f6401100d07000a688460701c0368001130a03840e91403018003054400000042c0c50b190080e500c61105512031544a01d000c040150a9407a020748940e48100707920070048003aa0852061010190054117044403084242c01040040001c11905484e41c10f000d1400540a40217640511046100780e00030f1001c0c0d00c850b0b00325032a1500c1546e880350311211500c0050304c4082207182803000d81d0f00525000c05ca070144900c010301c0e80c540414079000020f444005880620201e030068500604030f40380c0304d503c3c40c41c116400c00c09a00814045010706400c512050b418840140c009030041c140340454642d030703103545603425032217640164003c82c0a4080c100000410358041e1041450300c804540b00e14003c80140380342c845044185d09043e0540a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 128785728 1250 128784478 128784497
    0x150f07090e040609020a0b03090304031506170604060c051207080a1407021501050d0b01060f030204030c091a0301140105040207020d051e06150307120f061a0f0103060803090907 78
    0x70040300071801d00a0b4080c0340009525000c80c0144900881c1982000114035810800c0c8145400b00104680032203402030111501c9005010b171303140203400140d202c42003001a103400c60040701d0012624500441c42100d04100d6403002190030b444600494400f26110740070b940004200074040d01e640c40d4402c0504500040e5680748003c2e43c400c920042e2011801039009910209100d0300d00524280500000c89a104128202f581c40d800b0421050007880c082200c40140d003c5084d02940559000d16409541c0c000d0719902c031205103000b040c10702101400410342c61a000103d05040c41111210440d60f5020307002c1d6820001400b01940c802c5100b260080a00403082000c201e05002c1c1400d4045055142c00038085000444d82c41c02101a0100c59000510b020a42203036400043c1401220070320544083c82c80d40d5404c041452040c01e0708003038441d900781420070580e155002c000181c6135038100d03101035802d20048011800c6130701500619410340d000300540052441d000381d40d1740d80800d1034030300780e100c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 128786978 1250 128785728 128785739
    0x20609060304050313080309032a01032304110f040b01020a11010e09010e0a05060603010f0303082e0501110a110609030309100201020703030f0b030312040503160c0e0702150f0709 79
    0x4161495002006d207400204180c0c0151409201e01501e05081c8030b043d818881000495080420f41101e0007410300d5500c00d502005803894a101c01c075000003040a401c050316041c00c101d4034404180c4822070ac58030061900313108526080c03185440d8540d041c0d000b0b2441c9031082d5182c17604e80240144507418005120402e800f240d96001400380a0541e810000075a810800349030400c4e140040d00061060f0800e03c014000f10904900800469400d454a001181c840803c00f0001d0011000e0800a01ca6011100e681c12181c11211004450b800c0c0d8a01a51103010300044c0d07100c501d503c10003440c074050702d4510000c61a240d000750514107c018280c0307143c000301700700080c0e001360000034210140c0d40100300300d401d00d0741504c2000100030500c04203000301c200b5040085e80307074405c00303c09003c61140d200205040c03100c00c1080e62000894a1301303088600043c0d0a01c10b0f0484807510030070076a01405000155154800b10f80c2600c100c15052942e941d503180e00000d09540c103030007080030b8200140305000145 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 128788228 1250 128786978 128787007
    0x160f030e101806050c09181918020a05040e0d050d0b041e0b060a0807050a030e0706050904110901020712051005130209060102011a040b0d1505180601030206090603040503 75
    0x1841c000d00b8842090708611460701405a0b8001030000e52209410710103071409440e101d070281c01c01e9401550001940c0e40b804010b0446c8101ca80155509030b241120b00740d0108040d0200e10380c814021a0f5440340260b03a001000300352a1003021401c015001100548011030051006d868a04119034000c0b80c0744500ba404074080351091000050790902c51750b40120001054403580d010391205540f02443d10401010207840711401400b02d000300840014020500e5120380e100300d60001100f0252520986e61701c00c0108150412800140305925010002100c011446c08039400d0380300680161000910703113210aa60681364560070703500c5c0e020b2942c0c142400d00d0244035030741c411202c403031003e200e10481d40140461010014601815689045402c41e81d40418030455100408200c5c0c1c0032603076041e0000840c2c2c010002c0d0b400103084151107410705041d07145a800c881d205281042c801c00101076044885079880500707200280d00540100b001c100c644c14500c0c01035512078000c0c01201d00e0443c1e110050b05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 128789478 1250 128788228 128788241
    0x90c1e21070e0a09050c0f01030209030115150c050c06070813060201020304061a09010b0903010b041d01200a0305070504150207080609030a050d05040c150206010806160f030e10 78
    0xa9803a00051018849a0148070142da0800c103440004c01c1046001c0d500c10341d46180d0204954031605003104c50f5005a84139404035010003002400a0103101c080c6007580f5050307034031030240c00c41e20041080304c400c0c010b2184050010701c6070420b00030042d4070340714428003082c1d51202a040d03030103e100300b0912105003034880e07480005000b103a00050f900c1c5804d0424108848541041c0c03020301c00140c0300300b080c2e41c0c1c40303003c014107466568100940d5040d130003002a0050901c05d02d9640c200d070502952004490040c5030542101000e08020b01408100c0b0050800c207043d030300f5a5048404040c850b000510b40b10b40c2c400c44d440807403814500d203055247c211000c2c010019140c0880180e005400074005690144212500070582400030340c1023002002020b44103010320301d404912103a45100040901c00c01e0070044000b00b4108100c4006c1d80510a4000c1d1243c1d024010180184925004a21481c403120010240e45190b584c40d4164502401822000340c0140d1340c403d0003a00c21007016007096515072141740c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 128790728 1250 128789478 128789539
    0x1b04060c030f170f1906030b042105070303091b080610060206010803270901061e020705010c02040b040605091303080603030301080d050304030512011409090c1e 71
    0x31000c1910301e4001c1182d015840c2c0310040103081e03209020aa5400440182c01c401c964403050225030300c001c00d03590070741c120200003420182481d2002090010101c0030380d0180c0c0c0104005803032503400d1801c08101c80488840800008c004024507800f0031301c264828020b80e480784151250f4041400075100d170080303e0750040f1009422010a02c0504014400408010320450015152540c500903100c0e440307005180096004030090704003080034180100703403174510001c000c1003080c865840e210010000004691003000c801c0c0040702e1074100c940001602c004540c4142e4900e1300c0b00c140e907401e00018105101d06290020b4481c03502103143d94441604900ca004109500e1a0320380341414000c1006101601c001d000c1d030030410040c0401c840104e036451001c0841d050031aa2502e1350b00e4115880d10071413101c0c456500d4110004580c03030140c00110302c01c101e001c4030180c1c06621034000103038943e0440650143d0220205140e410821000c841c2c8018a12009260490b1704801d0405d000c3e2003485007400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 128791978 1250 128790728 128790737
    0x304080403060c0e121b010c240203060109140d02011b0609060c02070f1a03180303190b01031a040e03090d050102030f10030b27030d0b0a05010c020a05091b0406 71
    0x1060581801259010303145c034480000c000095028803410100030104225a040102000303007201400709074495896101b500d4803404c4150a4151130b140002c3d00141c9105000071305d181c0717000591464414034940050001080095006c11660041d20140a0316207100801c0404140c3c00000c40c40724031903d000315010f107401003000c1d00e012100070300b4002141c025210050614805008140d007408035184c00360b030743d180740c69900e490f1440054040b01034410210314503c00007081000300880340615503000b0581c02000c0c80000704503070040d81911141d81c103e411410324498411505e2502d508801048510a41900d20b41b140207008180c4001c9040020340d072a030340000600103901e10588100ba03000310b8140f40ca404080c29650360000300400544099110071100000006042c44442045c5070411070008480d6184c1001c01e191002d090740030050741c0700c1d0720003400000381940507801c84491158010700340d01c4000d083c4000c00c5030800e006444400408200b4083e006448100c4005101070a41a00c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 128793228 1250 128791978 128791997
    0x309080c0d0e0a0602060f0901180c031205030601120c11010c111006030203120a09350d2a0609050312060612040f02030a02040c0306090b0301020705060c0304080403060c 75
    0x601070304001d10101060300548003c40b040000d56404107150b908854006401c600315220031209901416421060f0f0541c06141412007003004207200314101103d10450141c00351002c0241e040d2004d0000300d90950114025490704451030840d40d0141c0d1514070709041c4900304030006071002c0e0841c1d51000d00d6101207020300091003d0400c0c10414803004401901c030a01c42c050959001c2034031040042c41c0c03181c841d4004180903451741c0c0a402c03a03074007805100210b6035484500303003d1074043c200c855000540e003500030080600d545001180e00103960415407295040a2001d50310711000e0031300d0854854014003455980e1000600c180035508640f40104021501c6154241240c40040f0740a0039043c840c000800180a0501509840070380c13107500074407024608130460000ca42001641203009512030318005085280301d070940e000c64141ca8003540100036046411007858201e02c120080a03003d6480078001604030790700e000040d81c0c4544104a806d00742a640c0d9a0541907030040240e400108065a9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 128794478 1250 128793228 128793253
    0x10602030a09080729090303030408070318050a120309091b0207060306050f040b03010b1201021b03030405120c100212150628020102220e0609040c0608070309080c 72
    0x84800024080c0600900003d910380350f045c02c00b0004000b424403482226003070080c0160031802c241d542030f42c800b40660b607603890145011051a0b00440c404c0b00421010410b01c03105405400c03480303040d10405002c80301441c6c2060a440c400c9001c03500304904000e406c040c04601240e5601402daa24980424807090b011200c4801905001054110508240c9049001c1142c0e03a01e4101c400d01ca580192b4001417451001d0000c24007402c0311041c002d4010380d02c040b0070007803c44154010186246122118800c000c0d0725801e45890b0312003034030045d00320b070701104100d9510b1801c03c0040a26055400c11a0090404000311301c2c1a60844822858003203c1070040081e03804d00c46805504111080310744c0361410700c1d0115031420520501202c40001e280703140507281864000d41c11614030001e405064000f2141010000e518020385005450301100c0240101e10f00303003403000c03226000d076601c40b800490729810301108990101000748a0802c240d00c40700820041030300c04004040c180340c200045c0c50080d1501c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 128795728 1250 128794478 128794487
    0xf010513081e0f0d05091005070b0f0604050a0216060b040b310603120305060613080615030d080a1a0409060203270c0402130803130806070302070b01050d030215010602030a 76
    0x810921143d6003003642c3c0034001c02d501c1401c44080d544216586012480c2c090001c440d070f401001001000840b80f0b80502c00412030442c08a4820301040728280300560703422040009078080d560800c103030103192080200025600340c21070b0820580c06030000401001600000c1c004001c280448030040d55030140400b80c181ca00c42c0e010040c8000301605100c0342d4510358524445800615005040640d00d0011440310b6a0740ba04899810190030540c82040d07842c0c0c0c503035589402c0d065503440110b41071040d02c0780c00e40c10003284003210b00c101d9807106036203a5101c1c40e240c005081000307046110203100314030710385e8a590380d8032810300c0c41405100d0050316803902d50038441039120003404e003803c10501051824803581c0c0000e04550012829603001d80c841d21140c62000745406143c00004050000ac540d025030980b02c2c030031240440300c0b2101266016190080e09808a00c10344c10050442c0c07030010018001802c100407101001440b901c104c40c00341225100103501020283c1110006810020303c2c510040e070700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 128796978 1250 128795728 128795743
    0x30403020d0810050907020708061501030f060b0417121b0d02060402061902011e02090306010909120309031e0f0e06040e01060c080d06030501020403200f010513081e 73
    0x2604000b04281420380d5491401201d03440344921402c45140040c81c410f100348864401032400408860240c1841004042c0d095096001d060019142c4420141120a00c0c018041143c032000306151600303051001404107482c2100c403011403032240c10445410501610300400f050401243c418140321001004941491810103100b41194420030601c80540e07110b104032102c15050403404120300807940000e0b40034001d951a083c80e07032101c4100010b2180a0354004102e081c10131070030b1f2001c0e40e0321000c15404075854400003500c5100c120020010b568040c1e03201401c40c5009082c1110107082049a8030401c101e001e001c0030009803402111135201da04036813040c1e4000c03c210f0b4200d08082c2058034030384080c5c605128890030090300c100450b060101ca40308960340340c0314420050201a4403800c2c040d0203544140f100306c0388004650031440408510003a0121440001412000c41c04554001140c280d00070800c00c002c2840d011200046840c0c1c10080074011019140a2888109542c10940d052180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 128798228 1250 128796978 128797003
    0x201090210050309010902060c010c092903070e0913020102070923270c03120a02030d15120515090705090c1c020c0102030405010b03120901030902060702030303040803040302 77
    0x1016202001680d42078000d0622454518200342c8030341da40c16840f40900007400e0003a400031000500c0040001041d08040e42c518100d13247c4050355540d5080c1c018110761442d40401d01920000c440c41c52813000003005680005941c0391030704004a03400c0c0005c884490543e6845000003140c0700d40e104550b010300801d00100b001640c100400500000100d110908225111205515180004804030b00020340304104d918000c1c0b62101502041004956035403c0b0f505083c400e103c0c10302020640742e0300c2011941180c40c19400b45040002407110345c0c01034001c00803140c1070095503000c0031503011690581c8800150140c4000c00d503036491705400803012603000d0007071203940d0400c00c000e00c05511200c068a070081714506620f595900e8500d8540400c6c001c00c4d240894013030001580003401c1c030054014600503400380c0020801c0b600610100350752014481001540d0716008d01c00b1209542c041c0d070058603c07600203004903107041025800242151302c1158208c0e1504e20106c1800300b45941000810b100e0f00703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 128799478 1250 128798228 128798231
    0xf090212061b0309030c1603050106080a080406030e0a061e0f060506070b0c09040903030516020d120f060e090a0c150203030f060105091509190e0a091406040308160201 74
    0x244400c182d02e00c0540c0030318180340240c0000c007144110702d08008840d448010341041d60b09200c1c12150398550b001c80ca00c001e450710b40c24104042800c00011070102c202c6540402d01c1440c1a28100c07059020b400c4c01c091002c00b9010304614a03010a203240514031910032042030103c160002001c0e44000c68664030601e40d40300f45030600a10640c1c0701c2e0000c444145400821401c0c0d1541e80074042505031140c01d003025002403c04030803d003015015003000f400b40324004446003029445100880e91a81001a42400a10740d03590fa40140134043e4020701480c005401c01150003515220407001095060f182c42d205540060700500601c0805c41503040940100048030043d18000700f8000e50b43e000c0600801700300a83c140100390507a008200300d0f50854806071180c002d1400c10100c442c1ca50300500c142c03e01580104034081e40b0310145446071401c3d070b016240d60445985402206070700070001d0660840d800c043c40c100c0f03003c214204010b5030384600e109588019180c586481c1d0110124501c265050132740e07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 128800728 1250 128799478 128799481
    0xd0305090c09060604031e0c090510031202030d022a160306050a1416080604150e04020a03170c12090102030703032a0c0b01080a030903061a040f09021206 68
    0x38400403920030742408046620402c01d0b1141400500300d03204a500c020200c0700788032600003111980a01418201d4083c460210f0308541e5008044c00386c0358121104141c800140da018000900a50f030300094440c0c49c3d05c102da0a240300220340b02d049a004c09898000704544c0c51116107600c0120b070f0780c3c85014050002805030601a54a400942800b9000041ca003944620001c0e8070780ca40c5a01a901c0494114a182c1c000d0070082400c00c8004d152420708000a1400c50004400781018094400003400780c1c040e600c4818504200d620309100060022a44242c10f20301c00404900c50000394105103020890041d5994840000355240020a40a050a07564240121869070380c0200644490f142c2504010500b10450010024015980b0341c640d455540c280b2407161080340d0001142049030300c5548042d170707140d0b04ca5100c00c0e030703030101150000c1c00115191028000115030390007164015030751480042282c6011000141640d0340d41350011030b0a41d44a820f4401d5142c40c91110030010703079140c0076102a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 128801978 1250 128800728 128800741
    0x5070606050f0303030c091c03030b03100203130f15020a18081605040216080a02070617060603070c050f06042f060901031e0f0203060a0f0b090d0203010902030d020f0d0305 76
    0x5034000101b800e003408801080541440c1c0324190940c0d110003c01c95450441c5100380b902400414110707003002c1c042e07ca00d900c518241d51191084901034100280501089100c039601c6d940c014054482c12078050300d4600c00115203071214000743c084450143c03945140c10580c035408594840c0140d12000496008101140301d04100c11895401e4a40940e0056903911000da200c401302e40740003600810f000d00c006040308965501048050603134a10355550311214980f0822092140003d0747c03603503400601080072884203401013282d42c500900c43c105582c001c06212013610300300101114150b034800c51505481d0640c5d000b56001e001d00c2c070780b0540c9034102c0032040f1011840d940144108241071590b9904c0c181884280360404011901c50440144031803003007440600c020390401d03101c0c0d40c01810f2050000c80d88035140ca0280b01941c2421904a003000350132800c00004800380310099070555640c503250005628140260240c0f16210340081c809000100010b80c58100544002e404051070030090025 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 128803228 1250 128801978 128801983
    0xc090108060108040305120705131a090405190c03020403111f050f04090501080307020f09040f0209130210080415090b01030821011211010e090f0c0c01020a05070606050f03 76
    0x10442003e103441d45a5680c1c0b49030a445074850951103641d029022400c006880b544040180005041c518680040554801885021002c0c5d2800c8a0b141d001c01e21408019040c00d52055510a135082081807076241c5911a080440d404200400006500000c05009001049000d11410f00301610704043c4498100c0d820040c550001298108008000401c045001294400d4a02500e40900c08200e9965540070880d640d6100e0036080f4000c104000018801c2d1600102051080350030540300b0240340010790802c03440300401041e107010312101e06600c8000da141c5d0000c42c4910300982d103d90920b82040d00b032001c5a800030401c0d500c0c0540c1011900d00c00589440032690450b50312095043d2146480100b20308442d00d9a0082d0101030040400040e0a952a02400c15618000c20790001220461001143cad122a0007103810381180d00c44011401522011000950060b103280055081220300407505082ea402203046c0c0c000604007040107401d10000b40b08010041000702c1d01744641e4810400802d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 128804478 1250 128803228 128803231
    0x804031b0518040f060b03161827060f02030403030b0a0f120b090a060504081e0f0a0c050c030313080708010b09040201050a030608060c030a050907050a050f01020c0901090b01080c090108 82
    0x113010070107824a260070802c2c00e0b080001c1c0a031b00282900d800c01e80890b0072034484030321442071003101c80414560303c1981da83d91145003032001c412050800d4208a001d040780c0c410245900840318207569000b81d4050b0305d1144007550080388a0343e004101014141b00b08161540309400c81500c0c081149010482008802040d9034aa0742c0258600ca5030341d44c00c2100c03030900458020180c071803402c1104010030064140000c210096882c0c60710100405008605102801140700c3c07501e10445c1003005400f1280603406080344c2500c90b0040340c83d503100d0500400e0541e041113504500c0340090746401e1107100030601c450300140140d24002c10004c0580e8000076660700020740040d052110003d0700240851080d0001000b51070b045040703036800d040620001e440ca510407103442500382e10302004544041e50105442040719401007500411034185401c11040e86881c400590641c400e0f440b0f040201d071181901a40208002880040e6550b5501c0003d80601b43c014059003400b41c0410503500260703080140c1d10b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 128805728 1250 128804478 128804483
    0x12a1101110d050319060510230423040f06081c0c0b0c0c15090a0c080610030206030711010e031b03030f0a09031b0b061f02120c07030804031b051804 66
    0x240041e204600c0900102031070341140d038200450306040c08410740c09c203d0889904103818000000b00030020b20064290240b401080c00c107003202114800c9018607450000083c50008000048022800c18050300b20303580d0b41d00101c4160410b50340c01c000501d210020078039a03e25410003500a100319909e440c4602230090450310410342c0403681c04041e0408100365000c01111901e0143c2508006100710f645480c221803c417182200440b0105101c00040303011405242d00c50380280015013142d08210301c80c2c00081220b002c001c1882100c4842600034001e90104502da040650354881400703221500e180c100b800e11800304d501c2042484100b4040d81c4c01d403a80207072000d10025800155250032503040203001c0302403412030720000d4880140144018224040d0500f00c03020302c21466000c0307004c0b003100d5100e06400c0158005024101e200b008600043c011603081c00e040c0c50036191295510681c54001d500113460000c1c641000304489400c18542c100a03000c00c481c81102d003000748188181c20350006000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 128806978 1250 128805728 128805751
    0x20a1106030903041206060f120201020a060b0f031902030f0706051804020d1a0415080c0904140607050a0305060105030402060405040b0a0f12030201060909050309012a1101110d0503 80
    0x240042c0000d02c1550003600400b03000034428581420301c207010b44002e018040e1400c1030020f000820007502881e2440440c0d041e005004406002c0d1241c0c00201000005250072070317039000e8130711aa982e0900ca00350b040c00755540302001e0503203035005040c901103d09a0346003940d40702000c00d1040a07040700a60310400702010400c5001c0c480c1ca00800c2c060302030740d42078800040c2468070510340c104d44200d405d90700d250700b9901084040725070400c000214100748a8807007103421600d085030080c208a5000d5501500070301c8101c0012114143d01d80c90905c04491000002e030340440e501c04410fa16008554000c007091816a0031405d058000074032610a911909100381d989510a620540340e03008003400900764510300c0410742da0b840901804407a8400c100710015464041c003c2240416445404074998210009600b0034083c4001522403000290343d0300204686e400010391042c03280301da61886103204140d00d1000c4a0740000140510810035078020864106c000526002c541c403a0580c1e07030018103500c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 128808228 1250 128806978 128806981
    0x201020c090907030b0a0b0f0a0506030a09051e150f070905012604060605100503040b011208040b130302010305070f1d040b0604030605041e20180a0912020a110603 72
    0x18600f003600c1d88001d107045401020408111840d902c20205035406481041203a807100d410803a004115006143e44903005002040a000445c3d000c128418406c1d0120741c20500c4074042145042c1031107103002c2407a03000c10007076048400b070002c40c03a0b000b00f4035010441650800e16030185c5400d506018060420a1000c00c0064400d008902104610103000cac000300c103420941400ca0103020b050207280d0150f84088a498880c0b80304408a0327200380c0e0054010f041d10303400c002480500080464050351203450500c400f0070380e010a0b8008202c0b03910140da1490583d0300c1c500c005001c0c2c40c402420b10050007012210943d17480d4128030341600550b2013034001d000d028007100001d4000c0101000c1240c009501040200801100c1da008900450244807000e4445040c1090140c1404036003400422195405c0009180c0c2d08484209500c82c03000100b941001076000e00d035491400c0001c94032800000e4403440d1000901801459100c8524941d1020b05180601a1549050705400c601200c2c041d100010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 128809478 1250 128808228 128808241
    0x406030c03021b1c0906090b1b06070908070e07051204020a080d0305011707080a030c050a080c030306100302160b1f0f0906060207050a0b1e0a02150f040201020c09 72
    0x141120540c00030150002c42d00f00143c0c401c60780d5074100c4599124115902d00c00344044034041d1441c4030860f00700b6940e031000c031b0303050002c221041e40020b00a50706200174546d0041c0e40380d000340100c0b0703c906495a2500c84040c94061403500c0c3c00890b9000011844120050203211548072040f40c4014426a09100d001d4442c2e102064004425a00080150003000c41780203082e039044e04464100c03000c1c0c01d4481d005800320540a5190b0849201305a003a9011b807003000b0020b0b01418103225201c2c081c4094600e0b418298851030801e83c0010154141600000104030342490100e20103034038200d82d45411411b200328079448141c05010360a0180850001d0800140750501c010b0120001c140c7c031070090703000541d85141910f081d089900071210041d003007000200d007a600c00a49a4201d4200501212101e4a051101070700c503030003000d1194022030350707425805107420310f4802410400d80680c01001032900c901072407046502d014001d184004400c0c014000541c0c1d000501c860595401c868000c1143c8506 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 128810728 1250 128809478 128809481
    0x1d150d022107050604060e01110c0d0311010b091302040c0f08060607061112040c0b030f010b0d0f1e0b0d08030c0a1b03080f07020307050714030a060e010f0615050406030c03 76
    0x3c0d403141d5441100000c0105455901262181c0c00c44c9080e01d604001c003c0030b104003611030140d6421181c00818045c0d414002c07078452440f402d000c0307501c5000010174080400204952070400c0714100c03420300c0404445d07003c60400c2c0c8201030241c0100d260602d107000810400030a8030402400700d0740328020116210080c0805980090710107010400342c0ca42d00c00030225086201c00040342c003038072050700c03072400001d07c0c1400108991003080e02d0340c10444241c2c02c041c070f12415a080310a4007170f40030383d03500c000440100f5184602040c112821014030649a0b000100c801641c4d04041c2080c003a814440d1000006030654003503a07005131071034035113680300d000e002c80071603403819080b4101d00c141481c5840300003850f13000260f5a018080c0c0c44400e070742d1a9642d2405036903920030208020100c0c3e101c0c410410514660101c1000d44034001000c1c5c6403294495104c3c00162100c4424035111a55100452500e040c2107201e002c00900060300005881c404400000c2d0a9001c0c52040c0010b154582444801c071600c60f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 128811978 1250 128810728 128810743
    0x60901170c0406140a0f060c03050a091205101107050307020d0206070c0b0301031a070509220f0e0105071e030510050a120b0705090d080904061d150d0221 68
    0x1820070009960740d02c502c503510594841d03907503001c0d85c080e110116044598109010a071010f51310b0b0220765880e60340d000c484640c0050b4038441042007642c00480c051000307061000191303000300c00800c402c80030012603208403038081c0030b0482180c20402145000031404000d480000b60120f4010010001a001041882c8a06040100701c640c4404000c43d01d115028041e5050300d003e100441a1013800e10700301c1114003815164900803640920260342c1d949004016140f903105d510000c1d00b940144180801c0c140c1e020b46014959040d140c030720a0018071000d1240f50342c403901c10b1404191007048144480480f100a040410400d51a0300010341071b017503040111801020082d0131030303a0080d44c601d0369450304025910100c44030304d00d040100d00030034032a005440e40c81d00010241e0040d800503582d02c4c100c2d6841051580d0304203466050004092000300e951384081000d15a480420b841c00007440b03140740c1c0442800601c0798041c1c0ba0301c0d00c05601d4442440f0300144001e11203484200c0d0904c11103162880 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 128813228 1250 128811978 128812003
    0xd090512070b030c0406020f0307020d020f0117070306031a0f01150309021005030f0a0603080927010305070612060303170711070305010b010e03010b0f061c1103070f050306090117 79
    0x400205001a45042c130000f40105d40c1c20341d00747c805495500360b0440d103e00c07401c0301c06944650b5400080015141040403070900001c14103001c651200b2400c841c200008044030498040fa544131030410500c62048031201c040c3d200107030514004d00d0000f64400b03000b481806400c121038400c40722006424000d502003100241c004118400160300501c0007046a8001c46048203401d881c4004523000002900035241030729030107a5014184002441445414072888881c5950364209200380340301018085141800380d8001c0011300f25090610902401c004d0140203d0f181c518540641000401d5104440403041d1900c1c80481c01c035512a410104ca1110501c0120126070149041c00020454158010940e050080e260b02c10058141e808141c00c8a50b6000c0d116003109080d42100002c0c0341403002484034035915184040500002c00e0b131141181e40461700070f52003020000611108503040340b109034a00800f45131091543c03400c00045020a80103100c1c2034480c21894401080d415024801c0702600300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 128814478 1250 128813228 128813249
    0x215040306090c0b07022b17030907051e0f01051902010506030d0f0e040f09080705030403060b0d1a060a15020c1903050d1b02040e1e0d09051207 64
    0xa8481c20a44024801000d007180d030940220300003e400001d40c3c0980703107415002041312a41c0c00f49226884850050606601c18000a810070f880005d0202962203003200464419161a86000d11344185099180e803c407601ca5440c08050070340703c18008102d810a14020f44800061520032401a40d25000780800102c0b0410b20750048102907605600480c401d100c220704842c10050215000d5031700d84c0107a40d03c2c80000340c0a00440c8614205500284c0c4213070384601c8001035404d80c070340b54003145402c20b603011110b43d08002010030078402c2d103014110b020442280c50501e50304150740c0c0c4400c01e0a82c50003059509210f03c0c0001da5a6540c400f520b40101078051400c0c0b43e082c1401130094850308850045841529407414000001c441a2300c1101a281d200300140795001341058141e80c4114000d02c01d020100c5101c80c08c000503200d0f0b01840990044d0380b0b004055034145070000d10703906c202c1000103243d96404145081c0c1c24652103000030003141c200381c0301102e1500340d83c4070306401c00d00290001450320 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 128815728 1250 128814478 128814487
    0x3021e1e0a1b080a02010605010e01140f0d0908040e070305010e15030a050304090b01090b12130804030614040312050f06010c0302010b09070215090303011503020d0209090408040f06020105010810090215 89
    0x40110f0080c8400701156000300500340e190300041d18150407645040f80007405260400c000e90004000910142e070604034030504001c00c1c02100400d456611908445416001c60204900d407011180c480d0000d800f400d09003d02c1d030410032002e03901f007401001c2c3c401c404903040f60019a92803d10041c0051500003068a5955840c0c0c56407070045c01c140d061242c00154101d0300017601c40ca5501c16a014164607041020840d200c440c2c000c020030000c1381065403c02d13000c002c0040000c00a00c00c4030021a1518401200d074901414080e140b5034141c2c0f25201c40505080800004002900500754024000d08040090b105c960804900503d58a004a41c006120304107021003242c0016082d000b54103011911400741ea101101c1c07907101e0100384101c1d00344046488040703103000e0087c0c0181000c1000c101e001820f00801800140d01c0c024150740c01d60b244200041c080c42001c503007920100183c046400280115458020140da036032490603000002a0354410301071003155503114000c1d80580711b400c0c0c002d0703d9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 128816978 1250 128815728 128815733
    0x290a080c07020d051b030c060a03094b0b04060c11030f0403050c030703030e090403121515050702010c0209040c050603010306050a05070e090f070207080d03021e1e0a1b 74
    0x40c5c241e00c0000042d00701350100d684800d440c00041c01201b008000d04001c3c1070000c0000c06070b000d000c2c501c40031555221000340045190b2071024036141c0014a000c12031080008c0b5070142c1002d620020b001d02c1228014182080100780301a19450300150b000c600042e01030310f0b22100300c0e00c5101c01c04050382c9074080061901c9180501e20050400d49000720260384044410100b01561540786100060105100010020403032804c010310580c00b90007803c000070404030f40e621035412208014104801c0d088003440030301c8850032061030005030070034508015103081d07440d400107030143c003070010002c1c8030785110000602040940e5036504024a4060b0038552256142d280210107004200c0384d650030540740c0070000e801036108a824040118010307000f100f050301e45201c0c540c070b1131500502c00c0c010352090007800030301240204044040d540180d94016202d801038140c415101e00703d02e00030221b001080c4281c01400404280c074800c51511902130560390592040c0589083c030555451100c075050030b6104805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 128818228 1250 128816978 128816983
    0x70201020c0a110316050901171e0a0302060906090c04020c070f0b0d05060411071202250302041401060207050618061c050906010e0a09030201090203070906290a080c07020d05 77
    0x443c05811410788246880011034000c55060b540304180c2e0043d034800041019103007150642a010441e10b0640c1c8030848001e01d20382014401000c118034540c05601080241941488103075040000c04029159a0408506080e5600220300c0c00c14030450b4001140034004401b0800d880083c411548000e403000d0f52003229541d0b0340c0058525070381c00c07828000010300384e00e02403280701c80707038005500003600b8001d03503841c0d000a102c000c0e034101d070940c811480030b00341c10066100424101c9c039a01d80351402c1c032030441c410300c01a64480a01031040209220060080c1500881c128043e92420b48005403941c88004140d4403c0e0820504240c11200000c1d940c04035003c2244c10640c44070017800244007548400d4075103543c4020034030030403100ca080760740421104051504205815800380c40085015040c0d500000c0c00e10006a01c841c48442c1e1300c2d00c0401035080c540024150307444480309022a400714038842a0800c2c0b0401c03514004101d1141700113410786001da41542c110f02d8011f00002c182c92840c0c5080355 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 128819478 1250 128818228 128818253
    0x150c060603050609100905030403060f0e0a081b0a0b060108040f14030d060501020303041a090109080c0109030806010f0e04110408030d0905100605011209080c0a05071d090312070201020c0a 83
    0xe0450185c004c0250360341c1d040c1d014507048135502c04020351500c3c0c5592643d50090080102060321951102c101c002601c004011048140380101d01042d51151019100e22120300c0e900356074034141d0000009140440c00705104141e20503030a0030600001e942e6454111050b07213900e0401045861316109004d01e141c00040940208c0c40c0c400c03400c0000315190001a0b95902049800a00e42e8003260300ccc2c03001880750400e046802540150020655051035680c124890700040e45004190b956002d03410285035106a85540011007820a5154900c04900083c4100e03e070400d800d00450b01c0381702000c0b2805002c42205c00900d0010103482d150320001030b881c0b01525092a00b921035110b0240200000c8046100340401c03500140c41e00d202c83c10860340340401402c2c80748030503608000184003c1140660034040000c00f544100013800a50b0b04041c41290200e074000e6803100485111020060392820020888020300b003520344540c06941d401e48224060b10844070b031440381d8060b0100010030064000d2090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 128820728 1250 128819478 128819491
    0xd090807050a031b11040902060c0a03050904050a020c12090609041d0106060504060905190306060f081014070c0c080706021014070f0f030b06040312080a0b0307150c0606030506 78
    0x500e204000284c0600394803090028004200030180c0720024a4140e025030700462029010905109031030008500f0030703229100540c04100c0009411000d0f141c544607856210b20303051811410482c010444994582c881c81c02405c441e180010a210700b81d880c103013030b070340401070003002480542c55854060000e16800525510998200380010070401d018900761015a441a511351848618080c1000b8102e007444c01181250100d080011012808a0140c94064008050381c04070f0b207803404201902d40030240c044120107034584025100390503028424681c2040741460040c208a1260500d0304980c0d4035944407040d140301e80e040000d500c1c0d40210701eaa2842c448080c040040c50085010200032001c01c890840024800c503190f2005140100040001c241443c980003600300660400706000b903210b9002500e10707100b81d0b03961044250f40726880c1c950040c0d03c20424041c01030b502d40400c0d6200d07444c2c0283c00c01d12080c103107602c0303c4622850f803951004d41c21480503c8400d035a428419260b00082c1e604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 128821978 1250 128820728 128820737
    0x40503010c030504050c150f0307030c090617040311010209030604031e020c031005090708030403240218060a1202030c03090d110d0e13020a030f200403080d090807050a03 75
    0x1c84215501a00c076840c40741c0d400c44041c0c6201e103040d40821141c1e1001c0f00d416041c00005200c0344007200b0808002d10300c01d1013240c40024480c0318541000c0c146140552010301040100c0300f178a410086200021508998981000016030107000402c0c2e001e0302030f00c14400c0d0103100381010401410340c0890000d01d4040f1041102a07400c4401004988130b09007001040e400d43d10450b40c100c103240140d400143d11200e4001035031199601c804215065a10591090310f0001c00091f0122800320702d04a01d802d040702141e41189084550b000716002c0c641041c422503c1181c0c00304a44079500d0280308008600e03400d03250110f54900d8100406451034005480f807850610a0a60032a503aa02440e03104000c2201480200440c0f8580e01c02110111204172500e90010440315511008400a0014100c140c50545010170827607100705070f100440e0b0000d01003212200c800f91004464126240898050341e8005424a5452b110000741d18090540080000c02c509400582101403120100319541c4040c46940d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 128823228 1250 128821978 128821991
    0x3061701060e0c0403110d0c030b160305010b03070c1106040906031b0e271e030a02010e1c0c020301020f031f050405070f0c050c090702030a081308030112032304050301 74
    0x4040864061350000415140000140c1c201c20701d081d20498034034510581c0010300ca42e850340d6a4000d04001928041c0e40012004508092141c0500800d405440c4d12701900342989840000101013400b41800a86101f0b0303111214030050700e84030101c4010708003642d0309210700b40c0c3d645050300c2403000503007280c0fa020300708100103c4d000c0ca0b035030790a6000b00e203a881c1c03100300200344140c2c21452618032139221416204d980c11007015805180720302e02c0030380810009940c490340901c40180c00e403848840c035100345801c052110401140941217201c0300d4074451802c03000f0048641b000c20300912558852922201011040003036121f0290420a0310a010321081141285d5400500003519000c0c0c1e4400c010030302e910304204115100c0d0b0504562079008104449107022850041010b03664181c1d06407006800003e944410103403c086d01c503410410304240d22100c1601c6440700e1409010600071003541e0300c85004e81c0c20034984610f0318900d6200d41e200000801140000c0704c005641d0141c4076581c041d500340203 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 128824478 1250 128823228 128823241
    0x301110708120a02070c0b0a1e020601091a03070f030210021203010b0304210e0f03070e010b0a110d09050a121101050a03150f1a030408040608060103061701060e 71
    0x6a40100758420121410300b003140405060528000340a4070740560300303005080128244110700d000070304041595a90b0303141d6440004003840b410301c000030701100002030a0300000d0b90000e110350454031520400517196101740c00014403107846254841d414071490fa80803402008459051f0b0484c0d100312011f04201c1c4000805a8490303c605c942603040300ca041c40100030039014a001190300074815255454015400200718400600c1c03250407d0024480c0c1031082a2400c001018034070202d4214002d01255280615558030034005005003040700301c2c04140010010b00844030058074280b0b04095130040742c00580000c28082c41d80c07055074460100038200141c0c121100740200c011a4010b00746021031070405d401500d0a038032003e4060f00b095500d031051005000c91010040c007504141e446000b400d450201c034801c00340301d90703406003090907010001d210000b28210304450803103d560401e80c103140d4400d40141d006000e030794080080340319201240030304c00c5019400a000c0d0b43d03083c100f4040300e0b120748 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 128825728 1250 128824478 128824511
    0x601061103030105010c020402040302180a18230a0807050d02060606090105071716060609050108120409180b07030b120106060e04090215070c030501050c030402090c03041704060504050301 83
    0x2401461041e00104014002940302d102015010340c005400076107030aa40707501141c5081d40c4c2400d0304c844c266040c814001138442e0707400386c0d500071025840034a041c200c1c1078031600c0c0c81c4018000182e0481d1302c03404000a0b08003040c400d0f48459504201102d4a40f42241021a2200c05260300130006008510002c0c0807450078200740c0c2d60340355045e50303024200402681c6601e04c0080034100c20500c050140050440b282454002592441c881e01012490f549010b41c00d10030740ea010b810203195038200440a007100e102c14415a012907d01400103d4000c08080c0320406681140e00060004000802000341c8150113811071445c4030f5059400104213000d2280c640d00722250b80c01400001408403c000245260a03005505040c2c002040c0340c0c4080c00c0c0e550707402c0b15a48920011118810f44200406c1400428420680d1000000101901e1458103900180d500e44004019100c0f0100100c00301c0c0501141500086c11407200f2089143e586446210140a64005e0702ca203a101e9800c1001500780801c08 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 128826978 1250 128825728 128825747
    0x8070303170a09121d04050106050a170606030402130b09041110021218150a09031a15040c0516031e0309080904020a0507060612060b03010b030a110a0905011502060106 74
    0x1802c450314424060750850780620500c0b1540d0b0b45c0486104000100c1c1d81d00c2c8500d038020500b548400e0750712402c10f04050328104003403010440c001030300c108202e078a4803503104882c0e200f6411190421030001041c0440d004040c00c211258022501c00108010019200482c0b00032100c1240c0300107007a10304180481c2d403004490001080300c00c0c14400781142242c90030f100182014000c1c00c201c2c4041418130f2842c9a9000011060300040110808105216104d01001c01040c9004020301d4146000c56a4040c04a541c0441c1c0b809550b0780d401101c191880fa8007981c201c1044045030141048003824028000240e8070303100710600500c0a803000540340640b05034144190704c03050507030504d01108104402508260344080600c901000200e0005041d4030800d00503126400d03106003409590b040c031a01300c840c40d22015000e68545030301c410a59400041d100c8c8500d50140e10251003c8807000440e003181c041c4d50002940350f04240020907100d44140b41500c100c1100c2c1c3c00c40d0356903030ba00c481c2145c0e404034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 128828228 1250 128826978 128826983
    0x908031b07050c011101090b100e060306131e02130e060c0a0c1415070518040b0102151f0b04031514010314031c0902010e04060506160c08070303170a09 67
    0x44284000540d500900b0041154540305d0000148488152162400c08100701ca04070b15002a126050207450b600c911382581010040d0000c2c5418030701401c6c0220041c02c0400080c007143c2d1103403460740c001c241d000c881083c1e95901030b09403481a0704480108024041740440000d80340503000018041046170707000d4401d91905562100b60f804815100c40c40390458a2203c0850360088545150509104a107018000d206540d0317060381d03d6019000c6001e5a48c03050703443c00d2145c0d00b0100c00b54480c0c0c0e80083c61a81e01c41006103241140c1d210301045005150307080701b0741040c030f1041c5d650025103c90410301030001c07240200586802c5090058007901140d5001e610784500004040050010800c2c020107260703107041d0401160303c0c100305c0741c242c49a00800714840e00c0300175407907008100855074454000600c410023070754184415810400080c42c107006c1d180e08403990507100080311081c4004d019054000b04155420ba550b50382d2641002484200c03000d8442e451003131401d0114405201c1032084034800c1b40c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 128829478 1250 128828228 128828233
    0x907050a0903230114150102030403080403060f0e0f030a090519030f0f06290901180c090509070c031407020603010306020307020a050d0e010207060809121c0908031b0705 75
    0x3800c0d9600d81880035000305a400c404403c0769410300c0c0440c824410600c140c40007141c01c9103e458a8450103500f85000c0c18140d0441d0001c3c802000001d00e4202506c00380c82e407011001c034003c081407090100420407004201c0181c0308001e524102407101100402a24805940745c000341c5480b8814044850b140c44100090150054070420104d14a001d40c1c8034603610884841031110240e8580078140c030700d4800c00c100e00c0c0340b103a0261003524140003c0032591041c00ea8080116600d800e013102c481d00100c0000d209443e4036800c00c00b4040b8410801040a4070300244030400906103000700a1602c0d0504c0303421008202001c0d0345644a00c807c1003503484280d4010310715442d5070f0070b540d1074501940002e0010003e52180d01c0c1007400040b02403040c103038607070781542c0c80c00044140240020300d80507c030780c840b000f8041c0b13403800d001150f80e012541002c0742c82a0800340c1e642d44410515200304122200c09010348900d4a011002000880e100850081000746096421410103d9100300c05201e207010082413076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 128830728 1250 128829478 128829497
    0x7030503041e09021c0c080601020a030e03030702060d060501030608031306050d0b130e060711060c2802010603050c01080720010b060406021c020f1e16030602090907050a 75
    0x5080c1415000a4030030b1410b54200790664500c0d80105a81118201200704039802c0360f0503002c4005489050103500342e40c5400c1940d4201900041d4840b04007400c00f90411052042041c1c2d00e44041040342e4409074042c06a41d9640f1502d01c10130028034081c040c0a0000f411701100080081c400429035130b42440396040c22030598034001c0162075030340c04091000251501c0e0540000c899548090058401c2c14604012604600c2d090346c250504400900c080280310100401041244002a005a1050066482903500c0216100b00c1e0104070b1400d805180d001e07c80908844410384c190455400c9074416000ca9901c0601600103448006040391028001180a15000704043c81c0d1071090382c0c41213a140c00010400481c60100d40940d000360480d4002d6032040c0000343c40b000d0081d02c07a81d03aa00d0070740301810300c00c940762180c0c9841d08900d03290040415542c18413004200e00c1170086480c1c0c070400b40d6031100207503900d19200d0040d41111800700c0c421002d84000800c024002c100b100c44516440d038541114 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 128831978 1250 128830728 128830739
    0x5070509041505070e0402070305073302090f0303161401140a0c0c080a0c0b0a0203070509010804050f060f010302130b10030f02070f1a090a0b0703021b060f16020703050304 76
    0x200302c001c00e0b18041041c490045000d5403151f2000305002406903460581c0c0d11940d0416243c0300410010000c1d424058440540c42c0c0c80c1c940d40d81409034003490740d0140e030f2504400000382102541500c52907060100007011503e090b030266912038803d20990103403800c421845840d40c01ca402c061811599400703100c000800b440c034168400c20161080707007401c0d1070b0807100e5201c180d110341001000d000811141c0044000b031088076494654070660380002503107149000e00005001d4040c4004403818410801d001c202081380c14058906410480011500545006200760300c1241c020f1005070300400c910403412141041c640a40011044007401c0c41032402d003c4941140103013541034030411300d070707900b4080e0900086006812907111400f030450031190481041642e419458054905000b5a00802340000007508100409a00413103504006855005680020040e444080301101c90360041c00c0800c0041040340f85468002c2c00b5407204d1b0f220000301c0080c141e90343e03421400064041c0d402070204102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 128833228 1250 128831978 128831981
    0x80f150102030c060c030106110c0d0210090902030a0218090f040201081b0d0213060c050a08160602071407150206011a160c08012d0c030605130207050705090415 71
    0x1604410310440e442d1202540384941040300950720914111030000040081960010305e02400b00c3c030082c00b40c248a00d0320400282014039000d0024040ca0000001418450007411080700902c3d1900b0190b690303140c8155001c1c000e5004816910401d40c2130b0028821605004819901c200424184105552160f40040d902903800400342c6845616076111048a00c9641c0c0107066010490f000240c0c58001c800701e011885002e91700320008014214080320301248000481d205072030303000b10b0740315559000d40082c044000480180a04003c7c0001050003c0001c40302c482c882c00300750003043c2e401490316030030741340105258030440300c00680c803c40050124090404040300c0c0710303a02050491825807540c200c048440c3c4228800d0791542e1074081c080102440a00030001c8486034042111941132205119400014210242050346607440c05240b080b40d0280d4010406014010452010416050000030180d072100030103d843d070245590020b028186946000d01999000c40b8442180340905003040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 128834478 1250 128833228 128833261
    0x302092d06040f0c020105040b01051504060f1e0c02090f0105030d031a03071805090d050a0c03090902031515030c090618180103061404030e12030f03010f0e07080f 72
    0x194003070b50f40c2aa40c14a02081c0c41000c04414982c0c0001c0f0f021b1820341041c80174248160b00c2140540c03160480403c003066003c04480075903000c0d0a108140214110003190070307481d0840c028000e54210348540c102950402806000c09108030360100325130740c0310403c051021000f8400c26405170b002d800f4807900c09020b9000014101c1c503410001c80312071400400a40b40c040c1a50101e83c45602c1d0400700d0f0126002c0703001f50780e88503450a0041080e00c403c0032740102148a064500703000c00103036519403401c241c41a90110000c0083d14401e5480f820095101d60448900c020060311075105101c006070403c0d0060300384d0b0b20a5100c140142d051800680500c900f0303500000802c5075080f11140305540f41e9807120300c40000d00c1004495841c040d030451803c0401c9490f041130324031030120755408020000c3c1e448002c00005841c252000c140f081407501000e85140101c102c00f1140200110010a0307510700e94070003104271041d0000e298010745580d082511035000c1503078421035044180f000201e01003000003010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 128835728 1250 128834478 128834491
    0x915040b04150b0a111e1b01090302010c061508060901060e06030709020f070501060308300c0a05040f03060b09070906050403062d050601140903061b0910090302092d 73
    0x40140310b0308900f5040c036142c4039407000c00850701b858030801c14908000b8000c0c072162a0f4150070307846201d800040c201c155248130090401115034101b00400101d0340080007400c1c1c902d860003a0040c0c861003180c2d00d501c41240e144469605e041000203010b140010720074040c0300e020b8041d2681e035007000c04030000b1b507110002c082e5800100704400300000c0c07000d2103204000e41c05844807079220044141005d50040c021510500680743c03059100032000440da001c01c0d04241e410640782d6171562100015600c80c0125809100e44001d1044000248031540d008403c0f41c010450b0941e040f562481404c0d92000080e00401c000954180410310000da010751200c040c0100303001001084500000c0c5644010080711302e0300020640b64414030990b960000d6411182c8d60b8105d10481c2015604000310755901002071280300c1801d60080c02c918000c582e0f01c11242204130107403040343d810107540300c06082c820141c4000c80c040c00600c1c1c00600212403411224151024101d13405040c9510394600e5441c0381c202a140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 128836978 1250 128835728 128835737
    0xe0a020d0605180601120204060f0e0102011d030403020411040f031202120a0c050706110c0d0c08030f03010e1003020a0b0a022e051b04150203090915040b04150b0a 72
    0xb16240d9500c0c4142ca211100400380c8003000e152800005001c42c50440100e0040c81c012301080c450310341c104020200c801c58920344140030021100c0100d0141c0041510308291104401540c104410040014800c0d00e000345d80078402d400c15451701b1189803181380300f40002952034501c00e0000034560603200b8184c024034030444400352440340c0c00c040103600c1079027400045250010034a04000381071000398020915414a2080d290300c4a00340e940b200d81100220740b0541c1080d02680412441c11040006403005400310303038035038849204038440c0358028081c022684a034440024441d0301c0810038002030f20760103070016a5103860400140001d400055500c415030080c40384985260069030320380c1da951802d261841e6100305180d40240c044407c041e101104084844032418000044101203400b12401c41002100303259100408034154001e40e84601e503c035003050305200e03000071742c0b8001000304101114108000350003031b41000212a091805202980ea06044c00c01890f12201c02a101d521641d090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 128838228 1250 128836978 128836991
    0x601050114042321070515040321080a09020d020d03020c040c1d040501030b1503030409091a16020a1104060f030b09120c03030f07050f03040501091205040e0a020d 72
    0x90888448142001c5a0202032203c0c1d11410700d0105a02000440400f201130007104418004035100e580c00d0040502440d400b190802c0300f410400201c0f00115003100c041d005013141c0300141d55841075030b40c680200203140b1101103003214008d8860b0004050707004105002e0380c2444d1782803140c20107811000703800b94090981c1010554445003e1404000020364510325000d9241c0900500b2407400899280540d160a00620000b184030441d01d401000c042c0d8004c03003c0f000303400000d00c2c3d44203540110300c40c0c80c100b40741c1c88104900c02180403444030f14007480e407000307aa0300707041c018051030a8001c0d400140d10600f61580400c02080e420740001801a1000c283e41c2d4580503881e0b8601d106500031540090f2410812080f0384041c4441408070340444007462030014032004095603400080c02440c40414144081407605000f441190340c601ca500c03603055120710781401c1c00ea0081c48206410350b000601b00c00d644621030700c03681c12101034510307070980d080d010749410b90201c00070340100c0d02d070300c1c0455602d80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 128839478 1250 128838228 128838239
    0x5030607020a0b060d051c020706021501050607081611030105060103020705030a0305090f0a05030c010b01021f050a1d0c0a09051e0603030d0e070602010b01090f06031e230603030304020102060105011404 89
    0x1c07d510342038261004403040000d92880013071a0030f100d40d100384119044005407903c039031043d00788581111805ca6007203813a4152424001558401c420340764180c4e140c8800f030342c030400c0306984070f042d09034800724000c00455465000540907403140404c020450780080100c101f2440c001d80c0801e400035024411140d014004043c0d141c0341c1003a000061300d1030751000c1210210590240230781044070340c0a1010b42020303949804c15100d18924200101d031465150000110908004c0d40261070f00b80c00c0d0b400800086109400c49921480c3c00d08240740030703c1d4110f80c003040784142406443e00414040c81c2403911440482e070f4409185d50040c00466040c0801c1042a40012590103410b41400e00580644489490842d000e400c584481500d00d040c81900c100401030035812a501d2001c030b40040c03c010070780240340d01500b400509022400d8100c0c51900104011141414000041284043c4c41c185c00d00c1d103640c0109603680c0000c480003401030303210200511441d441141c0c25020a40a03610722400c1c5510782 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 128840728 1250 128839478 128839483
    0x90f0a1a120c03071a12091518010507020703022107090f060509070c0f03030b041506050c0c010309050d030b030f01240b0c06150303040b03041104050105030607020a0b060d05 77
    0xc00000755030100e031000285141c203002200040c104040e408150041c00d03e111490340c041c02500540c600c0d9000b00040d0058401c2c0600580d0031605403a0b03001502d82042400d821300010802c07030045621b0300303000551842c0001754400503a41c0007040306c1c0302d03032960015038102d80b507010102c14414000d8800010715060640501115084408004a499410681406444580100b03a1000c1003061404c6030040b6010317095040134283c00d0300c0e0200d511500e01000c03401a114900b403000801042030400111990300ca07000e000090108415035240400ea10011810307107481160180c8190000801142c0d90790290b400f50a5094020382601c1010261003c0e150131100101d4081c0004080c101e80443c084060380ca100317004c6c2c9100c6052a050100e02040b05030382c7e000003042e0020b0020108481c451550b4104180e0700109103044003d07540745401d03d04a16041d214800d02409a802c0900224540c5400b1800c40c5c415034155004024409441d00d0328820700c1c00c040d06180d081a0104423032400318805 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 128841978 1250 128840728 128840749
    0x90f0a090501050906150d2a0210060501090308090f03071805060a06030c050702100504090204030309051306060507030f1b050d020607091505131706040302010b090f0a1a 75
    0xa40000160755890002844090b20004100d00e00c901c10600c000700030414020161041e0840118000038001c801060703002c00101e541120010310301c1e01e800b1280a40e6400901c103228195001c00c180515076480c401034824005a01004081c54001d0260170010b05190300f4002600d00001c1c00c6510690740e5101c403030340b052801e0708090455078603002081002d05281080f00010001c5260030442444031a0004005000708080241300310340b1240c2c5180210300c1501618081c0020b440c045607925070b80e14020700040014440c95001c1c2d034050140c44c403000517602c1103808a5034551102858036000d43d401311040126010f0210521890303a80e00c9030b40d071294010900400e44281d0050008074141040a413901d07000804032001c10600201c01e01222908030030780c0e40c280c0300720f04185031507c658420b40320f044441ca40050040c600007402c0b0481c141c40018020380a98004e40003000500420720034007011a4040360500500d41030007001c00c1450089621038441d40300e0620200b03200c084d006001504696a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 128843228 1250 128841978 128841989
    0xc09010312080108120d050a0b1309020a08240a150603050108160302030309040b120118020a0b0a170a0b04060602031b06040b01060f090f08060a0f02031308090f0a 72
    0x90407030801c0c1140c1d00000300740d0140c0604801400708050704184601c80e84a05401c0031102c40c1c440020540002494014a00e0710100401c00007400035102c0e903e41c000d00000308103a103d09000e403400201c80c01c000c50000c0000d00034040c0b0701180854074907604c030000d4000d042e401d070341660b510b5603082000148200ca4042d02c83c81d60041119450414401d10340050030400d1000b21100e48130400050780c0010449180700c4e0b054a000c186d00100c0d41c0040c60218031007251325015400d000c03880700365a0000c0c000c50358441c400c0b9590003002d920b4486680e41d50090080700c1c00403548182e158032682000d2002e05502401d10302000c0f505441d4500410181c5016500081c096407020a24607500c0f105042d403c0b040c085c40700010301592500b61186445d07140107108100c10300c0040c2b00c00e168070034480c14607400641990792007020b19507692a1081e40e40c0e14115003445103549080203e16020b906030085034010483c18045460b1704115031110005075102e1452240c3c41420060300c8200398868480c0a8014030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 128844478 1250 128843228 128843243
    0x30c07030c080c0d091403071401090504060906062709050c091e090a0b060f0a050714031806040e0610030e011d010b0102030304030c06050a06030b040f0303060602071401110c090103 80
    0x407a2104040c25030300e01034010b800c503482061b04e0780300c198070001a000100c5002451421141102c400141c60184071a08995045428030b90049203c106070b821141c21140300380c0d030b6030074508504800d1940700c3c00d146804902d00300a6140030080460319030841e03600024165003151801910000250001c048400c020050780d050940c016010320b04462695444140d2100034401500d450380041c0780c901c9a800f1b064103c107008a00110b403184604292102e06501c5082c040c0400b904158a60340e0340c1051042078101d100c0604ca040c02420700171b05460817504809800511901c5201c10080c0380e0754500500c1081642ea0b180a403191f06090092503a00e171b1911072042851780d483c0004074299400000d0135410f640c030420600000030b90205000c03c0107500301d280001c02e41c858001e2440a09141c1d400540400340c030b18103010501000141c611041031180c0c900700182542c60350180c0e00d036003191240c002d8080e0000c0c4102da1360f50040600b4841544814251003500440100042104c2d500703800079900756 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 128845728 1250 128844478 128844493
    0x20a1412090114010812160501060308030108120f09040b0d080a0c0201110102131e08060705030106080f040c140f0904050604020a0605040806040809030a0b0403030b190b030c07030c080c 82
    0x3203400c2c418618000f0710048070204960403e12000d41e9500c00103c0442400300c00608030b540d6200d03150740c01c50000d602c0402401403030358034281101190020b001d59034060103501515607580810004030790015020307078000d80c00c0040e904100801042c0e001c0c24079802c01e0080d400000010114001030500101c107444c1c05040707600d40e0000501c101001c1c112210785078410060900c0078000c1031041c40c11100c0d54800003003406d4448804d08844000c560042605201c3c8070305000701c082c6c000e0043c605079031003a95041459541c908149041e56402d942c0a0304034590401c042c40002140080781904000190024004000b0301e00442c1c1041c104a80585003034010a003400114500340140b00c004000d949442c1b4101400c00d01d44c0744d11058003a0000341791030400242491a610140246032075a0f0700f1000401d01ca10f070034180078007c0d1038040192440768144084000e80c2c48000981e40043d070315403100386415640d0305461448140e01204065091003284d10442000840400042c4000e62948014001d003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 128846978 1250 128845728 128845741
    0xc02010f05180f0a020a090e03040305010516080a20030c1c0c020c010810210b0a0504020103150317070c08030313050613020d030309030e060d090209060f060706020a1412 75
    0x140f07030201101c0c0e0301542180c4400005131303451120020a03242c00840000b8214100d8400600e91f200e07681c00207081d0750034a410880c2d42000c4403040d406010150310340790b10a40d140e40c0040304803131542800d24403d60700400700e929000c124030040c2d64019500040ca51400c445002082048116a01041800b41e256080001019810712203145001000e0a0460036418801007040400d0a18014200380d000242101c40034907401606074648181c20a00c0ca610905114204c800034100441d0300fa804a0b0824840d000c21a8445c4922001c40b500b01c0100c0c0410020f45844800f168400d800540e01c010030060082440017040c0000c6004000062100006003094500340e400e0050050a4a0056200000f90009078417031440f00840c2590516002801c01315034038050712800700301481e5540051002c07401a000e80b445a010744032003030080701c2e14040c903a100401c200240000452154026105106503000100385030003601c440030039070070050090410703604168410f400c4a80103111001c400014444c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 128848228 1250 128846978 128846983
    0x50304090606030504120c02011404060f0809060c0f030c0c03160c080102030105060d090c0e091e0c0303190512040b0109050901060b1903060b0301150f03060302130c02010f0518 78
    0x409450806012138176264845100320440c0d5802c0005001405410008580c032400440007a80100381180362604d0311210001c0c007c2007828940c1010480c80d0005c10300303246e00020101d01c102d245035185450245440f10f010196000075060314408103003400740b0748407400c042c0050301c1900320b0304110545400c01c60911950010003079000000d00e91041006020075142d01c1d00300c40e003420060700c1c003151414491418a184100344d51101e10310742c59010a0007010b00011480d1050075000b002058400b18a01d087c075900c401c181c016980d0f26500400c041d032881801e0342c86818040c20303203080850400e10001501c0d041c0d660101d504039030101204006100806c00361182e02d4010b1030550003040401e0500e42c074039207079211b01505540742810540a1045003403081d04501c1c0a441743d001215141c1d41d603001802c11034003146548101082d4403010411080c0d100e44250001c0340d4004040c03500d41480010100000d09078102c1500c215529091019404101806410b00480085204146041840f142d590 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 128849478 1250 128848228 128848241
    0x80f0c0102033403110c07080105070e0405100e10080610060f02030c0a0305030a0f090b0601021c050405041e0207050a020307050409031d0307030506090604170306010c170f0705030409 81
    0x128684400d0159200da0b004071192050043c00c98180040d002c0c01d4003254400d5801602440802486220030100b1035580640016018400b10b8480301c00c00400070081000390b82c0c04031203120b03020858003020090410420303000d0350400c10303070807942d0710050f1200601804e00900302e4070000c003500710820402c11540d00413481060702d41684081d5050050f10100300361142001c0101804200002c804030741087c0b550780c4010568100043c4c100711751010351406101d5600c08480c8103015015540e0a0a100198820705003050744003981c6407817900d41401c0c2004010042c8110011105640f60100e5801c00d1281c03009140c0c03c0e004100400070741a8920403d4900141900030034011810043d080e00084d400000c00d0180d0041c3c00310703c3d070395100304201080c507200c200e03030003d030091040d1400d01101460200b4803501803070060a454006560307000e07512855101c10380300c843c00100d02e0000e07240401c44441000402802c05c801c0c461034581207011469140d0407504003a10a9040010704002d207403114869003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 128850728 1250 128849478 128849521
    0x206012402100917070c030b060d020604120503130303121104060f11030906030415050a05040803040b0a090b010603060f050a06020a17040f091a030f06070c080f0c010203 75
    0x48000c11100c000c02915181150801c00c880b540361800b10041029000e0000002d00c0e00d054030325101d041a05040300301c0d1140d4030098908981400103d9164248000e80d2410650007818181c07420b860291020088043c0520640d0240014003190414217029805000214001d40e9100f801c3c4041c00350070811103000022000840c003007000300300300c4660405501d01800c281c80c140b000d400421030003d64150302c10034110301d0740903400204210400c039400320188520341400000700000c0d0303952109081111000d40d400707030109506200082c0081c440564442d0700c0f4031118804644000a5038911400308000e030001c0740825110501840701510b02000b500c000c0604950040d0490303d482800f03500c1d0a5414009840303041c8460100f00c081030304170b003142c0007070190300501094540d503015414000e00c19000241008442804543c07010310f0002284000c00d40c050340641841d4844000a48200c0000701085810000910036500c0f84070342c42002d002021001030001d031341c2c1c4c03829940c2c00340d40a6461254 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 128851978 1250 128850728 128850779
    0xf13090c0e0102070b070f05070b1c0207080301050f041b021b01020111041214030f0714011a1c05030304050d0206070f02120a0905031b0a05040212040609081306020601 74
    0x2800700740e07034001038100803030342620413082d510143c2c1d04000003d0b041c01980500b0038850303c0e500040000f00e56000708000c50201100c8540c0d08681c1607114107074800c65101821884050005000c00c3c0380600d00143c02400007040001c0d1001c11081c0000d10070440d101d850056000030790260b41c50201e03c8650b600340b410900c000c0000224518000704503025038004c2c195502d64aa8900c010042404142500c1083e0101105e032115446800d510140d1700c40c0d90308884144001c00d480c10700780014065004070200800c400d6501a03002014000740c1d02c110641010a800c1e84502e01c5e0215105000860203180200c001d40301e030188004019180c404041d100038100041500d10a0312140e0200704500c0905000c10203036540c0921a000b00d039901140d4000d01c1d0f260082849070303104204072000708503841906071444000e85655404100482c0941c00c12030040801c08000100013403000d50110030103522854005060a2103890840d846807850b400c2000941d0040c0b00501400504042c00040030074607055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 128853228 1250 128851978 128851997
    0xf08060d0b130501020c0a0b0103031715011103041805010503070501050307050a110703020909010905010b0613090906020d06030c0305010b060a0c022e020312010801090201020d080c0f13090c 84
    0x40c0d01401c0c0300000c0c0b200600010303a075501010000b00707404407001d00f2003034800c80c0d151451a09040d00b09003000e100480c0407461121214600c0d101e001e6034907200c1c8050401c00c09071032840c40300640b8080707074140120210f400100408070704e4954800010a80000d890b40005140d03050009141c6003d02e43d8203da81400000c1c400c220f182588002207a11000c034916000f2010301041441b185000300c1500f0082d030016505003001000d03041540078406040c0590028450f5094a006010442c42403109401845030081418803442d607a41d001601020310030000145001201c0c9003002c221400c40c1c00c102c4851400311010401d1000c24080d104d64940100e44041c50030b805000c0151262031102e07402030194a0840340c1c1500c03070f5695940300e01060020f07031502c81110300b1050002e46070f511281c0c924010841900011810703050512507480001c0d810780040031550705400d000c1c1c4803a00700030b29152902c40c1c104840c0c1d030ba1100e0400604118102c101403030040a0400021409544040c840e002c1000300002c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 128854478 1250 128853228 128853233
    0x3360302010e0d020904030c050f06070c060f090308072f010b010908070e01090c020a2001020f12030a05090a120e101107030305090f04150e0606030412050901030e0604030f08060d 79
    0x45e0b0b45400907030500b0044070004040c60b0150030840e000c0500701c41d90145408200c01e0a030041d410212480c0b1800c01084001c51441d42c0d0421280c50390380c040c000036602400204074901803043c00201d8010169885c02e01c0780e09200142c0c4d802c13158105041d013a5110060b080c0340f03580048404000d400c5400c041d1040c0c0741000f18602e601581403003003d12141e2642d40042c4003074028000b0030000340d08942d41e0a80c034018000b0040310f24007044a000d00502c64a90007001d220350114071421200188002685103031620440307a40500400b5000c103005000c0e20000e400096031601d064070051503640c40b504035440c030341400c10106c4151110201d080c090030344c1c0c000c00c401d540815003a0580341e00d420019111154200415035990201c7c485603046443d22200300b81d18840c07483d0640450302c9810b0031036103550300d440500010340002d60b030040c079030341014200541c443d00a1019007100340042c0f40004a4030b00c0701d0001441c0c4102903c082e00841e2400e850f0510350350384891039aa00507019910400c1808042e03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 128855728 1250 128854478 128854489
    0x506011a160206090d0b0105030606010c0308040204051008150916050f01120b1203030405060109142d0c091002010b150304080408010608150601030c080403360302010e0d02 76
    0x70a01d4903501d400e1007801c241159618015a0000c00740904400850032040c6080100c9001c2030240b64820700c26680020702030f40c41030400c200b02a83c16a90650507880343c1d403c6c440608009012000310241204021038444801c21148000e40303030080001049061007c0042e0a04024000e01c3d200b81211f0a020300054840c0e00049641000a10740081c0368603603d031901d0000c00490a506a0140400d814961140c0c0d000010310300603401f41f410340d01c0c5641c0c1c03510b050088501c600100c4a5194a42c2c00080900006040043d2490b580d9510003032640750402c01d40044102c1200c0c0075144400100c0c038890306091454030354024101c03500080064402d510b000481481000341050242c041c0040010108140d41050b42c000300140d00090050b01d03210718103283c4138400080483c0c00b25815200041c010361190042c140c80c03c40b2a1640a607544981d01c04599441c490080c4002203140751000124200c003c2070103219411042d51b0068411b42180b00040c6821907014403e031054001d440444c0242c7d03200c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 128856978 1250 128855728 128855737
    0x105010c0b101502010209040e03180d060e0109060501030605060904080f0c030c0307030503040201140304111509030a200a030b06060717131809030212030601050c07120506011a 78
    0x1072150190341c400d44000c54000311604401085101071544480440e0150050044240e04032410700040300c1060840d46d0f213000e0420048031128140d48018103030b0500080100999000b05004241e4040c0c0041d0745007546e6040000b190515038031f000400c28480d0510405412010445035000d080c1082c1e102c4100d01c1c001c040c4084a041000594542c0000e4200220b400c21a14107060f281c40d5002420040e02e80e81044030107074045030550740c0007100c81010b0000c0700e20840c1d001c0c040e02028811030040c0b110000c484240c008089004104800e13103560100441c0c040b9178840c066900f1018007004c510001011454025806080a17200c1440000e100841880e40100261046911482030303003403800ba440d085000030040c0520015545403211420f04030701003660103461001100c02c40c01c3c103000b4121200b940300940160440700800c10a40c1440008640000e814074256052003507140c2050304001459011079440601880950101310090107135500400c08004103000901581c404e2107032070b114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 128858228 1250 128856978 128856983
    0x1107080f0d0b180a0c090503070e100b040810020a050d18060c14030406110712031b0504081f0e03040807090506040501060f080a060f081b031212090a0206070305030a0b01080105010c 80
    0x4480800e03800b8070344680a0300d00181401001c0b6810b25507078031304013582c07070002f41c03036000c05034640c04004913003c1c2c10a8201d4048a01d050010072450b000007441100a400c0b0300341e00410440c0810100641c06540d00401060480c5c030a50044080110b1605c0f00c00c80390038400c00020f001c607503e4561100c14032001543e40c07040c3c01c1500840c00c01032407810200c00f841034803c001d21401e88500b032034a040e03a0541c06680291182400e40c20f105c000d0020548845c01180b0420101e540407004010742c00034160b000c0f51500075103a401040c04590000d10307605540050304103e440740e018100821018401e8011550000c0c000c0d43e040001d0750420308010048035001146505025009000c21720400c842d6100b50300a0042c000340001c407548580c1c4940d00c0d102000c180481d02c0c00f4038140e03205d840c58082012040d0141c0e6420041c500740c00f5113842c03000000300400680c8240111060740c030143c1c0b01c01c0000e1031454440d030f071070642e64a810b082a50444034cc1100950402076800c0c014400c603600980725001598 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 128859478 1250 128858228 128858231
    0x1b030c010f111813320f0106050a020127020f0a030503030f041509061b030c1e0c021305060108090102030402090c030408190513080606060a031107080f0d0b180a 71
    0x404000840c211441105101858500e40b0a8031800c140895174950b4600340200495802d4400c00000180720301c905441283c03442c06c070311004100c06400b40c00140040000c1b0700001c51342d4079500005690304107040388210302424000d0b00800440c0780c4018100e460101c1201d10455072415501c40e41c0e0b5a01004180d610903900960101d03042c0010001c0604448075032010602c1104514540071003d4045401034820281d070a6466000c82402401118620304007965106c60141543c0702012001c412240e60f80d06101600c08141c0145e00e0301401100040744c0600007003040d050a1000404c994002090841302c0d0f4410b00a00c001607032407110850700001c01408164980e00e650074003049900c241d904600c1104003610242a000340c000c03001c1c1a42d005a0000554072940d28903500e51036410448070258000d104200401a80b40240c0c04401c0c00d840582b4103d0404089a0f00d00c41c4a074801707641011469000301d00e07080c240c846401030841b05141a50407a2258000f030481c1c603a03110780a4115030300320b07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 128860728 1250 128859478 128859517
    0x100b031e0717030c0c0108060109031e1a070c06110d02040803030609090312040b0a110a080601140a08040210020f0d0306050a05120607030e100f0b0306061002030406050f1b030c010f11 81
    0x580c2b040c40c44002968000043e541c520300710302d811178040072421b0022605c404410503503202ca4400442100e201d0b44842e121240d11004541d5410024500c8505000c030640e8107024044901c1c6091011300080c01d00e48004695a0400c5001c0101a90b8002c200c4c800c90b510410403800c118413246034090b00240d20035140220364603044042406003508204000420310082880c02d5526072103102c0070f004000c2a2506c00b038030740303120700603100300e21501110b6000b18000d080072500504020516604003103051040e500303102d4400381c0690130014003d00b2800081e450300e0041c052480c011301580700604048405042d56000520385035210400200300006055440400c241c076502c050240c405548070f2410108800d05200c4603030f500400b40d01c04494081c0c420400020503d0400b21500050801e440c1c0056043c1ba250010444080c0d00400100b91141310600089401c5482a4019461a86088003440c0c507030715800308280c01c5603802c448c812442400d28400162801489049038107a604071520141c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 128861978 1250 128860728 128860741
    0x160309080c0607080f0d230403031512020603040f020402210601030510210501020d060e0604150e09030705060429060901060e010219061b02070602100b031e0717030c0c0108 76
    0x200550061001f1410071a00603215019407400e106101d1032194404002903941c180030042010064050220304a00f0180703440c01600e0310a000d0355000d8410402200a50016808a0144d07005005c1044000c040d0704502c0c50610205e10398203600003020b00c0c08120910b019140004000801c1c8100d204006496616000d03a44540611072403464104000759074500c44068594000c02c0c5034810040380b880198045001e91510307010b41254004410300c0005024104041c1c0c4407451005840c01c0e4040c030082052000141041c00400d2249002e840c05401d0341c5000200b0701e00c2450301c403030003074000c4410f41c0800900b80d07195003640c0d0544140d49441e45069043e240113130700e0300381900b80c4542e408510861040821091360000034040754400c00c4d5090310b0200f541d00740d0b683e5449000d000d000d60084101e09410040f250310440703032800010100c0395811000c545106045003180050352490700320300c030240001c0c0a4150303169100003181c4004c600d810329464003d030f100c40d10070050038104111600030824 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 128863228 1250 128861978 128861981
    0x2060a0309050c0a0f06030b040e0705060f07120507020f010816080604020705060c03160512011e0e1801050709050a2c012301051204120302160309080c0607080f0d 72
    0x4550f2406001a00300f117071601d00c0e810304449580b003601c00007424505d07107207503906160081c1660b401040c03009000180c184800c10010b5040701521fa00c04100a11502d00842c009031080c20001c1040d89030780b07a80c0c3d0321900603c003964000301c00150510510205101d031900c1611002c010414042c945019692250780019010348140c0201610b107208210030310825500441c01076000e01c24128182c0c3e14200800800e59203809800c00601d041c207141d100410071030007500325105694804c4000400b8203522100c9401080100781c8400703040c140009900c0c1c1550f070091183d5500006282007140e0f2441c9810005100c181140c010000d01c2c4084080d0b58982084420006240015124404000d903841c1c01c040a06030b030b00d200c1424001c00c0c0000030528254001d80c11580700e500c2c807180c4142c850f562911070080d40a11030100ca801c1540c20003103111398122900c0050500c0d80702c0d50702c8211552411404500e003442081c0f40b00d00c0703008100214030014500700704495030000108480f544420103684000c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 128864478 1250 128863228 128863243
    0xe0a1a07060b1224011514090102031606140907050d0f1e030503042001080103080901140a030605090f010b1b01060503160305010e01050709120c3302060402060a030905 74
    0xb81c40e8415071105010904c803900c04080c100d1212818481d003607980b40005c0d50051290070f55603010880c0442c00510847d4440004c045154040c0101c81c07071300400d10100714a08011120507a001980c494004101d5004006803580280808006000702c40c141000209805903000c0010001d04829102c0e104200700c00c0740a0807042002070040c000f514044c103024120390304c12141201c44841142c402c21002c4030f8000c28954400c0107a44600c1c06a080d0b07640e03140c25038006004e440c184200d02c640f0440d041518401003e4103101da41d0041643c0d45000d0500c820700c1d401809076141c2c0b140140050010030780f10000da42038018503207506009511106103c500508258101e150103015400c143c1d6102d04050815404481c8184000c2103841c2c0b60003c4582201c00a4035060005400000100980401c144840b81040d0050039080c0c48030b5a11484800f022036108114404c0c600090705030002d0900f803181c1c5c080b81e41584c0c000b800540c135241d400184248111583c1000340b59803100c800007403020800c004c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 128865728 1250 128864478 128864509
    0x2007020f06040605040303020f010204030b0f09030720040c0201020306181b0309060610020c090601030c0201020f0c07090c05040b070f06090b0907080706050f070b0a0902100e0a1a07060b 82
    0xc0b50b480d910380c80018055841400254054480e03070340245004001442191308580d00030324084481d03200d41000110015000d402c10005103c14042c00e40403035805111707484047c8504c9003408640d2149024081030b60304010440302507910500821003d0740b180352071086850031f0003404507040c2d41c540c142d98100c00c0020400003072504000c03040108078200007826a0050100f04d810b1240204442e200303e07a10300046100390303080f140035408136030154000d4011540da21407500001d81484d8140459071050307041015440074691180c039041002014920030701d031b61507419250140c50300307007840c0c1040c6480c81281c100501510008101c1004c0c00b415500c2910055030142d411079940c00d181c11515075641c075a005440c05070040a800240488c0100200d544003003210320b1070390509400e40c0b1008031140000704403030741081d2214099001641c62034003540004016844841c4d10001450901c504c1040c641c0000c01525101700c0b2860044120505079004190701220114003001c3d108045a110748004030071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 128866978 1250 128865728 128865739
    0xa020c0a0510020306090a09030c020d060b0d03051b0316031209151401090501063221010e060105040504050403140d020c0f0109230703050d120f2007020f 68
    0x29042c4024540085004440c1254a0320a5480f10180102107840400004003c00d651001d01001801c0110102c05558043d2000040031140407000c10562400418202c0000c0c00026500084080040c81d4a07104580c0400071414656141c070600f03103c00b003040c1e0103402e01c4901c40034001c412020b50006840e03954004c80c90741c81d038690700304c041c00031300114450815800c85080011410440c0e42c4607044c121286036450303402e030b1034800103d070403607400f10351491040d200c074403026134091002c550052590803203020811a841c100c680a58000340302c1030300910318919144040c401e0f540c0e44203068a013a6642150300040ca8bc48501c1e09803080c4c40032140544c80c1c6080481c0d10b07800d880d0594058803071074500d042a980d0030311041e8041400c842c00e101009140146d1180203401d04000b100c82c460344402c03e03e00715015640c50740c4900b45000490060f81002131100f13010014001c3c0c1e1402500500350b090503080c04400300b40300d0680c0d114403500140e03201c10070700410f03001e0655560b45940240020f0140c80e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 128868228 1250 128866978 128866993
    0x506031305120d2a030f0b0a1202030601060305040302030a110c030a060e010e06060a03060b0102030d0e0601050a0608190b0607020a030f0201090f12030309080913050103020102160b030a020c0a05 86
    0x801c1140e60f00310804654030207160503820400c20110004404440b9003e01c032600101819400030380090000784007981040e07545066051840d2a610120005056003660070824500b4502c100b61624405030040310405081c0f40c14000025000019918001c01c41d00f03040e60802ea134070300c03003e141110003149180e0602c1034200c2e500500030310703074003038007141e00060000e100340824803200d1640c400c01034524035000314011134100042107050340301c01d181c0d840500c150f80c0740c4a60108424141c6a8100e8510201d4003d20010011840d146c044080100050308042d1014980806068819030000340c001d20300d1602c41d014007849541d9513048880240d8001c2c580c04400780c4900380b02c02d03c0100203108070f01241c0c40ba003000c2819032201c0c1020044451080344980000915942100604001c80303041300d418109008000ca140c0d0b072105607010000000000240355030ad140002850b11012002101c00000d0700c001c14020041c50070308a0750710045140340966143c5914000b46e152441c4070074054014041c128 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 128869478 1250 128868228 128868253
    0x13060e0d050d080a1a0a090c090e070e0f01090305031204060b180103051207081e04090608010504060b01050f04050d020d1205030a0b010509010c0b040f0b07050702090f040203070506031305 83
    0x40b01a004141309041081903540d0003030302080051103401d9072540725030044020410540326070045281000140340900049541d0401d5014402d000d8a6074004265510240909824080c1010030715000900c3e2000c020361843c0c840a84a10400c1920b540042e01040002c06118540c1c024400c1460007501944801d140b42101d140c8508003030200b22944d0040d000c2c000c1c1086248020b03a10715a40010a4601d001e102000070700b0303504801d048251010400b4080001d44000612950004206250010030a4074191601c80b049131a00401281030001c28442c01c014007080c2800e45d0142d480030764100e01300c0f0725240005000e2481e0100001c3c140355040203040c41282e440000b95009680d04101400203010410040d0b995008204403503000460055510700412418118690864000c8410f422407040d903850b21031581d00304440c040c0c0031940000b2000114102190080d6024140111a0081d400c1070b07130000c0e0b155841480b41c14403640c80880829540700d44e017a82030703800d240c0c44005c5071241118030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 128870728 1250 128869478 128869487
    0xf120c03030a020a0332071b141306030b01090b030a02090901090209070e06030c2214101418030f060907180516030f06030b04080405090c13060e0d050d 67
    0x403e04034006401206580302503602580122160504d8809802da0f80c066080500590340002c2d00580ba0712400641c445c6940780b0918140700a094012036580c442002751043c0200c0c400d196080143c114a040410408200600d00450640d41242c002140c4000750200080c5070050b9224007035403141d1084280128000c1c1540180c01084c400e44a501300f980d00d6690aa5909410340c0c1d407207401900c20000600c180002000800c00740d80e001c0304040304074454a04004240d00a6002035001040d41e0440804a19003000404030035500c920b4103018007080030b000480680104c0c02800c0341c6c1d01c5c0650507480c140d41d040c0000400f1519403c00c90301d461034140071b002d5460340c6900c5000c0d2244801400340c21600241d0080038410101d0b010a00c40ca52a9098114002d08030002c6400c202a41d410011001509070410107004030702a41e90a9181c43c1090200a04021302802200c60103608000c1502c00d440f141450074202d0b0894101100340000c0c0c440800e54400a1140003803541c0514820b001c6032a421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 128871978 1250 128870728 128870743
    0x60408120c01060608090a0f140d0c0303050c04050112020f0f07150506040504031704080f13090c020706020706030906180b1501090f050f031608060a110304020f120c03030a02 77
    0x3280d0080c800f42c0d82d945015260420195225040c60b040185c80c240410450b2003180b03005072040c1d481f4003952000b108210b0074a100c610403000068940358100003810303458010f00703400605256660385440d1a000010b001c6280941802298540208402d00c0051045041c2c45a4882490b0701d00e0740c4800b070386803042000200c5542034040c18038043c04100d407400e0601c0703180d20840c1c1c03503290341042e12801c4c00451003003280204100d40803401080341103101005d0070301605040010f01001d0f441c190410001c4419146020442001c552100d1400c20250b540001c0d880100e40403400c0000306160142003540140940c400da0103a8501c0105001c820003030005a8070f07200d0030b1071468504030906404011185c0b4100c5101c2e144035020141c409020a24012038400c4814070001c1c200e541880e1054824848203d207580030b943c0c035070800d90820072011200d0003109045559204400e140d40740640c005280f444070119094000d85a070881e481c0c0f035020070007049801c0300c0001e04903030f00d0342e2103064000e5941c00d0303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 128873228 1250 128871978 128871997
    0x102040509101a0a05090f040608031603110a170d0608010219031508060a1d06041407060503010605030a090204020c071404060f05060f16170a0f0806010207031106040812 75
    0x100c83c100c0703400f40d04040203036140103265a40f41482c1c160386800300200da00d409505680c3c800e0fa100000130703400200b0802012166a003170061440b100b42c2d400c020307200c60148440080c07070750446111540041c00107042800c200012100445d00c446010304000018012504a020190b100280605d85ca04040d0748aa60454a81c4d034248681408014521000c1a02e0303c100c001c0c560150000c12191601600200640820207400450844010251915124003038030160794900c034031074122104010501c4440050186410600c0c51945000b00082052000901c800c1480390b441d41d80780d0440d80c1e280c04a504c1d0b0519103080b1450141c445a00b100c0c0f18217003610f09842070340b80c2400001c030714092007107001c100d940080045007044100c15000c01c0c580d022660382503846039a0404400061040e4807004003000b20104a15100e0000c10b40181c00007034040d9078141030042c800200034041c3c6c0c0c0040d014007070707e500c070111a0201000c0c42c0442d0560243c0e412900c0c050069a00ca50641c0e04414080d000b20300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 128874478 1250 128873228 128873249
    0x3031f05040c0c030f022b030c020607080103020108070903120809060604180b04020a05150703020d0c05061b040f17210406052101080a0606150c14010204050910 71
    0xa9450040008a600c0c10618801140401c035410011a018480c0c618428429006560300342002c016090303e081f811f204041d00c0a40a001091035166251140d00c40c4100c0c0d47c0010705043c1410303100074000380814400281008440400104402d01c00c100300c0001315807010441d800c2207910a0054100d1030111014212407241340c0014a162500d40591404e02100d83c1102171580820780b00c0c510070302c40080081c0e810881c039181c001a42d0305c40d80401208001d80440c0b46448034490325000341004000d401d240c04001400c2800d0004c2880403501e00c0e08000c4002041ea0740060b40c0009004500541d40b0459940c0c00410b40058003990410106544900362015241c0042e00e81c1000441003030b50079604504400e00748010700c41140a100180340e018180c0101481c010003030204601c0c070302402d821886841d0441d800640411813280a071074058242d114204d40f50300c82d5003c0003440f034940e001001d400146409010310324a8020341c100c0d40036107009481c0d612189007421140010103518410004800e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 128875728 1250 128874478 128874541
    0x10f1a0711180906061c03030e07051c0302010c08100504020d0e0607030606090807080607140702130f0b100206060f010306030605070c020a060503060f060a0e1e0a0609050306040807140303 83
    0x611b40015403c2e140c000d1000c1c1d03505440180d44048004240890b5141c1079449a03990225807a611100da040e5488404a081042170720301d445c00a095a852200100521006505004100c110207100c80c040c0c80c0107031401611808a40401030280040520000042c003552045c0500f02e40d058110505a41290b11400301d519030715608140d075041e092048110981029002c60801485500e1004100300103140c1107080c0049030f000a548a003071101c021000e03560b5031600e0449180a40101c06c20141d049035210540c10303103d04065143c0308001c1c550780c0f19009100e403440d007603070203648658040c58002e20b013007002c3c1c908644003a16400c2030620903441040c2c0c00ca03000611a10420440e442000c014007504501800c241c01d002c26908803034800000d00000740d010300503a071603000e03295050303070301c89485103c1610b840402d024220f070142c0c00000030440c100e242880a80c50000d0416042980880801e81d1400030b8140701c2c03020031041881a52600000090284032411104c5400206442408407480e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 128876978 1250 128875728 128875741
    0x6020d0c0809070905040f05010507030c03060603020909150406031703090c120c0d080403201908120309071a03060a0e01120f1416030605010f1a0711180906 69
    0xc07510440341c6080c158000002403003554515000310750850310400d46a481c5002ca5a1070380c2c01e44070111288800296512540d108441d41801048001c2200e82821842c2c0480800800c5443d10f00400b80b2801094000f40e119254650b07521140045410038050005203510b406120200e034002e803180c0e841445510120441c900d011101e8880c00c3d0040c6009003c10240340041c044044803621003611051000d220010120300400c1d00f480d5070b43e0740b641a2160030113244007080703400a440306114250400300d64050050040c0011900030089000440b15100e6403100019842c0c8500340d0040e1a1100c40e41c50701d901406240c201840c090304e0126030449101d51030707048078481c4110901c5400389180a00c80d08402107000c00c5034038902c20340150f086070031000b04540d00d00d1400c46155803408905420600070420f0003214071a80e030140c03440c40312200100b0303c0d04140c808078403184021061014000600b80d0104521b00e0341c82004010302500c2880068919100c03010003000c1100c00c22200c1c020741002522 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 128878228 1250 128876978 128876987
    0xd06020706050601050c071208070b070c1713050103050a0608010c090303230d0b01170c0a031407020d050d0b041104080c030c03030a030f1401030b010312110312071b06020d0c 77
    0x102064006c00401c1034a00c1c0807000361603183e40100540e81c01200b003204101050100071030300e101e003019890b000300030001e41c40d000e0817404213003804409040c0d050204031405207101c1d91450444600346000325043d280c114000313000308034031b5010078403c2d841c2400740a040d50308620002c040301c2c069124035081100c10200120703c81c18042c605510440304020200c40c0c6a419400501412010300d4114a409520301109000c0c90f002d5900b100030000200c2d91126569041c06035242445030791103260414100408080c0d03a848184100c102840790224100d40c00c55282e5100c203a200c80000d0040c0620b064001030f4a01e43e500030701520040f405541e28044030f5040014205600c40c00c0a00150f18091603a002180180306608006425548410070302580b1805210110f010710302801c450320181d451440c00c0900030040c0b0300d504050040001c410308072000d011081d2031610b2034403040c0343c03402e50307880c041200c0b007003c200200281d41d000340001e503060180b154054002903202140400c0807a034000780030b44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 128879478 1250 128878228 128878237
    0x10f03090b010302011409090702100e0705030a0b07050d0f0b10030e100f09050109080c0d080c04030308040c1e050321040909170315090c07021305060105090d0602070605060105 78
    0xc000918401c01000103522403041110503101511a10f0308080501d4002440c01d03800762183c800580c402088501150440c2c840c42101c2c0103c0c500400c0250324190201c1d4482c450090043c0c0000c2c5487d00050b201070044084440340e0005c22820089c410300c07844a08002e150702810580110380110a122205000b407107101511500390b40140b42200e140e00564002d031101d100d00c09070282c1c80c0c0d402080003940034010404090711504225407510307059001140381c03a40d420032600400c0800c41c280040007240104443c00d0f65010b14005c0c140d80c2d643d04298040c103401d580444060248000300c2c500c6e0200824604084d50012420f40b440505003c3c000505070409214203460048200410041a1025403164098a2003110112240480c0410450140d0402c54807080b070121602c0c0d0140b20752804051695104403088401c2e400e1005540220f06540c0349a00003190341c6503200d0225105a0007601950f42450004101c0301121105242c00c0e4084e400c10042218554100800b090b441d6000c0c50944 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 128880728 1250 128879478 128879483
    0xc0905010f0e040e07080f070306051005060f07020406030c0e19020901200a0f0812010e0f1f0509011203020c09040201271d150306060907030903090b0408010b010f0309 74
    0x148102c4031030701088001c0a5030001c084251048036400a000902030241c03182d0f089905c0050300205156040460035288010069640403075a02020b02c441d0b40d8a1090310005d8000d050b15a4413858188007050007029560405842201c142500142180c400b211082c400c203250b500383c020703840c9074048035406c2c0c0c007500105a01140b510a00000401e034803d400d203400d01f0802040320300e140303d181c0358a449800104001c2d104100e0001c0e000400e004000189401801c01000e000b200749405412011521009086401d4400d29980064007030b000180c40d2030f0280000501403141540d60395500c0391113031003211049000d0301400e25099014036026589512030346d01070f110907080300034028400405280f0281121a2156a0340002c01c0703240c40c0c1e002450740c0887d0741e5121815030410f50701700010190a141a44d2103640500100f20b02500d8100072aa0814890305020501c2840c514082d030302d20702d00f0740062035041c8010400240b468015046814260400c4c0c84410300c042048408030700741d0342503d102 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 128881978 1250 128880728 128880737
    0x6060b1b0c0406051026070504080d1b06050a090b0106050903010b0901030c0302150c0a0609060b09130212030d0f0902090f0c0a120902060a0c2a090c020109050d030c0905010f 77
    0x1c064651b01404c54000c65210300a50741e03520001300d090700c1948000984aa20020307801090074007031004200b05d07c40c058078140c1041300e81200c0d00051501d44101030300000b0b04e1152903902040f400e100e590882440c0603403290794601e0b15038440000070542d401c41c03000070780b1a60800b801040241851880e0700d051382e030000e0004c41804e085400340b0241c0040724030440c0603503900300154109140240300540000e44240004580440c46041c0700c415145d21260840c4a0407001040c440a2805900d8044803164140d400700c1d004a00c500120f0f04600610300c3e1140f2030f50070144072030505612948049001c6108a401c01001e496988400400308022511880810410402442818042e58603040c051756100070200d01681d0139030101b10550402c4401102203001f5402200070054a041d00c400416080c4056440c8000705122281500000388105106180c0c0e801c0b68407a000d02c02c2d0001e0615541110840740c8502244030000c00404206000c60b0001d00c0c45540825036610451181115a006507075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 128883228 1250 128881978 128881999
    0x70614040c210b0403021608100c090b0306120f0d03020c0607020102030105100305090a0807060203070905300a020d1a010b030609180a050d030b120307020603011206060b1b0c040605 80
    0xb00c030410f149000d8015402d5100d144911101c1c0030302d0203094805441e951005d0444040071404907002e895400038000140b1a04507400e2005e0700ca40403e13258041021101d04820f04440b85259040035031040442005010b400604e4420b0f542540040808544c100704564140d500d030030f8124206c2c0401e0045079400101017441d40c0034076109400c090341002c2cae0b04054030b100706607503030318205140e00603401140d1036a004010000302c0e82e0031085c000000d11082d6041001d10301e0798000380001050340c0c054046464040010044030010801c4225203240d4040c01240d50803083d420101040c292030b0301441204007031100080390a880b0002500d0003088054654582d50311003140c420049411004800b103507101d0140517802003481040386102d01449600c0c00109504000300b441a00148c1d400240540d0340204403840058070b50200b100d0441d250309030b44e4001c5518901d800c1001c1d018941c0041d00b1400302040031010348482c2005001405a0407046410045940b411300c005e44220348901e0b60310810215 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 128884478 1250 128883228 128883233
    0x70b0a050307121506170703060608010909052505130c0c02060702010302070209100504060f08060f06270601320f0c010515010e010507050303011505070614040c21 72
    0xb810118292a1490202e9401113441e15a6031075246a031000f80000c4152401103d420450350b0419000355461906115050600300d0141c0b0140b03042c8140b44905903504e406906002c000d03c02254160f28580d000290316100080d24200040c1d40d010f600d101c1d0b064aa01c1030340b4400580b0070b40782c0395000703500d0301007500b01c00c2d400304a11a0880c9078183d050640030440e250040c0e07180500399210b01e903d045032a03010341c2094103200c1240c1054002a440d1105a502406a680e00240c0c070b9074040016000d800543d80c5103004a080319880407911200e5450b010000c1c0706550440c040188100002e98590391001c001920071a035070001c90f5640b43d00144808011000e01c4040d000500306203050359521803030718007100040e5017102ea044403650720140d0040c0340da85196038400d42e01c60042809180547c141403094440984900c410f01c1081c4410f0754111448080707d0242d81612906900000d040103004c1e01d400034568000004c43e0229070380b02480340c0200350142d00bd0f1840260070100c080d00040d01d191036 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 128885728 1250 128884478 128884487
    0xb130227130303022a010510030519050c03060903030a0b0904030c140c06040e090c060f040e13021003200c0a060506060c0712060e0304120b280e070b0a050307 70
    0x40ca068003016001c05c030800c2d5941d00060741c00070b4240c001c45100e01d910303607840450b82100d01c05001e80e14090711103170040011803070003c0d04a010386c503040042c0d181c030325052502c2c614040710f0002654040c0900020860b02c2a0044041c501c01d01501c03209209071406ca13410481400400c40d00200401d108004020118198020740505a04920215580451440002000758205074804d818003510882004035040301400410a050415540181031010034030711040140560301554219002c2500081c02003082c240b010103a0700c1c2c0117411584c501d4070b180f41c01000350402000142c140c600d1890a00c880c20030040c00c0390a22031800380900092100e42e5030b43d002410300909035540c81002440034454024081c40341ca0024600808441481c80d503e10300f41094030004181c62503140c02c06d0004200002419410008403135020f18120030b02e940d001d0700c000300c080108415401d103100c008911501c00203c1d51001d040040508100d030241507403400300e04c7c2d15100300c0c1940c100240d02072000c903c025000f03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 128886978 1250 128885728 128885761
    0x30b0a0608010c27051c050f031614030d050c0414010801060f03110403060204060908060c0301050f0f03031611120f030906070c08032718160207030b130227 69
    0x1306005110a02c0d904c0001881c0005842c1c03010803802c0240c40460b04004040103401308000000d0061401c00400d9102e03060000c51070500502180b040c03070f1000c81c60900504c2282c282c0e1900c0d0b042007140f03042066150040360040e02811030b100c1b10002030452550302626419040700c41681c0c0c2d0030304044007040120041c00080e4151948030702c2c1448080002101c900141010b880f10390350340110070f071400e5482490a480a00080b141d0602000144001d480700c0f03d81440c40030080d1058020500341d000403929510591244015032100111494204417225001041290341250400c01031408841d5254880c0c1c400d2404541c941e10401182500c1d003001d5018002440c0034203020245c041d610310140b4203582c482c410142200f40d84000529200098005149500505072156544c507006120406200d2102518a42c400c030580c03403441c09d04500c2003100e40701035580f1040d104003c2c180642d07000e4000c0b09415007203109420604040b0079401c9a004e442402100d488201800340e1520010030408958 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 128888228 1250 128886978 128887037
    0xf06060903070308072006040602070b0906070f0b010e07020111041e080d08220506070e0f060a0e040f050601080408070c0b030708090708062a0c010501030b0a0608010c 74
    0x100080000410313101809024810b0140c0d007210302010750591004041c80018a0aa11584080c402480304035030004030002600d4840802d84d43d902c031021300007040d50103040780040c600304141c41d0020400c0003e0348000d040f505407401c4444903481d40b0074142c0c241ca415201e1205000418442003007805003815104103a00900610356010341d449070141801e01142120840c04501c4490500c102c04000100c4050b241e90281089103c408890b51001c1d100c1c07002608250800215609007501c590b06c010381c1800701c0400a21880c2d4035119040094040007204040c14030442c81c0144688802c0c107507020341441081c050b074424095a0311559500c8050b0003000c402c5d98098241180481d5031422080150300808450b120840f40d8944694034924003081d64010f880c15070040014481c25100d5032803c0205c0c1041045900b49001041c0e10700c004500824062310120343c01d003800002070102d0303101d4150050401d4101840101d484617403031130a841d80408200c0c0020101d5500c04004210b8201c114180c96 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 128889478 1250 128888228 128888233
    0x60f1204020d120809060c09061215190305100501080a031d210618060a0b0105090d03030902120c0d0201051b010c0f03230105010c031b03080a050901050f06060903 72
    0x29041d45881184400c0b005900c0f020035501c100b0f000174400200b103c01d6012400d4034540d40390410400200703003103008410403e03002e2001d007030201e0703044d404601c4207003400100506203441c620280780a4000420321440140c80d50b0148400140022426006050698405000515455109a4046450703c141044400c034910003049002081d95490142d10801484100004240b0b00c0c140c0441d4140440038040448144910311010000c5a020500c82d5000032886000216036a100c0d0041c0e8403071141448040e404950b00050401300b54140c1c6c0040880c500039104502400180ca0480b655460705c070710071550104504840300010b62142c4010a01c0000b8598503040034098a0345090035500541b2100700441c40703220203921010341c984110b12074544c00c1100000b0070740540b01c0c000a043d4042c0603040c108100c15118405160240510008036100002e841d81d07001042c2c10024460308044e034010a89038200717401f1a0415105008050103410b0700b856140b259203c540030041164044c00d0742c0c0c0c0d00b60 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 128890728 1250 128889478 128889499
    0x70b16170f0414010c050c1e090903040806100b0d0b040906090501050708090307020a031b0308030a021e0405031f06080d02010b180c0304060e0c0d0302010c0e060f120402 75
    0x382a900240441d07560000d2020380381c5081c01e50003841c4403600c044081c1001107410b0340b4400314400250800b110902078460030155010040c01c450005460f8420a400503008000d0000062000000307104542145055502c0d43e2207100a076100d145c15031150483d820380910040c4217a1456a010703e60440004000082010740c954540050300c40c400c5082c0c0d001e0359210300f00122a601700c1000c6a200340381c40701441c80c190345130340000c07046a0349010141450242c0c141d0441000c191008820196410041103922490a40c0500d000307544201c0e5a1004840703c0007454010203000e10940c0c0076104018090f0040400c440a80e041490404121000150f2a070000040c0e4600c10700815041c0c18141c1c1c00804c08284100c2071141301c0c92640312a0a6100f103a8082102040e0420143c030b0700140c0c01a404a11030b444074000c42e103809245204180c2c13041038940100c0415805520031007041d10780d6180d1003210203607001045070a029005c004000001c0c104401da500c040012049948148000c0280001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 128891978 1250 128890728 128890763
    0x280906020d03050624070b06060306150306030a061815020703080604020904110301060e010905030f0601060c08071b05101103030c13030803270721061823070b16 71
    0x850201c900c5c038441c011400500142840403002d00c3d04da11410640703043c0d2031410a007000c03510ba007041a054208094010020070401d950901410490a400c0401804181c1c40c145074140148015182100c030000b4400d8900c085105e01d009941d441600341c4c40b03200b00769442c0020300000c0d510002d1078507801907442e004041104410009507019040369903c5000f00c00f500f2001410750302c2036810491190f403040003160351142c00043c01c0c0d41941c0c45490301382c0c0490550314110806000310000282011004a011200406280e28020840f0001c035051080e2074041d04003942c01c41410f07004400d15404c1003001511518200c00242100004103254026450343ca403a8040d9540040d01c001c40740c400342809054082108040d42c80e645a20440940829031032710404000f02d81d00103854900019280d8111030600c42c441d0720111200d0b09040d034280340c82c511031602804610300c04550040c4d0f942c08900003001000006096401e41d0500c1914a1800001d1044191624445034086480030380c07564201d2203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 128893228 1250 128891978 128892019
    0x20310110c010e012c03041208040308030106081e041703070909050c0301082104030609060e01020307020a0501060f030f15180c0315090b06040b060f280906020d030506 74
    0x1541c0c0c400c00000560f640c5c03031011030001c64410440c1c10201c0045010f220a0031100841100e04480b040021008140720900d083c1002c0e005550025010000c0407000140b0301d41c018890a109102c00051802d000d40601c542214000d82950050507226444050b0402d4480b440b005540154080c180f90780f54a6490b00910140d030760450f0140d204400100040007000410002c080350308203880c40040310b110501d003181040340254440030300341c5501e5a003118140b086960080c80c0142903400290368a1030125400303941c41c21181c0080758290300e400000a001c44202ea40c80c4280c991045c68002050319070386030f2007584010301e101700d402c00e40d491018081c50000b03403c0ca02101407041107582000e600d181800402c00c0b018002d9800000d042c40d84d01c0c00003c000b40342c607540c4500100c4002600743c40d00800300780349019152008001100c0084d941800c45080c0b2007001032100c0c54000342081d0850400304440c0c03c4aa44596400744e80320b1700d80b2101d036074083d4104513400311000d00401101500c056a181 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 128894478 1250 128893228 128893241
    0x1403040b1801180506070503040519030311180a0b040b09060c07080607080403080903041a0a0905040501090f05010f05010822020a06080a0b011805011110050907081504020310110c01 80
    0x1c0060b41402c4810b007001310a11280c5c2d804081030801c1d604618090701c0e0380d0780302c141450030b4079251120b0300c24050800d03000344c1c01039203510400c10411b9110348121080b8144120b001c8115842295640000035404148000f2039044e00c808a60b61030410f200c0740e0522403d42c2150460200300c1c040e04c0004a42040c0804c0b51fa841004143d59501c141d040606020701542c1015100780d100b908100300034490f12241e2082001c0c10b00310500c000f0b54800751500c04460501080d0001c590040c04c1c540001010400d581210030050014803042000380d0361401c64100703a10003441140d000c21031110016403541c0000d0340c03542d11901c40f01000d0700421030907400a45a156550480c4001c104410280300460700548100c2e4040f003070a01700051441c0c07600030030703800d400d950348140c90400c510f100001183c1e20050007148002010f4060610040c01c0c1a950192a09000d00a01841d0f01c11100c5080340d45101e80030840c0155000b0300a08942c11100549101030185040c00c4881c00c9070400c010240403809200b0742 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 128895728 1250 128894478 128894501
    0x1090b070f080c032a0607050c0312100513050907050625050a030809011406040e030409060b180a1a0304030e09181b060d0c02070302100305060307061403040b1801 72
    0x10b6945900d90070306850001c24103c205c0f940818103501a041c1c0140000300d85030080400c0c144280c0311448410400c0c0fa501c03c00c81e00e42c1c50108000c051040681000c502d0500381d42c411a0158203100181e034981d0304603801103d002e4a075a1119004001d40d051810040c0030500c414441d44041c0032401d0304441401c915240102c0b055400095094141a40891038a403c80b510303400a01000900034617407a01325801820042c4075550710341110503000010007c44000300054441404816074440c40d405098010f04a46010340c40701415920545c601025800155141400ca00601e01040000154190002003084040c04201c006500151369a918880e20800031480a1071240181110290901e0580000c550b001050112020380c0360703031508259412014501070008005804840c228a44582e235400a03403c070510b03448204080741e058200c18821401501200c0d11107a0b030302c07401c0b907814415240d2100032440c00e00200b80000e00d0304600d0ba800061068007940d05101c60030700c16085030711480b40d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 128896978 1250 128895728 128895733
    0x20304030b010e0103081903152c0603070308070f150912030b01020a030302070218010e0103110f010c021e130209120d021504080c010203040809030f0c01090b070f080c 74
    0xc0040044504405024101d0340d07004002651443d0350710f490700d02030640320140356404901101c0c1c0b03661296201030f6100c1d14010700515415076850050110714811407110603140110000c642d5030010300c070092400340c0d00250007001e0580c61500c440e09070b5042a082180c0104000d44810082440031940c0b6814400c0b40f040010300240c1c40c0b0b413943c0c90b43d80d036454140c00c3c1400c11754420b00c66a00031401b0103141d5014140503a85031403901c0054150581e000c4800300c55018180045240c0941c105e03403d06a900c1612018140b0602380d080000740d50350000e80710f00046021440c1401820300d401e1041418034041224a8820300001c001030840c40c288100d00901580456030205034585080464042040040a001000320740c940003510782c19001052480724485001040030420102c080702d0039854210f000715142c5c2407038904058181d10000304584240306206040c141e10b2000b0038005d10802c016100c41185910f400c41b006d0040d04940c00540e01e2440c2c0d00d121001003085a4010000b56221001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 128898228 1250 128896978 128896987
    0x61b030203190501060e0d060608060408090a0e06060403020d081201080d0216031a040c09141b03091b0f1503100609030507050418080a0201051816170a05030a0203 72
    0x14840580b21000c10150080c50400c00104000c540010484c4a041010340c2c65813200445800c204000d003005600c6074219200d920100402c0c80810400b40241c1d81c0200c40c900e07402c2d03903607800b0001401419903145600000c100410001440c2c18080c40c1c1d0510320602d0329030f05280840721640d0300303180240c2c804c118680103c1142195a035040c0000048424201443c80c552401c5803a00402890945040404c050258020400740000224604002d00c40f504003030003084c0d0049440c01301e1142c2600e601c2038808100034080001c0c0003040c2034900c6120000c006200c1201400c2d10300c0b0003905080d40c40b40d008036540440c03060946a05803144c1c3c0210351040c1c130699a0400720540001c0c8400382c0d000b44100511381a0500010340003240b41130440341b0480340400e842410000c0b603100102d84e01d000a0000c800002d050301ca8a03019007005220f40842d0221161941c0715010064455602e44a004500380c1072071400d001c0400780c03800c5a03460310034240450310314418039511076241d50300c03134010700b0050703031010a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 128899478 1250 128898228 128898241
    0x14072f010e070608010b0f03060d0c0f09020408061b0904090212070b03041704080d0309050304090e061b0a0f11070b040f210b070e040902030d030209040b0414070c061b030203 77
    0xa010f1780113000c0d4001c2c691610420888000d03d031b01000d080c0611916001e00d086042c004010039040280c2880e04900d05003d95420380f400c020761051003105001d0003500002070f14020081c1540d02c145001d5400245885085d03002c120042201c0402240c0c00740000341c16068046040100101604141072110f5a030308003410200c1c540405c404080c80c207404100f00500191102003110f007140da0b040d08001c9030f104100d251240c11405540c0000060600d044941c80d042d030780000b00c141c083e020303c14a000035800706100d03149a911520590b980815640d100c803200c00c82c480c03071000107004810720503113059580751b200101d55a40f0990262400100c021018040e4401001b5074201400d03a2814207000ca621a980720b91000304010280805e1248618009803d500c403508244559a4000c0c2641d94644100c2c9001c2d000707400941c1c64500072858494000000c0c02d262080c41070035011844009015503c901d02100c040c03012803011076010b40c0300d03009405280610008801c1c03907440d5403400350302e03441c128 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 128900728 1250 128899478 128899487
    0x60203180915010804150c03140a05270a080307020703020102240a0b120706022802031b0102030c01090606050f0102011e0c1107080307030314072f010e0706 69
    0x5000080c8034007030500a01400c0c007810301402c289014207003440030507592207003800548800310541e003503c2d0600704400507a8440d4194007500241c3c450f412454100d840350035101c422500210ba0f83c1c421810789a03e100014100004004045044c100072140011469660045160019201d03d005070340f103c2024405c40d1307018800051407008011070556959440ea0f040e0714505406480c90b00301d50b076602000b003041d44881e0644401c80d2070b005e003100d10309540d4440c02581c400905003040c00f5000b40900840d822107180314005115034005000700b2000c20000884d01800f10905544c41c1584010030500e11985001e014201c10903014040001d08580b506052002511140781842c1c11640b4107040805603403291942e80c0c1c1043c0741b15800003044800c28406a810030103620340c200d2984112400020704140002c01000080e21039901480003020800b81e400000c0420358881000c03481b6004071000f5030721151035000f41e000d809011903034419905d141042c00c480306d02034561844e801c104010301c42135800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 128901978 1250 128900728 128900767
    0x18011e06090b01170402041805031201090f0603031d010e0d060c0207090e1510050607080301080c01020102070210050a1404120201031a0d0201050706020403140d030608120d15080106060203 83
    0x3804c1c407210030a642070401004210090009200d02e540350088400b80d82e60303002031102d0ba030303011040300d0707071640070801d2618000c0d0f0034481c000200381803800410403840140601d004580c1c5c141c43d41e1001c410700070303492420403d5441c0001d04100f52500c3c0341e40307540e5503440c0302911140208000180300c3c0d82d00310000d0810803260004001182400d001250a00e400159240c80c90318512804000d601c808249944108059125070b51001010800310240039450340118125040c003002c0314802c0140c50300583c20b07402050070113035001d0580d040684010380070300c0085c40346040c185014a8007101c2e080072043c0e00d401c1038000d0010500514514411942c0503c50b074803c243c000840390b40f40a5100c000905036004000000b4100240446c0319410480340342c0540780955801400e4449503890000344c240c1c1c40e0086035030403000a091031000502c0302c00200303a1a07144c3c16525005440d01c0c544080040240402000c5900203110314007001814003401c0c030681c00501242d901071580d42c8110001e03490000c15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 128903228 1250 128901978 128902001
    0x60709060216050901030809010e15040509161e02030403021003053301030c0c050d020c03100515010503090c090103051006080c03060a181b03020109080d0818011e0609 74
    0xa48142c180000d5841e0300d8040d0459500c01452030b50340005000481e08600004281c40d0004110b80d82c04400310800d074084e00598506842e42c40c4181d6451100109454045034a50045001c0c8334801d580780c410b0183c00d06a410403401100e00d05640d80c1e010440c20b80302c1c0b1f614140041d07580d00600c094100000d855041c0c0301078241d010340324000c510300b400850b404d007403c103203060540d950b1320354481c20b0041c645d80d4150f03034002c0d0070f49070080c0141c0c902945400030142e107941302c1c3c003451f00b0301d008803415440f849001e11160200c0c171003074044140055a256001070040c3d603141c0b16411014140703960b5544210b01075481580517195102003681c112068030550b070095038075600f14003580c4c5c0352500d00055066000d40c0081001c609501050701c0e101c4041d4032400040c201000c011004a0702d0000b80d98884101ca2013070341d82d06400c0e6035404080381c03103200000d0410700252a0b040480c94017100f10303035124501c030300c41000002d4803e1458549004810305152140195840e800c0070044000f0512600d00c6652 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 128904478 1250 128903228 128903263
    0x9073506040902010f1b0b1303030b0603090615060d091b05040902090406021e160b0a05061f090b1201030203010e0609120d0213030605040b0702010b0607021e030607090602 76
    0x955550010301500c0c8003c1105c0e0410003034100390451200c0c43d48107044015044035400c038041c200083c203500c0c088407000c03041d40072074180f1304251500e042c004102c3c1d124590140c00751140c0d48520245503a02800c0203200ea5028006001f0364401c42820f04c90b030a5110301c04c003002c024499004071142020307002d9034441803080d80b80c040c0000250300c562507a55170043c2e02031340050303680d5040c2d6960224201249802107c011021419212029604082c2250701e80509030191243c0c2c0c07043c4180c03050342c204484860f000301042440380d404a81442c40955031248506003501615102c0c1480c4425030424480c40c41c0700c1c1d450f10010406c2d82400c0c45100b8490715104040e085070318083c01c55960300c4103400c81d5012a0800042c03d035080ca41184d0644003020541c8018090640d901d0501002800e0306407000c1d6120241c2801149003540144140007083c98064a040d007001059001c20602560503046888110490700010009540c14010284a102035813a103002030b60414100900d4000c00114416420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128905728 1250 128904478 128904491
    0x607080c0307111f051317161a040b090d02040c0e090901090302030f13080106030303050601180305100b0402090901060c2303030112030c1a0108010e010b09060907350604 75
    0x407404135640d68809000c1d810000c0e507480c0f038000285065521580708094a908165660b1404000424242d50045081c101c10078040c2e2124901110f00322004901c210780042040304100b1007003100c01820401100070960214550f59030041070660700000c40d8400041d090b5400040e0b01d04e043c10603941c000044030003c009040d4030b660080c0d035a200d501c0b01c900010b080403c0c04404034010020400180410070001e0010aa803440d0240240905564040c0071078bc102500c0c400042c40743d0804400c40f60080700518034a00c0804100c00101201d0000a8001da020001c0d01c03201d486540070a0f0003480702e42c0c0c581c40301d441c850500604440d04441c22105801c600100c0302080a00003007600e040d032341110203e42540c401440d0995029030003102c001d00c02003188911090942a1100050403108464024803100740c200420600701d540300d841199112607030201064050070103e108503803040480c2000d035404520f8401001b41421880382c0003100c2084a82e00c0c2d0716114145070090b821110907582408030307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 128906978 1250 128905728 128905759
    0x60e191e050603070f0303050a140a080f0c090a0f0503060f1014131803021e03070b13020a230a050105090d0501110703030b04050105030a0b0c090607080c030711 71
    0x1580c22000400480e00d84400c081241603506214200c010003449144030701c416500e00d80030301280c21040b07a0b040810480e210960301041c82d0320440301c3c0780859a543c0031650f42c9040030309210744005030511008140900012116031100c045100107030840300a04a2543e14020405162403c000c001b1500d083c200c1092080500c22454048144d40051072032400e5984440c01052a040e820031400b0313915410f1241d03214138542265644111940240d00b520803c0184200141c0c0640f103084090140f43e2003003281402041745c0640690b08284100c10302841c0031b45030b0300003a03550400d60304103445240000c0107035982d140c04c01140c008090700964224818620b0180003a01c140101240b00b4040c0107180340880421100790f00c0009a60a80307000c65445400c1410024003c14400e45010b000303602d40400400d00749400070311f0030505c0390f2040b45000c20b5550b244600c5082d8100131000354200130103000520000c0c503402c000d4501041000300031621081c80b802e00d030b100151040c058501500700303181c11011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 128908228 1250 128906978 128907011
    0x1110702040b1503130807020a090b0f330706052e0b070b04020a051c03090b040e06010c031809090510200a090506030103120f0e0604090b060904060e19 67
    0x10305c0a44450f0420f101e04807410070042c41d1054200080d07001184c6a13011502c14940c1e84075011600d01614000360041b440030600507444520901c2d011105504400c641220614801038980316002c440014104622a030b100f40a03035106840c07007179407000490041d4040e5000c00a004c82500000d107803070140c0328030b00288e080b035510038544042c0c8038145c0d0741d00180654a49000610040030058018600b0003a00000c1c1e8007001c43c400c00813000159000e00000d41403000c0016074081c1c644c0d05150145640390038006541c0900c01040450910080101d0b00c003100c4e240800704001030141340800f141c00c010901d003450804020903401400e2a00d01400c0c880003503524146142134064100711181d585901403010b490f0140581e0006038041000400442080001c410140044400351503c0e030041d81a201c2c00d403142c032460720f00c030354004c0814003081100006503000a00348810241c4840d18124844000c101134482d2134220003a52044070061040c4071100840041d01107008003001c004805422200070b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 128909478 1250 128908228 128908231
    0x605030103030806220b10020606030c010503192d020304030806011b0b010b131706060d060e010504060c0e03341701060503010b060306180a0e01110702040b1503 71
    0xb020040d008000440f141c4429000500f64241c602d410602c40d081481490040c3c051361050a0285110400010f00380d03000080c0c1600801000740544280503150004450076040141a12000407180c0074a23210384056100354040146180c14004c800809150070f40b0500c44412090402288100104400300744d01c03400c0300f43c00030000d00e8041680514440c04030005003440d140030700403c10000001640c840c032300c03004041419000c0d032280d02060b5201c0102d4114803c0008002030742d04004000781c0c0038586034484e0075605100d0701d40001e180304c01c51085821180c2c1103800701c803d0f9650b080d0403201180c00040c01c800451080f001070141d12407480405185a2240c1b002c0c45010103a50310400e000c901500c60280544000340c1480402d00c070780016180601094843e0500951030701c0c045900b00e040030003c07284038201c003a122510484003440300304076154004100000c295683c2e8444c0c2c419100a018008a442c41e1003441912120310703004001c11100350b003003001c4c494441c140f20400e40040800c04c0d43d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 128910728 1250 128909478 128909483
    0xd06090c0e0c0a030b13020a03020304020f0907050703030902062a060108030a0c0201030b04020c0303040804140418080304052b09090203040f0b0c090a0b030406050703050402090604090c120b061002070605030103 93
    0xc17030b03034414410120340301c400c00b240041107440c008102500c0c080e5166000d0761240e402101c601410681903418030404030401e40d02c0c02e0021b17404018020100e03001e40c01131005944003400580c6000d20640d2034442e1034240c91144046079840401d407400d014400c2162501601041024500d017038052040a850702c100c401e4001d05160715000b000c00315941c0d1760305446185503030b0304c10b0305e60b64640b503d040c1102e64801e0041d0030f021001c2058001490815110f0440181000c10903404c0505050319221a40e40008204603130f213100c0d091002d807140e2010000d40e104d403d804181001d283c000788070050007410081e0015070320740d03106208020118000151041103283c0003048a0441e4440c2c0b41508241e100e001d52094101b008480001404160140250b02c2036014040801241d103c006044054880564020b540901c140b004030f2403500c3c00d030703000031000c0384104200f1228580e5030b07456845401003d0000d94040080808001c5181403200b20790001d5076003031003d4070003e030402101403d07501040c00003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 128911978 1250 128910728 128910731
    0x108100605010e10050415050403020a0b04031208060613030501051801050c0a110f0304061d1008061005070203010e0601030b010b0c0a060c0324060e010314011802090d06090c0e0c0a03 81
    0xc903000d2a028401b118080c003030094403503180d81d46448015141e03510034441203014030003040e0002440c074159401d036410b0340c1d885803001c00039480c6c18001b15000b68018000e550b106104110404007203a0f41c0c0c59042c02036101c0e40010699151145400591000001145815906180402c40b40341d0941c0c04a8000c000c140c00d018030038030380345c044080c070b0103111002c080c1da0341c400002d000c0b0301d030b580110b00c140900150f120100110082c50043c44840301e0355880c4400450204004500c4500e051441c1690180c41d503e0131030709082d001d0b00042c1c04d440c104001007640fa004640140203006103136031110b0152541485844c540703d58480301070341c1c899915002800050742c03401c1c14044a407090700408030004140d03401d468030743c540690806a840c0984203210114001c80600c0d812540a4001c0815018900d01012080d030720f80401e445903040c41061841c3c07416403c2000400c9680c40c007402144c9070380a59800103002c013051804110340c0b072040d04504110b40341c1d00c0c10081d8050400c03003103482081c5140f60 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 128913228 1250 128911978 128911999
    0x50a2f04050915180d1e030b0112060e04050c030601150507030e06040e09010b120c0405040c17030c1002090a06182402060c04030f0b0403120f050108100605010e 71
    0x590303403d0400002c400d45800b003038641404014601c0c21050040243e00b0b03800c0c0c801095003040160f440345415617012260100d05903100c08118001e5000d0051280306040403580341488581420071162a0b801c070045803c900e10500c01400b2040107050615030099000b0545941070002107040300030801c4c0c652040150003e8650101841040c44010245010340b044e0f4840d40c40312910408400202e981c40c0481d0300c1c040403c55145081d18005019480c80009401c24038030480c144809043e000300300ba50400400034001482007414081d00e000d0b0041031000d103485038141c03490300d424500d1500d0369941c02c50051004250310340e40d4014400489509003020b8980320658101c0702900c00301a80705240303c0450821299234401444099841380d08203509680e110f45c1c4094006583d4029800060301c081122205140015004401c00d82c01c81c0c000e007440e519041e2865214410f4808040310320f19407030f07100c03001000480410840c01d0040447c00308240681410500003d104420380101c0714420101c40c01c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 128914478 1250 128913228 128913241
    0x1502131208070b01091a030114071d03070303050a110a0812270c0109080f0604080c0a080a02010b010e0f1f0e040204091505061207051305030604050a2f0405 69
    0x402c0324192640004842d106603990101c18000b012100034540240c21041180000e514041c4107241022864801d14078103030311610402c1b10310003401002d04202804400c0310715410340e01002140c000b9071003651703416600c0c41c055400604000801114131090b038413015000d80000c500318181c86144016402c01081c90f90f903130390b9486006001044203500a800c48001291914020030490b90170701e400e8a031403160a5844850b150388001c6c2100440c0360390400c5001c00c0c00038400a0043c02144841d40441307230700f110303e41c46595285d80300145940160f99282d6010f551940c00c0394004080800403240421810f00d10804a242c0340b8003025401d022004043c68180308900a040c191944400500215100d50710f5002d008001c01c0b40c43e00741d00303040403178040c00101407400504440c021000c1c074030040d81540310841d0a035a250401511402403080302d01c004a020703102041024451344c0103c0060070850114100100522001c440c8008a85801d003422030503115080e414110115003960000390303940e01c60 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 128915728 1250 128914478 128914493
    0x20d08010f0915180e010b0a0e0a1d0d020706020106060e0f101809020304140105040804170a080c01020310050a06022a10050c01050a1802010503090106080d0c15021312 74
    0x10b40044400104c0c0d00f882218007201c2e40c2c08444198521402001440c0c2a10200f00e01c0e01c0d80c610885d1910f0740396200044c2007080785e402420140d4071004a02c0482034040110a041c540381024090040c3d0003400108a582c0d424010708005007118104540c02c3c520081c08110561410081640917205500c80380d00f8591180184c4042c841110081007100d645520006000c0d6109071015501c402c0c060b10a804d0750801031062a0085030b100c411303585070919000c8030742c4419920140d2b030611402780745144c0021070358010040c008211607900042e0790345030012082c0030300d44850b00802d014083c0c2813000d2116640002d5500c007180c500e8030b01c000040159480580820074201105a005a14080c100c10b09580000240490080305002446980c0d1a0040701c0b08481c0c010010b06411201c44000c0c6d00594000c40003182c000b4000400401c1c0340ba140e07003215180c88030490314840040c0e80c051044007400700c0d2101501c0c03000208403083d4603040309030024940c0b0744164010150f082c1800540c803001c11484 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 128916978 1250 128915728 128915771
    0x50703090f08030403050c06040620190602030a0c0e01050d0f090512070201020717070501111914121e09060c150105120d0f050d0e061303020d08010f09 67
    0x10712640c00340741500c03400c2c150746a422503c02120a031155220b079064900d404400d480981e545070b981c3c0c00552407921000b0f46208107002340c2e07812034015400702e020f10a0070154503903429401000c015a590500551007800c1741c09544010040040c800b80c0b801d5141ea1040c100d0340c0c194030841003c10403c50301400f1f40010f002c2c0c3c80b40100284034107400ca80c9910788010150180354000d07000c0d01c0000b03a4138016605109a0b6141c0740c0070a400800040c4000d600400d0035444840d1040101c82c0712582219103070311040c40c07a03002a10410450102140744450030441d800e02e91400d481024100111482ea901e400b82c0242c0d20443c2190011a805806840711420b40d41d00c14822811500c0034140c054030500580c0b4280a681d001707440c1103013410802a0009902040100305a403541e220917511903080b5401d400c003045403021142c40e606072000030a801c0000c1ea001e01d5036a1034003d00091207180c040c1ca003031004403030041032125a00041242c407503082543c5044600340800860008006120300710003080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 128918228 1250 128916978 128916989
    0x305060103141e0906090a080d0209091014120a140309030303010e0610030605030d030902010909020a11061e070f0309240e0601140103110412030c0614040c050105070309 75
    0x4010803c40440400d05114a910111031a520255124082a5510b5000440e0800c80b194030580210001880a80043c84036070a8290f0040c20440d0b03940010300d034428203417018902c0720480c0b0002d000001c0c609241d8181e484048440b402c0300309590303d03400e13190050400e0180c401e642c10104102186400e00444406043c020260b99032507071600714442c40d01400365100c0f4040d64628508604940c020311070071003030780c2c0c004004001411306c48200f1400381c40d01c108101c0c1080100100001c0000781800a4440945182c5070b5260b03a0700101211858080010905040c0039108070070400b01070302007031000790012407900e03042c201e90700b80705015400340c45418070040005840d500250000340d030050840d030145490746010b01460703864a039400d039211001e008002031059181420040c542c081c1d403110304101c0c00b0300c69003030a081d40c903482d6282d14541b11000384c003c100b503070070503004020303c078419020303c8020b201d00c810076400c10341c881d0b00c0300090702d0007600d0510400040d90000d1500403c400402800c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 128919478 1250 128918228 128918261
    0xb090108062e0806091b01080415020904060807090905010f02120112050a0b01030c06180303050306100210050109020319140a0e1005010b0406020708031606090206070506070302040311010201020313030305060103 93
    0x7170400341c40d5502d0045080c00113505800c000651080d6104034a0315000d107400c403007070241c1d003945d00c1d410134003c1d4010508582c0c46503071034100281035041401601c0092164107030010754410103080c282c0c2907503865040021603500c10024500b00340791410305641520b44244030150f031501140340403840c01070710f00d901520f0030705514000800c00060384190420f4902c00d5072100c0c02d12a42e62440d400c1c130380241c04002c02040307052001440034140030207400c240c1d6070b051044501c921600f401801c11a0000c6c0c008881d203903000010014400c4c01031a440049170682c004c1000a59451485091401e00191091940680f15000128181010009189034043c1000c0401c803e50351079600c845243e1291048a003d07005040d00000c0d912804000d83c0c0310701410500b040300301003030b40d9150802030200b040201d911190500500703002c1802045903d2085000d5200140d4441c02c40c248108015102c90165046a004100f044000d5500c040000780d280d0741400d008c03686485106c0143c0180605c040318155a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 128920728 1250 128919478 128919481
    0x20a0f060903090608100504151a03010e06060408060f040c031208090f070302010903080c1c050a090f0602190602040b07200103050606030c0f0d0e010b090108062e0806 74
    0x324007540050701481c800e4580e103500036918034041d980031508a40d1846481041c3c2410043c504040c0c0240500c0c170484443c04a84a45070b210700c407240d160890700e00103c02004001844504400030046410040880d4058101860654107d41d604401040c00c143e00204202003401c004e0110035a401a543c44202440d40984144000703040380e074205e45c801e001d882031003a14035004101041020903aa01039550368069410350b01c17180050b501c4040441c91601c207604484882c15108a54900300d452150f481e180c1d1000561401402c901003508503194942c0442403c021442d0009500501c2903010501450a4441c070304000c0002d005076804001805800540301d0b04000ba44030140c45140b104d0007107a8848650b2800440442d5001c03918207801c031204201080c54910910b014003c141d490b60841458488c54004c803805641c2c2042c01568103a443e0f081100043c909100d00f0743c007401c204401003000307140c2107000310700141841c088500d5040d0303016940c0c03480f45010b0760607001505448003183d605 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 128921978 1250 128920728 128920733
    0x40506070501020c06010608010f03060515060c0f0c01030c050a0809150901090201090b07030c0305180a03080301090509011a0103020c01151202030d0e01020c01050322080a03062c0403020a0f 84
    0x80e6001095084c0390b030242800204241d402801c405040c1c40c0741034800751031181543e45140003408003415081c0b0b40c1d400f411810740b09503141c42c0108034035450f840c05000e040d0212031040703151503080070001d410315040900800120780d03c041aa02c10300d460b480c0003841916502913407414503c1010030f2040c0010030754104004544150803804ca800c0c801c2c0d0b9030361007090365000780d0095805000d500400150500c0103075400b186c442e0001d851340306a003000d000c146580c44400a8040140e0b580100c800441c048010092491540300b03a0707611000c41c00c004d0014600e40ca82400c11410106440313030501d035001c11401000e14096118040c0c1e200145001c5914603110050843d281b110584100d10030303c41c0fa0076035000b06100314006468258180c00403d02c515040b0019a007039000103058680d200310843e100c2d528071241c208814844d030b0207024840e941305203c900003016100c4039000380c00c0c0c003007940e0f0766040c000000c4140c0b20300202454400c1074403074640e46000c9050503038000c0c0140c0008a84e4000c03405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 128923228 1250 128921978 128921981
    0x206070f0507170327010f0b03030a080105130212010b031b0f1c02160f030816020a15110408010615080f0402040b060904020c0703140c030d14040506070501 69
    0x9801586a000e04014159030803a2244201c140040000b10500c00303444410482a0295403c403000d01c03c0c6080d00340305810031440c150503811800b4882d070345900c0002c600a4403446010042c241c2a80510304c3d107070051340040c00b0454103204050241501100302150040168182d816441841b0034901542d40c0da2070b10000315420654900b590302c1d040004a0300000300c1b081c122625503406605070f608203180054403519a8645075280013196408000705c100d0000c014441078a403d10542c280c054110542c28000d0005600900305c060390403455290201d4a500002e90441a6a011518036583c2a01c0040400a440d180c0c400440c0035078003040c003007420300064200d002a202040c46100440c7d001e1081115889426908010425103c402080150405800c9010500b1024140c1da2512523031601203800c0707070b02007091941c1c9034210800520410480480c0d040b501403410004100b0071b0710400001f038650341c1400e007510a120b0190090700125134010180e50051200916554942d2500d040590 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 128924478 1250 128923228 128923231
    0x19120921170a02250f0e06011e0c03080a050c07020d0807020a08070e0c120408091f03090501050a0b2b05060703021803011109040911090108150109020705061302010507060504030206 80
    0xf294400d04140344c02c0c880031401c004490b682c0c3e404280c10307882d18460400909000e020141085681c1c5004807010020701c848420281ca29943c1409040075428000d040450140104540605005c20b1000c0d031001d03001940d9050790100c0350034002c03140d1880c201e00c20788a12751009401c80940d4030002030f11a8042420000c8450940500245903910010810540300e00c9030b08200008407800450301040b0410082d00010001030005154040880c5404501412240c841800a40c44111410800c4003e00915403c040040814040302c001140042c41c40862000c408881640c140004519000c2255031500c1c42a000001d0b2500c904280d10002d0180d401644840718041d0100080640360405208001104403411003840c1044403620412003d03208040c016180c40c2001002c0c402c041c0d0b20002580d00071b1400c0c00050441200d13030f0f0030300000408142d0101c8007240c03041c4070392404580d0110303161780d010840d255104109845440140c606004001010341694500420070003090380014619 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 128925728 1250 128924478 128924503
    0x60603050f1e070c0302101401051306080601060c170406020313080c0a090510080601180e120306040903091203080f10030302100e010e19120921170a02 67
    0x7140b580c403078400440340004000701202800341d080000d01c0003842981440c0c40c0a102c3d2055030a1170394103251001c02d540301e05c01450980009032004011600c0c01e180300902280b41b2070010700201c1d241841094550034140720362070034800f408119400304024540c078120740c2d07620b05411035143d50311200b00965a1f000103071060702e251405030b00850300100000700d1240c03038000100704106660030181100c0113041e0161401030452002c260102d0420011f02c000741c0a85100054100f104a00c810858162000b0020380c0705250001e00620800d51303800c02c03c8aa000d0410b54012803c0c031582e03e0200c0d101e404541c4924014a101e115110030164084e0400e802020043c29407440c94450346075500d010300441c4070080c05070f07001c1200341211a2840d08138091070320000d000020150a1100c8490808880320303980981070b62580c03c50f00401418481c4100c1c20301082c90941025410202012041031203000480c0181030070307080000803c150b0705a868510301000503115269988050040e5aa08a0b050300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 128926978 1250 128925728 128925751
    0xd05010207020411040506160203031e03090706030209090103120909020a0c02190b070b060d020603010326031501030e0c0411071110050313030c021e2d010e0d020406060305 76
    0x1040090340c4c0e1303242500c2c19075800601c1c940c900801e010b04034020529100c1c00320707010b00060100e150080070500d007480030200c148181964030b103031142030b503401c040711904040e0901d481840022008d40320310202d94150b0b940041b203400020710002c0d040d81d844c080d940c01107190700d0001400740b04581d441450400f9844c030a0351003680d03020902c1d08204400c02240070701c0058000901103c00480e550395042c641229024100c1c000d121034a03000b01d2100d070700982007038407a071111080310b6001103282800750852030283c81c0d03058251300b0b01c2090521440c840905081c1050344a090302d40444400380720880c03c140c2e00500411218100c45068070490b00144020b48c1c0c007405c20800c0d15514100f002d101c20380d0404a07910245503985010b0902644041c5400903020819510440d00050f00d40e4180511904800e5809500b032220480070000d6800d008254424191981c04440d01071030032501e041d0781c0480b42401c03c41500301140d8085405070b000130502951040c14141c000403019016031041e800784000c10038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 128928228 1250 128926978 128926991
    0xc0f0c03022803030c0801080619150305010b09150a090e19120e0105070b010308070c08010504061a0f1003020d1e151d0703020901030f2318120d0b0d050102070204 72
    0x3906c42c03200911446180c1d0b0004c90011340c1e41c0c0b18807803030410f4030300b808400010300c10140d0520a045a40c641c1044403241e548200718001071070600c50031a408140c1c49040c883e0304006002207521806a41b103030f201400d031568048407100e9024055201e0002e40060200c0f00e10507036050880041000c07004203170109e264111341403c42d502c03c4040b100c5c03107a0481c10103111039185039a401465400700b00c00703440308803001001052a100c00e0166500032070003140d010070081c1401003041d4000040e20003052107040c034045e00b12015280c00c40c000c00c10f00c10034100184c079480384c80104c0d0054a812008039219090614441200c1c1906600c83e0300100120b40605e12240d448840308050180340d0841a003507024103800046047d880703038000742074500040c90003040c51a03401112100352049545141c82d0713100726500395100007030b1110005a1000d842c00003040346002003051652589052188049102000244d24500c104a034101d4601648050241122007084c2e082c528000d41004804134840d17800c159 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 128929478 1250 128928228 128928251
    0x11d09040b070f0908060103110f0312030906100501020a14010e1006030b06010507150c0504091e0b060a12090f0503040303080a0e030906030708130503130602100c0f0c0302280303 79
    0x41c0108281e5a170b20f8010311a41e4213585911060341c0c1071015060744020240020340300c40e1010b0000c01e815000d00707900310340c40b810a103842a0819000601d0203100da80b00d904c040103107070fa00203484006160800c1c0704040d5503440c071200502410324100a088984561841d10f40c1d000c0c0241c1c000c000f1039024006501c21500c0300f000454081c03194102c081c0c15201c407003240034912005540b214105007080e0401c10700e015900c45024095641f04d0100d12644180c01104000300c0c1154000c5038944041280e0f003038035219500700090881c2d5124400400b0065403a58031500f040821009450b42c10780120480713845030750300d144c003c21220013195070303c10241c180300100d448084000203460380b442d4010250350559540701d00031206101c0041101044000402589012407030034001800b00450200c00803000c981440b2002e8540070110307445e081e5461400da1480d880c180e120709007919810307440c5403607003800456040491400006088100101e0340901c02440700904c100020071940e440794500344400b00284 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 128930728 1250 128929478 128929487
    0x1e0912010608030a0e09060a06180e040303020702090a0b060f0c030405040f021312080a0806030a0c08030310050d080702040203130b0702060709060503090d080a060b0f070201030605030d020309011d09040b070f 92
    0x1c3c0c90b11fa4202c03480d500700b400b0a501659090500b14540104201c48581d0703000d40d5403070464161810707404260700103000340540c1400c1e80310302ea2100600700144508050360011840a210381c100151102c4000704075040541010b00440d4001c020081042c00845140034400c0000c1d80500403014031213240306400209085d144025a0b01c4036002010319040802c1020305a1744014020100c65140c003a10601380009000c100c40d00015080c0700004646034500043d10009146480d001188900c2e4540d04810008504c2c0007218503460341a0f0f40503131131b074440c00a420000760200e040246910318000420502c0e560016640d13100f80695501d018000d030742c0f41070a4816102c243c036560801d420a0200c850458010f1131003a030008446a00000d06a035580e01191880c1c00024900204400029106080d581c4c1401000e0242000714040e008440b0f054501039980d01c1000c000d98184103000c00b485140d141d407900c0300051024081c2c4602d140e49000d141011a60404544500c00701c3d03550303603103400d805108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 128931978 1250 128930728 128930731
    0x10b0a090f0b090106020c100e130c020f0304054917030601050d0b010207080a03020f060a0212040b0c0912010504030f030509071e03081306141e0912010608030a0e09 73
    0x180c010301032035542c601c01c8c88401c02d0005040424044070b028802c80c6620740801c0c0d030701014141d040005182245400003030600855407901407603588203001c140301f5a5104000107030b0b4a449100f41883c00b0b0f200502d48110301190005110707104131804640104d01c3c14200044000f0340c4601f039400c201151449180310940410344031140051800c0c08440034814540e0301c00c031520401401202c060030390303603001d203490800d184a040b801030f0841d1040b04503440d0108003554000a464609600f042546041901000c0000780003a00c2c0c1250080800d021080b60b1045600c1c0480c080c0c00901c1000010003210701801d400d40c0e0031000140c03c03140ea041307050b104e031150754040e401e06e101a0072002d2811603801d90105103c0c080c00c100b0040d4040c00400500701c54002c0010080c01695215840d01c1c0c18030242004021015000303210340200301000d042c0440b0f80c6500c0d400c212200c502038607209480c02081d600d985540d01840310390310b032a5000c990180b00001504042c032250f40c8038852100b156081c0100f2040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 128933228 1250 128931978 128931989
    0xa050d05060409080904050a1113060e0901082104260c150301290c0c0a0e0c0d0203040302011d030409060f05030d0c02180709090c020615060a02010b0a090f0b0901 72
    0x8083c00240ca481c901b60700155001040344201080344c8403602c0b510302456110484000ca0205a40e0007006610b030014445082c402048581001661411984544030030743d1811401c0c40c1d14800c00715800481c901010b130b9000d0061070108404d541141920380404c0c010103400e0f0b5400f0303c03a440c4a0b018501d070203110181c4510705124140d083d85d00e088400700300c844101100074130661034030000300850fa810101174400060446e000700f116005020510801107034a80100d01c941141e81c1c204509030f02080c0450306208042d440c0181d9998880c10201e00424031800d0a4801e01d080c5c0103140503104000011b0811740b9035001d402c0007001e0342c4002803e0404080c1c4542901034214020301d01d500d5000724082c03d000380c000f80a003070101c07159901100c00c5007012a40080403030740e4400188020303a17146c400c40d500440940018035480c2010100795060030a50142144288000506043e5191017900071042480f000380400013a20b03103d480c0c02020308400526401200d14003a00011a8030340204418100c44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 128934478 1250 128933228 128933243
    0x3070e0c04030c12021302030c0706020c0109020109080f06070f17090c040609020a1b0807050f0d02010507050315310f0b0d020607080f070b04032715050d0e030a050d05060409 77
    0x480810b01b10080d40000349186000e4400b0700446010616600003000615010000020b04118070302c00588030f0200c50700301e540c55610140c54102001c100003034140c0c0141050a0512030304488210440305410030700c50f00c0803404241e000b4402c0c01e01000036400561401100d080c000161104200c1c0201e010301c1803040002640c600b4802040129400c0ca0031a0780e0055454900e001740c203440700fa06d441060700825603250310001c1b01c445190760a2044541102107860310a140d4101140c0031381d007810802402d603101e401100d01c1801c0e100080e40e0b01da442c01d041c034070301c064600d04032402100081c602c0c0110f20041c2400c2c0300401410313281c06441c05810950041100c0e0408c00c0d103031980505500300d2041d401c4148401c1180d02c1c01b0030079074003000d40b02d10b20941c0c6242c80485a0300b0403409005100c414000014689041401610408040555003002e5850201d4460300b00e000d40c24068060344021456078000010848074450f40311008000380d03848100c06002a481740c0c0184800c948200e0005440e02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 128935728 1250 128934478 128934499
    0x17030708090a0306090f11091b1b06010f050906060c0d08070507020307030624030206030106050901020a1a01051504140114070204050c19030504080d05040203070e0c04030c1202 78
    0x10160009007110010282104034007503143e54808003104c14000096070740000e002007603000c01c41c86404a2900b00c0e0242c0b021f881e81c2c140802d000310070345840c002010007140f01190100c0385054100608900b00d015004484003543d44020040d0080d1082c05050700810758500000c00c03508003c000c580d98001c00000a20107480b00380012222280f016040c4c008206081004401580d010041c00b00654090f15002904d80d0503610641d00d5100d1100031780c091195010703020009039540000b03a82c115034142c100759650b4030f07103000101e00300700041c90020910740c0401d084062619410840506071881603400b00b0580c0317201000320a00340528414103445088402c10b08843c2e520542a10001c0c1c00c100f0342290400c0070380d500050680b00120780b440c44103907000c62851002801c40c4070006e2541201d003020001070416458940f85ca110b030b0751030303011a50340f80c01c081411500c040001d80000d0251105242c0349040084402c070b0141e2141c4801d4448020802d00400c0c407440c0d50300c072862060390040030754448 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 128936978 1250 128935728 128935733
    0x30304021c0302120301080d030501061106072003070b041218031b09050702060919050c040b0a1a03040c0f080a02091504020408070e0705120f0a02090607030309020406170307 77
    0x1520748503402c4007140100076410042900f4003001d540030701100b001404c1c0748510020014203d403016804402009022540b2100c0520b02044868010241c1d08e040358600b980104502d010000306890102d0074400024854107001024101c180118402c210010f07243c01c140c0c5040740c21013900d40504540414210702040003910280041c090180c107082c210340300690324106501100d0341101c0100258020307038104038030500d050100302400c0700600c44c9400d103280c294807090741c1e07001c00f18421030103a43d82d10110107481d66030305010b00051241e00308a41408803680484015030b00160340c21a00003421980118810310444458803c1c0c4900c480104007480c0c06400f044070501c0d024000384050b16100001940c0303900c6900003840548503180c028040c092500a0880f90503000400b0302c03041100a00000020003000c015598101c545084444882e403280a1810003e100d1411940d512031000078490b03041582581085058074000c80c0c00b04000341e6104000c0080d4007040444582c01d42080005a00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 128938228 1250 128936978 128937019
    0x130207021804060b06040608060a1502070512031b031201081203070305041a0106090e01150206061201022a0d0f05030c070309030b01030506090607020d050403060c1b0c05010e010203030402 83
    0x1441070242c040465040134610104001e0f0380b0a8111800103280601007000c182482042607000f810807189125030755003814002500da854901400d84101103040c5d10304c00790002007081c1e541d41c2e407a5185080c59247e9040740b955580e40f103218103007803900c2000c0000901d183d01140c000301c0d80306141d00c500c4c5035980e458400c03001400d004004a8210707200400d14941117150b21403490107002c068445414060420810b504103200507401180a000d03003d04811140d540810f6207a0044012398014888001c03029a09002e80103806000c0800320703800c1034810124648916892403a41807c065030640040c0c402c048541d0785c0c21051403404200308001040320704954400400f0407030300034681041100d0f00e03a0313200d03d00040c0a074020364440d402078007400101d100501c403c581140c2103000900c5400703051500338206000e18840034281603503801d00200c003940190900c0081e400020030041c1452140e01d0a001c000780e46018a6000400205440b07003154000402c41c0e02071a0000c094010f403c44a124001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 128939478 1250 128938228 128938231
    0x1c02060106141210140904020a030f150513020a06020f070b0f040807030615060c1113140403030f05010503070b1207030b0d05010c021501031a220602091302070218 72
    0x1207240d04000b807150081140707680074050034405801c103000c03034076103417001c02204102ca04251003040404140401a40c91800d40d1013103a41c004002080c0c1c01d02400d006080760880400c01e42414200320400c01c110f0b8400e082105802e10807035a800388203483c2d80003240d480c208581050352580c007c00b418404900b850303000d8441e8842500b141482e01d07484100031402c2107043d510454155446400140d000c0081d00612030180643c0c0ca0710507441c56807602c0f052115100041c2c5a8001c80d086440303900c0300c4441d50004003003480c0384184000c05d400e140c030703009000b0880c1c00703210741c40103140034004a080d180110b6420112450b11004a04105a05610805d92400544203006041c1c3c0c41b001c250300c589441d00c01154103401080006240f4003400300181c00d190800303c4012403544030300c00510018a104c05410b80c40440d10900702070030b40e1416800c2e05810580118000440c0d150321030b5804000054000f007c103403205980005450b08480881c400340e00540000039400f1100c600c1c182c007807009550041d07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 128940728 1250 128939478 128939507
    0x20d0f05122a070c0513050601120510050423010905090a02040b13111201060f050d0b0111071502010605091608131a0601030507020606031b0a030501020a050405031c02060106 77
    0x41c2c004500300352030101258042c01c01166030014a040c100207620341007441c1d20102c02d542c401445540f6007070000070700d0406005008810507607100081120b107010343c8c400b00080c0002400400986488810b00666109046010b5003041c246d4000450b01440d00d006090103015510300a1a0180d51642004081d1401c01480c54126110800355a1492103601840b550500075a101541d1441507079480b600d0003805170402c070706001d518542c0b9000240d0181c201e40e620f0110307100001d82a0300d4400121030154000c18068094403480502041c506035400c000f490421058008109482c0d40d042031003070307600040302d0108072080340e080d031101018018090300d07500101a4014070161802d542d900d480c03a8214604c11050131002d1003c01c200380d6014860548c0120207400100018038007500000d40da50f44041c1d007850440344626812010391030340e00c0b044024660002c025511100c041340c00070010f401c244501c500c2442101289038440c400b803010182c4030a6160701510241e030910b07005680c0c198010040707 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 128941978 1250 128940728 128940781
    0x2090702070e1b21090f03130311061b01020901030e01090b0f0910020c1c0318080c010204030b0901140f010807090506010504080d0306080d110604110f03030a020d0f0512 75
    0x1c1c52040d04404c80303800a1041c4481c100000c0c1444ca0b08141b41080580500800344d00030418400c11107041e000280c101c903806007100b41440e00b0400491100d005400d0501c400302c0d8490843c66801d081034000d802880420b81c0d0802c00c51020300e03404c5080e03603d80780300034050b45140d0001c140072040c2c283c4000d5200c002107040f1120b1440c3c80e00f400040b41c0c0900041d400340c1d00203010b0b8481164040d0090181e019541c9000d00038410284007002d1034022000d0f000340304aa0001c0d40c1c030340124003034050b10019a000034442c11503160000c007082c0603090400303500c404000d191000842103a02c41c001b66040c0e500e0100181001c5051040c03e00091901404185c1441014480003a43e01070410565030249107555010510303d140200d2a80381050003030140041c0802110301d01c12010700050318641c800d400921050510083e4408503a500002c40102c07500350000140384441c55400044030902c50103950b64450ba1549030220440d014011588040341c014001b101242229280321040190010501c80c4d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 128943228 1250 128941978 128941987
    0xf01031103030f04090c27080114010503060a0902190f090507030c1209020a0302091e07050f09010c02040f0e030705071e030b0621070501140708091c0215030402090702070e1b 77
    0x25103040c0801c082100c1f1012402c10101445840028043e118881d5128642c95615504280020351180002000030720450340c2c2d90350000540d66201074015500c985c020500128035110ba40c2425914828005ca031045400c04d00410b00d001d21900c20018203c98541d60280c511411221b02c1000d40a0070301c0507a0310004010700440582e0350b09807118080e800c0000624403401600c2c18410200000800f5002449003d0140c2d0341048509812156211000d1074001040f02c1c052002900a260407000040c0760b51401801c0d80740c040c400001440d2860281c000c888049a94260740f100341503d0b402c0c60030903944d2542c2d0410008108485258000d400104407030505042c0031240450704581424070416580124001c120380e50300401a48180305069a5075840d01040d40c5541c9941d2098503080c60003130100c5420140c5011195100e000c2442d801070114101001001029a281e00300f5a0242d100d11800b4000c5001c46000007025002c4441204802c0d00c941d40b110246904041c0c03613248202034603400c10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 128944478 1250 128943228 128943257
    0x27010203070f1b03020613140304171006030816052104060f0c0b04080a0504030807060204030b0a05240d0204020d0c020f0f0303060d080c03030f01031103030f04090c 73
    0x1440c032408140e618040b10403400080240400082c281c095180c0c007021091001082d40810040e9105030100c001000741601e81c41c1c41e601515900b00020342c28040450003281010031542c401c6c0074a4042c000321400c809a00c40124102c50b41c0340b10040110400b00302c4981c00321401750146550300d001c1c0d0306030743c002d1203200e40c0c0600802e80080241c240c01c10000c0d0600c031982c3c0002c82c18015103810b01e8550704800340c980e1a41d040003000f9001a20901c004030300c03580c810744107000b2900a564400001038403031991f1329081d000380d0083c0c04100d910300b0500740000d05007852441030703d10480a1a504514141c078011542401440000d0040d410005800c00640942c8813800200502420050005010b00781d490000b410300c0700700c1c041002c035900490101240c11500009494001d40c044600d0020a40646840c40e603501c42d01c480d40e101c5000110420400d5040400d9540c1200d003d50144000d01041404064a9101d0103040c0a4450001d22041c4201c4141d0741c400c1030b040b2080c5c202858403984d5036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 128945728 1250 128944478 128944481
    0x1d2701020a030609060602010c020c040902220204080d08070e1e040603050c030616050703080c040e01090b01111207080d18200a0609060f0201110c01021b152701 71
    0x5059181c00300781c503480d00304010b46807031045400600c11440200030440c1207150085d00d900000f0520740c4650313187e0301c04900355070f01c000070318803103541d4085d951207000030b40074100020f500030344034070107440c0254210399418900900416129000c00d544254941c00902c041240e00744a002500e03030303046041e802c1c011054030f69100c0c25014501520041c03210091403020180ba080c00144594988201a069000c1454010050b0341080c0c0d41030504205943e6441d40c5001d00c0d0285602080038041c04000003d0222166402189110b40aa0390807028410040250796100740c1d4900b803d030b00ca1002c004071300105035441d020700002c04001c0000300d0050044550b0b502407518000c0305441128200c072a0505910441d0205e041280e8152241c00f0128904840038003040a10311981c003c2c06007002120002034400e5000001461070508840d03102c0101450300c0b4001d4120740c240041c40f00301140358a11483c40040c000c014000001081c0c003842e40c0740140b160307a40005208210300c41d40b443c2d80350905004203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 128946978 1250 128945728 128945737
    0x2209020c010608060123121516020f0606090a0c020109020a0314100e03031915060e010e0301020f2a030c0a0c0b07030206040b270a06061d270102 64
    0x1030800451003904192001e824500c0681c8010f06030240c6100c0e0018584010b040e01c8a404400c55030400300c004640d0b9001e082240c1ca00181006602c1c80c41001503440b0034031240f50089019070b084420804400790314540d10309054400c1c5c0c1c2d000b1403040020b140e0000f950042502d500c547d1001080c10215a8081074800740310341c100700c2d80107503084030131918000200100e106440d007801040c0130400e400240280c0301d1101031b00031403a64160524000e01c500498102c1e4121021070711780d002d0166900ea4000748803015048013a8000303044412030b0300540c0740500070380707040712030524200b4900303009540300401c00810000d214511954801410b04c0d24032040c0060480c03111110b0182050b10720b5490a030541c4c05090f004048004000e020000c007180c4d0000d00c45038802d50040505074207455030b8000307081c10001c40000c14150307002c459414001c00b40109810340c503184a02000d01c4465203584052243c0e0781601c0000b000041d1440028112420440c4040e1402d040351115a000e0074841c91a142aa8003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 128948228 1250 128946978 128946997
    0x60803070b070809160b07063801020a020a120c03051203090c01030c0f030c0e030a03021f0204060c030e011808031b0c0310020f0f0301060c06050a0c05220902 70
    0x3210300c1040211070b0401c1034198404e61040c0503100070800080709641000d0381d800344406000c80456044208a6254407500401000c95401094030340c0d242d01814024049a604000443c2c00c0c0840104950000801101c0c0b194010f14155920303040824031500307058481000d4a200c10318003400008200144040701300c2e251070b070030069600d1030206030b214940005440c0701030405107410411403400b0780c000d8000c000e1400514001c00c0d660300c8084216207000d21000f00e6989801000e001008254000070190b0400381c801c4401007000e22995422401ca01031840340c0b4001c560b0f0f50781d904002a02c206060508103005040c4840c029240700c514411851064011045540c800071f41c002c8000b0815103424807408220000b040078400020200c2d03203482950080020460300801d4070295104c0100036210f45464031840d80c0d45a41e5503403801030940340c10907400e49280f407824001c50b8920f0340380e0040c1042401c0b1515006d00d40300d001481c00c50b03081030700c400392095419401000305540115000034064100c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 128949478 1250 128948228 128948243
    0xc0801060e09070f0f14130305060105090405070b03090f06010303080717010807090e070504050c071e020303090f1f2601050d02040914030a08041502070506060f0406080307 76
    0x40c14160003520300c0d4001000320b403003010351004105400f81d000e0040402030380c0a1078900b862159009041c0c0342c00b24001500c12940b0343c045030402490000e5112481281c1c00750703080b03580a0740c0e80c2044c440c05440544010b48582c2018005010100c44c81c4000d6402908901c21102e585510039100307414003500ba0021800a07995905112809501405480e20310812003211080c1d5454000190350b02d0015110f404070054540641012446c01032142d40001d060140c028000347c60500c000c1c1001d540001c44c100d5070880c00001c00c402665030b00b00789121fa540e014004500c0c001404042000750010a880c1e030703500c0420072011041c08411030a81c4a140312554403240d81c0c0c1d100803400c0d540121842800030b26429821401000b150b52480300c07000999806843c0000c0380b0341d003810030040036403516401400074030000031304900041e48882018803179406501e0300b520304114084564203a101d51030001c0e040f85e12207004524603140000f0000400c0a00a10000d21a030351a18582d055401203041030320341c1d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 128950728 1250 128949478 128949481
    0x81308150903190e031005161b0f031409040c030b0102120a21110301060c02010909180636060b03070302060403080a0302040902031302031c1713060c08 67
    0xc03214003001604680c00001440c200700802e2051070f040b500540000b4100400102100029241030041c0c01c405008100240020328125040c0100354403a81715401c001100d511440d0742e6200003040011001c4e074000b03000c1045045585007265803411205102010241c10460490241d40300c0c490901c0208040d00e021450071142800a418580714005000c9242c4080062011266211000d400240704011034111074235200c01074503004050a141480c00c4140020000c5805500034122841c4c8038801d03610825056204c0402e00709458001c03c08240030301011840301e0000d045ca41026140041c41601c15002c80030064002d00b0340b0113405102940050841c0c1c080c0103102d01409070108042e4268010b04c13141c0d18580c08190340c0d21551101a0001c88040349441c400b038030130b030100c50040030802000e5450307090020001c00ba0a05400003240309106461071a080191100069500741246032213003044008207080401031040700901003864a40014541350001d5100c1c802c10350310b81003d40e50350700c55 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 128951978 1250 128950728 128950753
    0x501090503100e100614190810090807060c090e010603060608010b21150103110733060f3602070303060801060303180614030703180f0b150609030316081308 69
    0x1f40d0380d4a074501c96a84600d201e042c0a0381c180011001340643c82400005981e800d141404805030240010040c0b0391030615401d40b140e164050400c1c07050751040c04c044aa80d0740c3c1c41100381c0c115402072280302d000ca0200750041000c3d02c0d00c1350141200740e034849840300d80345c00307200d1485042c105c00b15518041c4904400b20300d001c950341132040b410032041c405051403500805443d52910b603149150b108101c0e200da0240c01c0c020b40c0346000003810405c13241e48107210150300c80f6840381c005ca140340201643c0c000340704850b585900e40d411400d14400c42e052025001160155100806135000300c03c141d040c1a20f4050008008200344a07160040d030090f650301c0441403d03072035841c928040740c0d4003d00c2004102c00c1d10b404c4089560045a802920718280020381e141c3c0301c0461424410001c2018000c40f1a0308003480c2030060508415119441249550540600c5d000c208006405002e0300c60ba095031052120001c01014600040c3d519401a50321904110400d000c01541500d10f8000c045281c000d1442c0046 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 128953228 1250 128951978 128951989
    0x30d05030907121703060105161a060d020f09060a030512190203040311040b0d06051302040f11040314010b090a0b01080105150328020f130501090503100e100614 71
    0x142003510812801c0c1c95058481444501304a0610f4281e910000045141170303009004945015010181412054900c0c0c184091090074890b070301070207415650002045841c0004850f80340c154000c7c0102c0861008000340a10650001c002c140c1083c0d03030440c007002044003001940842c50600146950302d4040d00940807040c07018040700c0703085d5803040c8014400900001042e460781c040c1030b42c0008400e0340b0a070010341614801d0402405c4a4509014002d0000c0c112100100b064000c4e9424440080c2c0100d4180403a001340b42103410b040010b01051001900c507042c41c030101c407252400401c0c114001000120425015120321800c25514583c0e440d407941c004040f40e00400007101d092030500c4031031100904501c0010120800c408000d01081c00340a210b2083c4000001905030454031042c011344204a40c0c0c1c400c6405584450b84001d00055a42c442c100b4281a1000600a81040d040d049454400b4103000e510f414158040d05202001090f1140b08540090403444000c143c007500305d0040c4403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 128954478 1250 128953228 128953243
    0x180c1406030702030d021303020402030109021806090307050112200703030f02161203060f170717120307020114130303200a0509030c09010e010303080702011b0e010e030d050309 78
    0x90003000103108201c0010703008010b5030180718032418056a1454580c80c014a0101640c2009521070300c08030000c5034540c0f4503806030ac01480c44070440d03540c00c030301401048540c5c02144029941a80101c3c0207104a520440a00075a01110800800c105003030749054205076401420003012440c01040c040c081c141e05006208500c145a401185400100036a241c1880c1421001074005140c00b901520301510070340c0700d507000784086140000741d1501d0b4074103011441c50200003514a8800c409001c19400481c0600c441c104596400818101c80c490fa0302c10141e070401840001995612905803002c1c070384103030b1503d12400810548000c0f000d80c3e49800740c11100285140c88400d408401c050300da9401c0c40085074078a1029082640d12205140000ba00e1311a640a102e50040c40340e4000003400e84002e060709040c1c4c4d100340c0780da41e096544c441040307088fd2055080d044075655401c000410440c020a4a51103290041c94007803801011000420b260107200084200010b2001007000945001402005c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 128955728 1250 128954478 128954519
    0xd0207050d0e030a0f1b0f080106170d0e03100c050901120504350705010c03050106081003020409020111031902010b0d020a09020d020408070303020f010b0a030206190201180c 77
    0x101c84201e0342c00701182d503552102c00010031a078441140700c02803003041d107564031014088074441203106d034035900e28604126051007280442d42c2000404240d0544800c0401843c0000c0070040040d0843c0d070134201c9181c1041c01c000d9030980655561041e46204038010081007508603140c41d070355462040001400c0f00281203c035500d080c0b810050000082c1110301c001109645402044442c002d0305c004041038030030081e490300303041c40c1c001030040801606422100580410303841c05c014980c0d07104820b98140344200c2d80004170400b4050b040c001803a007648011507003070040c034101012140d9604694a11707031014000c4c04803030b603020103241001c9509008807100294166001052000c466002c40c541419901403110801d03004507218500302160360543d0000c00c00c070340032102119a41c0c24080d4452000803448170007542801c40c24035a42c20030b580010210303940680460710704a4034800451540c11250220000c65407a64003c2809940484801401a02502d5501c2a0504e852220102401e608901 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 128956834 1106 128955728 128955737
    0x7020f0a0c08010c0206010509040f06021603030b0a090b060a030b1f08040b0f0103030512090a14030414040b182a0a080a0b0a05040b04020f0d0207050d 67
    0x24000c0b1900034008001c03daa0580c402c0740c883d4024022650007660f54804035000404407807900045600400c0b0041c00c007034030301d0596101d0b04c0f08210241c00007529040c0002c11454009241c600819012908000a0b16814042007290140807805410302d0350b40c00d09900d09860b10514118414040c40b07031303100746041d1060040c2c100711040e2420b4520017520f0f40015100680110b159042e81c2d00740c1c55050404c0855a01c2007000c046c0241601128000c0c0740400000841c1941e454580d02070f500c0280d51900c2c105409121040000d001440c0b0550401e428025191240c104d030200032104003821400c95030758040c074009408a4001d450034841d49414034884a030080401606080ca00f5039121101920340310350030410741e141000c0d2161b100003018800c00440c5410b50201c1d4140501400250516903441c0b0b00c048580c01c800380c4490349a070000380ca4010808140a1501e842d8100e040 = true := by decide +kernel

theorem cover : BRFrame.Cov 128776978 128956834 := by
  have h0 := BRFrame.cov_init 128776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 128776978 ≤ n) (h2 : n < 128956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
