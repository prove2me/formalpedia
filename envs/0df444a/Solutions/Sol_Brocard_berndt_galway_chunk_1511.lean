-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1511
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:19:40.938582+00:00
-- url     : https://prove2.me/submissions/7d83d695-58b7-4f8e-8d07-bc1f90b85e78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 271582733 ≤ n < 271762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 271583983 1250 271582733 271582771
    0x17010204050111010207170a020f0102160c0f03030504030605220308040204180b01050d03022401031b140918250801020301080a060221090a051213030f050307050303 73
    0x1010380f84104042e014507441080244081040002014030403524060701d01d55034020110304a181040d0914401780e0342d44041550b440b6002c03c02c400f4454a8056842a0105611411007000f03101292000034003280042004100044650f049194845100c101040c0c00d805000207200c6542090203044001a504001f04000c61605120301654110341f03803070021174003442e030b51007a9101d481809038602c10b1950850010825100700007001200c102c0400c0700740e420f454a8600d2039080c0c403c0c001160500580c881000e800c1201015240803603a03513129066032201c010092004c0407401600c2d0344814000c00301c204330902e03401c1010705001030f03100b0210541d00c40080c1c0003d10809064005404590042004111101000843c9000c3e99013051005a80e00903801030081000c50058800c0171030000041023105c00c4030045031901c40180140d00752281d01c20800d600c07002c0c82c410400240801c000700c14040c40400c1c1c103c1603540c0800d00c200c08581c40c01c112602c900e89141c100311200840c2c8000601d0035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 271585233 1250 271583983 271583987
    0x1020a14160b0a050a14160c0f080a03090509180f07080606120303040b150907050307120b011e030905160620100209040912120605010c0b0619170102040501 69
    0xd41d00800340d0000725820000108002086441400c4003001000444c0700320400c450114021606c2403000024201015001031038000001e1020740700340440c3c07a0001400084103070340442c0500d60668940e0f07c07801d0303880c1403108000b000d16000e40626401004507107100c1c15007a04000000d81650200c000f00b2009241c090f000b440d00784018050341c0903c02402061142e60300010580350459444000b00b1080da03254644980807100e01c0e80c886922400034014000c031142c22400450142e000e40c2e548044080400440c41c0548009031212400500b031900098201b4014015013300c2000c58030300420315040c243c03500b51800d10b01e0300a000c032051648408028090b000342d94644181c030400e40d000081300001c8151602c0b002090811a402900003828940e56a666072050b036019600503040b03032014055131001004d030309000e19a1000203103407a102152641c01104ae201c0c40d1a8400f0350022b03035030b07070380070500424085604510444583c50341002c03486d00c011466502080c6d03c21000140c5840c60a000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 271586483 1250 271585233 271585273
    0x1e11030f0303100605070c14061c0c08060405040510051306020d0b030c03070b031603180605010e0114030601031709030d05120c04150c0503090414060306072a0201020a14 75
    0x140117021041021034001071240001208480e403c00b42c1034869100c20b00842d401c1d100b42100040100300e01e4074003a050308100d0f801040300b14100c2d03540c0381c07840c0e03111f00c1404100c1d44180d4018107142d000c5100904404042c0e00310340c2d40301d070001d0003011408046a03038903000d1307803c41035a40000342d8640a0b89040c5040030803441501c95000ca00902b02036281030b41c025150f12028014000610340007508000071802074114500441c0d0401c101824011242010402000b00b8020215207000100002507407240d8210b4010070414000c0c050521039181da03459005c91554042010143c120a0203088c41d00d44e400c0c0714010220132107468640d52503900140e0f0585807000140000d254101c1480240403c0c4504558011000e115040200c0348201a0074114594004c4010445e4001d04010f0700b101c1031b0030030502d03842c0940000c0d01140d810f0740b54624181e6010b40313080155151803902c80540801c0340000042c02d2442ca0060040e1140b800302d030346a10310030451703007e13007000b440e0301040c4940c00c15065030507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 271587733 1250 271586483 271586489
    0x9050d0c0534080303220c0915030c03030f03050c04080c1306050603010303050307140406270801050108010b032b05071104021206010e040507120c0203040f080c011106041e11030f030310 82
    0x4105041c00c0c0e100d40d1441c100c06898001c610040e9070f01c082101d403270302c0d0000309d100146810811810b81a80d803864001c04054006200c3d0000904150124036010440301c1500d0640f282c1101601d16060701c1300c01c2c01942d0302c12506481c1019212a80003910381c881c0130041d806180640d44481d0303070b0300d8803d1003d071446601c0c14011800d04c070108400c00a0075401402d00b0860704921501d052a54000040104208000d4114034240d518180000503450700541c0700e10442d01055069644181c50441c800d6a00101400d1321000d140c1c0001c03075868030520a0780105011842419100302c580e828102040803a0891038016003908480c03002d0205070343c1c0050402294140403541881a450001070061500458002030301c110b07a141c0048100d680d0081c0190f801810798000307040b041c150340e9002140c0d41c024802800d40031560341041c500c603820010410521950300095500d145803d03040128182842c0c14070140c44c0220250300240b400c0e03505000510922501000560700c23420000100704071410254 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 271588983 1250 271587733 271587781
    0xa1214090d0e030601030209041416080f06100e130f06020913090f030503070c140321010b03060609060715090501050105010221030a1803020109050d0c0534080303 72
    0x1d403411902d0707900095964156a815104e2a4040e2510314054070002010901428140035a21501c0016500402c10f8412030f00501c0c101c49803640d901c0b0949032180c40070385003078100c4c0b42940400c0c0402c910303031143c06800040d0012440b24208040d11001c920002c0030500b143c240390001001c0c1028079180d585138080c501000c400301301d1000310780d40d07110008032180c1c001070034030030f002c40080c0d209030180800c954266000b032105000039104614031a100e5018186c104000075004030121981046108400e05032403043c0317000c80ca0b6480e04000c0214640101c030055500c098100f01580018820b00509284403c0c41c90300407540403401d24055095960580100341103500581c0250110700f90001c1406402515089203030340d035103500c64040003a08480700101d0740195291025401c01d5415405a01028068400d031015600380d180300300ca5100e28448040c20f2035100400c030100c3c0b00328121222402443e06401c240005010003810103030384101d0340c0141c115800200420051007101c5469924044c0c0070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 271590233 1250 271588983 271588997
    0xa050a05010501030c3006080717010b030a03140f0c01020a120506060403060504021206090f010e07050607060507031401090c0201050a0902060f131d0601031a060f0a1214090d 77
    0x10a45c014500200d146840481c0101400d80c007190510380d82054160094401050200c1c0d601d420703070700d40d4400d12032150020a00880b140b1702e07003010741803203540b181041c02405454010010303101200c20800c030b02400800602c0400980000c80d8422000304148048080056101c400100e0302400701004641c0304100c1c03d042c1010080240da9990840301541d5000c4c500286d161030b0b90011030003000c0e01d50080c2015209500a00264200000c0c2220a084210000b80100da00c004081920780c4210310409410000901c960030014460342c2000341c1c08403861a0001c1c0613070404254611901080c1d00c0a01e21654440c00520300340d6084c0240c0c1e9103c00c0d43e80c3c090011003000d0340851550f01c074000014680d80300c08500c0810045001c030618005140761020580d080c0821203191010080503208240400c1ca00042c40000d60007446091707108101c02000c0c64188613035000c1e4a00141d001c50307820010491100c0c48004d0031500d03442181e1a24014050800c8a4030b07000449034030740b1020340300c400144a05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 271591483 1250 271590233 271590251
    0x30105070807051e0403060917120703020f0d091b0b0306060a0e120a030314010e0613050604060f0323032d09061b0c06090306060d031103030a050a0501050103 70
    0x2040c0e00e03800402a03d0718035500d80003060324481110680030b003080d4200d00020b0000501001c1e400044000303004180d43c446c08900b4240c142c03054480c0402c20081c6a10050010303084038041e9001e0a000c06c90700400758035100b50940c0716012654074050403240c111b0100c0030205030088a0300c41d10050b06001048a1071800c100b80054114008c85030703803104201c2400c800c40f002d910b550400d13502084c4010304844805009190240161031420140c0316103072103170400060f22806160916001700702c0078260341048000080c9004c05480001c01903504651140386c00500c080101403450015402202c44e50403c00c4254081e1524480c408100e0f03507998018403122802c1000b18514282170507105000751a10030302d544c83c000c2030b030150b9864a0392207040850302510345601100030310a417045800a95118011031020044a030182e0003240d501517001d030000400c40d0a2180c40b0000704c0d4020f08141100d040e812161528580c01190303200300700e5031942c041c45804c5e0198001e960143c142401d007400b0f10b040d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 271592733 1250 271591483 271591487
    0x305060a06051c0212030c010c030c081501120e030703020f010515060a050c070f060507030822060b030a0b090a21080f060409080408010b03250b0a050d05070c0201080603010507 78
    0x1210840f40d65807011100a0a4110350700c0302d404c803038212213800a50b1f4171010107070000d13030007481480300003000300b800d1a195401d80d0b84240740c1184102800a0035014031512013004548592500c0c0000c949159500c4101601400410240a403284258021701d040031500309540c1c00d444014140d8942c3d4280b030504400c26554090540c1d00307040c0a0314000d130310340c1908001d152030031015502c40201c80854240206031603600100408901c0d00945072581152640010100041ca90440b1201c54042d0a0343d44400601a0303000401255030040c01c0f00d00301401616484607000b0b094070758082c9640300010038010030103402e010010080c40e800c0391200b00d40c40003030041c02c3d40f88000d1090049a8002d40001d0140c0d03503641c0190452500030905648550311201d54a00818080300420701c20300c25110f181d00384603040780444c1042040c0042100e0041e182659402142d0086108101071100c184214000b65109200b8288203415983d104a41c004a80c000034110f5800980494003e0b418841040075a039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 271593983 1250 271592733 271592749
    0x9080a02030c0d050705090c0a0305090609060610030b04060b1e031302090a0e0a050609070b0f090906180a0c031a090708091207110102060c0a0f0e0f09040c0305060a0605 75
    0x20660f14100b94842c00d1030141e003806880d40010758801c1c0d4110602c200c0ca8904406411861544d4070304122a444901c0610340d00e060803140e4112030b80c4803000003032481c01d02c0c507810710408150707082c0441c8a015000015058400f0303500035000f882408610711903d0305e5444114105042c040441918600301102643c002ea4a0002c010f4065080e007000704400550b25403103940040f01c18030585500903400c6c0307030464941005403514062032103016400b18501000c942107072840d5100c000403900e86188001405140744004103490f40c000d61208040d462040d01c1c02203d84511b02d5003800040001c0c2c4440090b040300d1460301c0041e1120360b1060340039166120b41d68615009901808c2a00c0c065884c0e1803110326086a80302003101d141c8002c108481000719128521101060076000e9401e2945e404445105500664074128001006040c45102550260084801005000c0d000c00c1d90109130001180c49884207940448030802041810403e100080c040c190300700c42800c00600100d03140c000091035030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 271595233 1250 271593983 271594003
    0x71509050123010b16060c0f0f02070e0103060504050f03130302041109011b0204020f0703080609011401080c2a060a06050f0d02130e0d0903051c081f030209090a0309080a0203 77
    0x800b00000d11410807011003007100a05d00c1c0d000d10140003040c0c60301d0000342064008500f1001146a1642c607089480c0041002c00c01c1d50206034410003513030300e951501005000094030541d02401150b04040302160144003d254a150129a0710344c0140345205010460b2444185004da0035810300c41b51070b143c0e13486114110b55070441c550219046110b400090002d114001c90b10440510019401c001c0580202c003243c41640c0456580056a03615680720801e41c0101441c1800180214009015400c1e600040c082001c0d4900c0c0d490004011100b004251400c0d1100c80c0e040c076480721041055410b480e000d80c20203884292501052001903601066180208840081c424400850708420b0070009606c8484240121382c01c9541e8a00160382c051700708002070000351001d00800000000c44c1c80c0e0810210350312805680d451015a44107a052803500c80c0c200300010f207850000e8400000740ea40c1641c02d500a801c0311300903060440311450081c0003091175500c603540035002100340c1c802503a0007042d50290 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 271596483 1250 271595233 271595249
    0x180c08070f0207052706030705030c01050a03140709091d0d031e090f1a0c1b0a12030f0f0608030405220c090302040c03090b06120307150905012301 65
    0x20581d60740605034100340c195000290800032084a02c6000003440704c124107219a180e0403003029444440c2030588480e5113004550301944140703000501d651081d4010031014685144c0029807035044081100503980a85250000901c06030081c0821075261255102440101080d81d4094000c1c1c0000d50b19004491410018140e0396070110040b030300c500700d583c0b440e22070a500c200500009c91408510418010030107440b060409038120142c083c804011074007a002410580d42400c41722100c40d19040020114a1a14000e84d00b101c0000741c12802c5a10219a00d51408a030729215407240404a40813102502100c5080100401c140c9001000b00ca0590b0313002d80d05d106145042e000403003211000c030100080307114038100000c1d00c80381d03125912005681c0308950030b03c9030108450049065846040c1c01070414a0742602103802031501d000320354041c80c50071050764104840341e120707240b100010528181c00e150b2510011300800070203210b100c41201008142c0d098081c9000b03004108080140a0001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 271597733 1250 271596483 271596497
    0x1b0304060521360102040b070302061303051204030311032e05150a210f050f0c0d1d0d020609070b07080307050d09060e030d05060604120618020d0309180c0807 70
    0x844070500c10b18200f039564400039961641c2c1d1b401000c1040d48080b4041e001401030001081c2100b507a581d0014030b035605a070300d60f4181400ca980c804045e4202034800c070241035403618007011f89074443c40a148585084404000c0982048aa000031051320000b03900d030048900100b07018a035104a2070a2032240e145170032030b440f0100480c065a46c540002c029480e00e00c000c8581300608000c50301302c5100055034050904c019220072850b42425141616802e200c40810f0000a251210b180c0c00b49076602c440760050b4400d07800720601e0324140044910f640006030014000c0164014080080100034046030100c5450141c040d2250502804050070400c00c02c40e00050110241001d500801280c6800070410414801e02e0880160399038411240e610481d801c05001807614070b0088140ca08031855482000c41110742503a4540050001184044d140c0f641002c0c0700025071611801c500c4110704c0783c8c507002071450501c0105400400d1455841e03240d2802d242c10440c034258449005034001001e401d20103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 271598983 1250 271597733 271597801
    0x190504050a0b090a050c041b111006080a020117060109122108010513091203020a090308070b0f09060907060c0201021c080601030b0d020f061b0304060521 68
    0x64100121000302800d006044420300010000105030001005e214108035803513141d0800501c0305a030410b0282c0c0ca00605910065160940264088400130856000f5140c048880d48410021150190810b0301203a011001d9402107581050030345040007040c0000105a24000c8002080700b2038602071101e0102002d8011010000d400e89141040c201d00030701030000c4c1c070722500010041c3e0005d1051034400c0200c4942d40c42d58824920a4450680d00020072079102c20091100364040d5003c001f81303404100301c917030300000812403560180c068644501c0303014000d410a0048082c80c0400601010302d04d0f04400c05000c902c400000381c01c0e086030070904201c40403080ca800143e08003003a05d243d16485182918400084540c4400c000d40308410980b01040003805107014892401c1c00d1301e5000350014048010141c035490018090100c18804456000103070000703218a03415a089039100001148021482800c00d1024030117101102a89007410442450880c0d00903c0b98120000d580c3c115240c0c0500034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 271600233 1250 271598983 271598993
    0x30906040902130810090b060f1005090d1a04030306061b03080c0d050f1b0a0207090b0402090a0303080a18110f060c0f150108150a02090609090f040515190504 70
    0x200f004001e100e00b83c8400900f50740c502c5014051a0404030780e14042d0a0000d105884c2c0501280c0104202414440020100c54010380302580b0485c080ca910401154007400040c506503905141d00318660b031502068241443d01030706030f4406420400a008480b98562040200d800302c1c2d0040c0c0350903151220705134442662a9800c0d10801d43d86000d40c5050904000800342e500661b24011403000e081c504c0c3c41c00382148910a0350044880e15801a082100108007040503a0091b0720a500c0007000185000680c00000344181c0b2554800c40c04150040d041100068551203085100c220420700d1885040751903a800180303940780303801c4a104500303444e4901040e0f1910310990b210014407100300d4404032403079440c0c00d41e01c00c166049000110358174800031a40040100b12800c0c1c0f080401051009032725001c515a0187d0000880507801c081c05004d8080d0959446000c1c0c3d008607125582054070781000e00f0320320305000d800c42465041c03000150900c48100d52610322400e40d100d45e1b0100240c192118604 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 271601483 1250 271600233 271600267
    0x3030e010c0305370504060b0a06030b01020309040905150403170108030a0c0201030203040f080408010209090c09010c030c06020d0612031106070206010603180b1f0e0613093009050102030906040902 87
    0x3007132042c5844100000c2081c254040d6480c040125401601c1c10b50700c84048042e140c40c5403003580181c00078884000203080c07540100c02040e102d2015200310302408140e0080b484011079090300042d02c1d1030030b1070603580c4460b03207024054100704000c2c41c5001000c401c040c1014022000003810180d0000c00039083c0810800c200403650390001103140c2d11551540f003e0302079085406002c1c0300f0394608022803200e0507070404880710100181c4407040c44c0d1111361030070b44541c1c840d42416100c203078080041c40da14013170310b00c03860018043d410b41780c078418851820002c007040b600003040c103120b500c030320144070201c0c0c2c0019119044981c41d240100d8507a171200c6c0401d40040f070820000300f0249015050004c00d0078030108403007007001c0800790702d002196a0030800c802403809540c2c160b0892101800405581516004106440d015080030283c0107046035009500006016032441456264055800002d07445146c05d40240300901c0118181041c00e400034456100d18450344080306c0d400905030b011800358904d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 271602733 1250 271601483 271601581
    0x601020a05010e030903010b010306030b0105091f08070f060f1403070c0b04080301050913080d051503060712050c27011103120a11070506070c0c050d03030e010c0305 73
    0x100a0180860152001d40d41e5001825030503c41c7d42844246206544030f03110f80f8045a4114644688503481e000520650403405002c1c00b2060f92806444540f02c0054020200181154001041528039100350740c0c440440a8009400b0041c66008200c01681e000044048044a000741941d5945880e81d050f02d29413030a8100801c8075460804000c24800300402842c102c900a0310486010394800000400f401c41e8000d00501050060041d462080350661109074007822508441401031000c0001a02e000401c890000004a5959440102017002e00510740c00018080405041200c07181d030804404c051420340700c2c60050031410b0043c15030f1040c58000e50705440c000980f41d451110b0609001c07600c4080724059205400c065602c18400d40c01e80c101c0d0319447e04800a0041621450700480c0c24a0407090260388413043e9150109031a51032244d40ba00070392081c0c030001050401410100e0956440b071104200385440c1004100070100c42d0400070f010074403403c0c944200101040034422000103107203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 271603983 1250 271602733 271602743
    0x2030307110a2d050a0e0114060405120f0d0e150c0a06020310080d090308040303050306040608010608011a091513180804180c200106091a01140307050a080601020a 72
    0x14503841d038025210b08083daa200300720a415081d07075864070107011364400b40f442030003030f552800b0004204029500103900c000190052080749010b50722000110050882a440303052034000c0f90304030342241010485812001a641019a42803d1b1000060b4117170100015117000060f0009200701303504018070504403684e501070011234407414141b10000d03800040b03010b040d010707100e100003031100d00d806220042c046a500202d801d00e080e040d03a40845107600040d050f5074120391200004509950280070b404050900f400000070703000502c2140b0459801ca07101c1040c0210a014180a0502c0c1420780c400c49084044c0c071480612180c95a080004042049801e03e83c41da203410350804101da141d00400c00c5501d00d40042d011403003001070b800c04032150401d119012a4130340040c401a42c0000c58140124481c2500005890341e0740c0555034103850b00140c1d403c07901c0800668100f00f0351781000e4507010400710054194110b117022040640030b0300c14030040409000c3e009002440e541c0c420083c0b178480c0d035800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 271605233 1250 271603983 271604009
    0x52a0d0b090f0906010f1404090218090c01090e01030215130e090c0a060305060d0210030f02030a050103020a060f020309011d10030906050a0e0304030f0501061707140d02030307110a 80
    0x40a010342c4070800640c2e94102d1406644000a0840c010f0350006c0192100030329410400300038501084001c2001200c207e80050402c0c00d8005501502c00703916200380070941c045d110203e001e0000601e007003002c0e040080e42203285001403025850354084000188a100000380c0c0c1c2c0d0b0f521050780c41e01a62a58051000b4070a51820041851401b0422032000300301038806d5a24992501001e4060356822120150040406d61099016140009101440d05410300300029007001052050f8260f80c0206d901c103004503280d100401c21410322084009c0201010300d081c5842c0c0c2e6000f80029144e105641c4079130f04000c01d262000c040461140b0707c0103040c503002020203041c140b4910010300078044a8a05980c3c0a184c0400640400541d000d204440c0c942180610b00d0036080d0707500c9000c91440043d00340e52640da210303070106006540c0b1000030415041d400c002e001c0c452501d0040419040e507219898080c1070b05044c0d04005031400002d4600440c8d105295081850318880030411311107040d88103000601a0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 271606483 1250 271605233 271605241
    0x20609040209030a050c0f2e050c1501030212030705030d020c1f0504020310061511030d1805060a09020105031501122f0705030708030a090204060b03070201052a0d0b09 74
    0x2840080c0c5032080d60340c4c45500c0c7c0214100601254419500780503102400c004c92100e000d4031079005503a2005040c95030070f200d401c40c074861800d0f0600e10320030051010710b0018410340c9000c144503420401c4600041d883d1080303540e201a140d00800d0079840071544c000c9034001542c081408110526110b0102003000c14052010301000f07400b050b00d059010b805482d900c420b8950761b5003c0c40c4c0540e072092001e84081c600c2c05201b119081d810303030207058a902007880201108116400b17009014044880c10201c1f052031814024203000018111000c10f5161107003220060743c000003a29030180c507240d08210200b035070900690303906a640034051821803500031034a080c1400501c2641c101c0703176180c03160200103a0040e0401d0380c41c810640040c0c810740c024040c0c10005404000219071141141402103895101c41d404902610840d800c81c204003035010041101980e030905c00c407617200000c52061006801b0743c164400d805c01c0c07510f100703100303003080041c2d40c440740c9080e504401000c03040507064001c5890 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 271607733 1250 271606483 271606493
    0xe060403030f0e0f1c05070b07090314030c06190905161a0c03091014070803010312031b030b01090e0a02040819030206010501030914060709050108010503010903050403020609040209030a 82
    0x16110390740815092411201c2e43c0b2070030001a003c100d2a1003c0020151035005024a06001119151100400c0300401941c00000c40e52600c1c50301485550300d408890500310707c1e01c1c000c80007252650b101c0a5206000c6030160309000030708550000150101101202c6600113400e010342074000700a820786c82200f10604003402100500030454049008028404440c0c0395aa07186218180c0048095172007405240078604e00b83e80301401018140c00c0111240f41a944e109d44075070003085040d10645c0c1c0c0880100103011408075030901c81f00300c510b4204000d0007603079041100040510361071020182d44280c122810b034041c0a008010b00301a00c0312800514003011420080d40c0203018035500303401044403803c001240b0300814406c080e40b680240040343e080c480110024013811009440301403148420229a1105001750350040040c0c0d03942c07240c500c0c140000917210100c182d010034000d0f8940103805010903405000d94003503035411112b01e503964542d540014042e0281c040d0709580f5004140701c0b801002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 271608983 1250 271607733 271607741
    0x303080a0623031c0e0f0a150201020703030b010309150c050c010207060617010902060322080a0e1011030706110d0e100b090f070c0f060e1b0a26010e06040303 70
    0xe0b02141210326848030060454500801d03010800007007000c44650600f68035000c0f10003040300c0e01c044c0c60510003940d1030460f80810fa88801c1d556000d80d500040b440d05050703040c0500034030190300b03080a000404165684412001201601e640d202c0c3e9034a1000e60b1082c400c20441c0d408003660310007951602101d082c034400408035840f40c0303c2003400c20a100e9451a00600410040c944c00500090456440510105413411081e0303020340480c070103000c0103000580150140c032a40c02c080d5100f00c80c034401c40d418011001c1400384c950f01401100116400d00d07460010071078003c10b903c04c0010803503003500c40d0390031481d0140840e880350b2507080507100004040b000500c5c548400c0801c1c0c0c244000c4104800b48601484240d84412260305d291001803040350165144000c540e21030b540c0c800310f5203000e490b0582112454540c802c09900700c98592992030800c880401c101400c01c5880400403840c004184107607520300c3c1e07a03060f60010070100f00e110302c072000c1d0320200c40310328804143c41c214502482c6c010700030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 271610233 1250 271608983 271609049
    0x312090108090c01050a0c0f020307090207050c1203030a09020a0810022d0f070206090a0305070504200703030510030506090303070f020d0207050121060e0a050606030f010303080a06 80
    0x44501c030000e014440001010341c40c91078107840301c80c5400e0f2642c20848404040440986440c0000d080000050f10100720180040442010040c0c441400e4507103503051103030b809013103403117003d515440700004100402104d4116100f8200014103400900c04200c511181c1d500580b024020450040c0d61074000350000c102c03941502c0c6002d0200301d83c001e5010341c1c44a60074115a5104814050b6150780200310008206050004080c181040002000241a5007558100310b0340f54220741002c2000e800d21780207401c04595095440b0f003041011034001c500c540036050020307003056140c00116003031070550707850030380503540000c180c49461901c2414281d0340c0d4000e03598000010300103007011444520100d1035a1286030290b015001517483d00c030045452001c844600d145904040024400d2843d4500c500300041400b4001508240b0340750252004881c002090b2034090311040081122908110300c0d800e05403940f5083c454019103440420900415183d0000038811004400c000a5600041c1c1d00f1010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 271611483 1250 271610233 271610237
    0x17030315221d0c0d031b031101020c07080f19110604080604030c0c0506040605071b05030a0501090611070507090906020d06030b0f01051e06030415020a0906080907050108060409030e03120901 84
    0x100904002809441324030410080e001640341d100490fa921241c82c003041c01c81d0300a18122951300d41002c40c10307089a1100c04c00c0d14840d0b005240400c9500800c3c03000c0300001551601130407118121200421007800c03605801803800702c0341c0e0500d6015607142402d4030040c124000803030754107240c03620340a00701120b900d1044c0c44582000b03400003003a01e003100403a0709071b40150b50350604160480c0e55683c441003040000081565440b10081640e480403c074001809000e040041001c0c0180e0518208030381600d00201c580c0c030070400c042008a0720000780b900465913030100010b24144c0d40e043c800000d0081032a81e410030303805c0c5030b400006e2000e00d004950060035030448503115130741e0b140c080049070000d0b192a02804540d61415034514500307a8050340d4000c0c05600c001c001051840d00f00741c100d034061482400483c95812003800008d51008119500c00b178603200900120f402c110010300b1010300142810320840c0c440c1104810148540c5800316018005011a40d254a0360b039210f5640c2d40000300b030b40340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 271612733 1250 271611483 271611493
    0x70501180b0a05130902070312180b0a29100507030c0213051509040b0a0b0105070507060302040609291606060602030c0c01031407080612070f17030315221d 69
    0x280c03a0045201f101d65244e81500c0d120741c405441c5040c540900b104040000000e003071125840040742000c41031350f2294405282c005088000048410003a078145203440441414440b90070640d5215401102c2c608405030616503100c01081ca006c83d540c282c1c4000080d0000c0200c0080e901000c0c00c0e401c407a0007100441580c03031010070a1018003200075403c90f4090b10b000788480c0441c040d90000d80c000b16404106141252034070803070b074455525041455002e1000291300080420007039a0040600010b403d4814682c0300403040142d101510500107401006200b03000201080b101982c11a50401d840c0d001d681801110790315100070f034403178111609600703050103440a104000c3d84030b4030980e0070400e03c0e484244890f482e0f1010031184c0800081405c1d81150440034401c0c281c1c90100321440c0101424403100c40c0c0c5a04201c21400c00e4070210503002c2c40c40d482441840201416803001e00d212030000d035a000c40c6424800c84000c040b190700042041d100380740401c048003280100401600c000641d4007207034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 271613983 1250 271612733 271612739
    0x801080a03140a03020c0f0304030c08030f0301150905030d030e06010f0f090507020a0c0f0623030a050a0b040e030d05060d02010c03030b18011715010503070501180b0a0513 76
    0x40d0312500341a0005000a0b081400e004035807004401401c0c00180384c2c50b0050400300900138061030848101001d030110b03803010a040080080d1820560043c1c030008001c0e505000f40545404d41c07038001030055800b40c50342d04440d1480c0c50b102c0d8207108001e146c020201c490024070580040c0c010b000c000c00740050303030066400203d00501c6181d0440125002101d035406981c0ca02082031000708805404601180910b1081c00d000c10350561012014182c00210498403e10301200038050604406c40c1581100045c000c8031304d42d400410070f40e9840040d40c100401e4aa844002c4a0003c1c048000a161303c90b20308121107200c00c1d000405098104e002034001c11158039030104009900d800b00c01c3c02400603a9906060380000d11a030061a0401c50280540c00c0140601903d83d1045038260020103420700310780955460240c04001000e008419204130885550500000c251540d48502800f418000a0050f010400c0000740b9880000c1141c4174016407980c00304180108190300005120702c070400019804 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 271615233 1250 271613983 271613999
    0x40b040201170129031b0f0d02030117101401060f09081614040902060a0f03090b180c04050106091205070b1801020d030212060904050a15020a09060c02030a08070507080106090c0801 80
    0xca000351041016980c400402c1408100c06e40d1020819000ca00c0f014007018800412034005075001e010b41d08042c00300c101600c410340b031a02c502c082002d1a41170400c00d9040190600f4034800d07054038176a10b00310f01050b49808082d103050b02c15501008451140d0f00480c040c20100019640980701c0d80852000c001004030f040000740e03840090301035030218040080111490103441c900d4190102070a021a1002e601e03210700543c14011900684941200740e10b181c2903002c24040340f414401d0440e0300304003c0d410144006c00d40c4045010708210580c10b41000020f024003085904010300d082c1d464260b80e904039070036600c405541200381c10301611a0345034000d14140a070007500c65215035500d000905949076410028100e4000c0c1042c0c406001e59114503011030b4108208806602c01001c000d0f940740e40340003002380302d4140c1d40d10000c1002542c2c1c000c50b0041c1d0740030903025100c60308203100c191074116500b410750806600342d000301c5440d0706e05640000d008445400001260300d01c3e4407101c8071682d0310014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 271616483 1250 271615233 271615237
    0x40510020a050d030e12040306060504110c0d080a020d050117070f14091b0c06060906030111040e0703020c0703051f0203060102030a0f030e0d0e04050709030b040b040201170129 78
    0x10080035a005649418403c80c82980010500c0705590103c0e0b0b01c44502240084565102c0d40040e40e081c0c0d00c0e02070600560515000b11071040020014480c6001c070300e24205500c4540c50203d0008000104001c9141d03034240f42c0565400108e42c5804001c256910280300da0604510041c550302070140407000641c500e0381d4403086084460746900742e01c2025180e4100701c02c1c14401085c210271840e01c40034541036441c5140c00780c0200c01d0440c000740010f003801410000b000300b005107240d12076818803141c2c0c03400340c0b101c0081c0e40481e110480e03004000d464104003500039009003100806141b0406400005005c2c0001d46c009002036008183c440c4101140d44c610282d01c02140c43e80d01603070003040200c8040d03200d07040c450b086108503d4002003100243d8081810300010720000c200060010030b22588a10b007a11030f958009000e401c1c03100105e0325650729400161001400940000c4010f00003a00b564081c03240c00124010700b510500d4550785501c1c0c89119407541c140d6541e000344e400c00e04408802c0210701 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 271617733 1250 271616483 271616503
    0xa0f03050616091401090b070b0a06081b0409061d1f3308010e0a051006030b1f030f0b09060f040c05120c04020703031407030b0d150207150204051002 66
    0x95111000c0c0c0c1001e441c40760340d000521009042260758180004c68030303042805051083d11a000900d40e41c148130350701c43c09a83c8a43c010b93300c1a003002c0e0810311040c0e000702c09420381c080c05490100d086405070800c0030081c840180b0110700c112101c0000045020003203400300040c0c90550b00c484101d01018003540c00c44040856440075200104440c41c10181e950341c158180bc450740915030000c50b1164005800d4980c0c010710800281c0c0b080e10349404011050002e201d800c0c00c50441001b11a00c1c6860310048003201402d0b0f010061204040e80798806005800034000e150085407249080b101842c00c5c42109030b0441e220303c458001c45000ca40304074445002140115003100d65507030f202d030400c801c0000300540c80f15004400e1040c0c04203030a003911680050084513009840000c2c125100c01002c400840005040340201450181555020b0381e441c08003411441e0007200300c0d00300a468111010091241d54800341103030204006403480c0b00d2082e00104103864040da800042100840700a03030766844500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 271618983 1250 271617733 271617737
    0x9060e0c0702030f0a1101120e0705010c0f060c02030304031e080609090c0d05030309060915010303030c0c0203010203130204060f060804080304021903050601030b0c0901050703110c0a0f03050616 86
    0x640415200d00300a805484020700040c02c0d50703618001000c050346454040d40040f0b030500c034a404565100c6d80c100170512a0b8000c415028007812443d015842d40310300690080318184102038241006100060802018156004d201044580a90b01c0c01954a0708112400c4001440245070720900f0030100310580d01591a503241e4030144e844000421a500100070f06440f80c6121785060901c4954912014100d0b580c0128080e55580c20b01e0001316040980080004030f42e94002030030f002451140b07108480c1140d0701854001800c000400e42200d00c0d1098040c083d6041d8004014001c1c2240c20302d48100c80303103208441c10490b8a6540c80389090305038031b501c213403008030b020200000d000c2804030004543c401e100802400804c80c030316010055006840d0400c1d202944400010300c100900ba1050030317000a0100802c5043c14880c0700002c100303200355080101044440310760300b50f001404002c400700101c03005007001d203655220440321100010510090b0340b140b0038200481c000c00407000c00c4d0b00404a160b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 271620233 1250 271618983 271619009
    0x10506060403260c0d0c1e02100c030302040317031509070203040b09061905130801090c0b0a02100507030c020c0901062a120503070f08250309050703030206100906 72
    0x2500c0030f00501c0d0140043d1603002c1e0010031015a60442c00e002071102c12689888000f88440f85e401c1c04091041600c00d0409801e198062800c0540c0d541710041e8a00403840c5031241c44100f561501318064043caa0000780200c0511105509001011000e1031043d01600c11030070303150241c0c404100c014003043e509000075801c1084180705401c86a00246403282c40034110b2840d0150800d0705004248440c40c1c00000100e002c10990301d482c900889403801442100000d0210848030345440e9601101c0e80718040c40e0050010b0906809030090011041c075400101e010012807522000190140214101c00790044c000d01c2d006031803a26000680e5410703902c1654590050400c0c00c500b00301d41081164442100d00f4500c0325540c0014003032240c81e515041c19942e46c0307840c1d08111001610285d4074400e01d0050081c4402046880442c2c11950100c00c031101c03940707401903c2d552205500a1240d00d034013910500401341d010040c5600040da66001e170a510179021311103580c40b480401199014040c4d12603010f51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 271621483 1250 271620233 271620263
    0x703090309090b01110709020405130207050706050d180803070906092114010f09150203070c0816020604031415040c050904021c0b0103120e060d050c1902010509010506060403 77
    0x540d81c02603c0659041c140044410064104545001d44541c400540c0c1500003900303020900b054804002d41d0685c2d007000390304003241503030b03402d0300c44100313000f1b50080200101d020154070310305400400780f003051400305043e400482d04200d10658070171140e100211315030b1400004c2c01480740a000c012168940105040d020350300941080400041c0d03025200c00c0d0806200d020242000c0c816030100b0044003e00081a445601d0000f808540d421010751200d8414003c101c92143c00c80000050700340d02a062644e60300c80d01132070414401c000c60000e904080049400b004001e000a81520050181002c5403406e1200714664aa411804c9030020a80410110b00700030030b040285425030007500c010701c1c0b420700c0902c2140100600c0300600d820356902c514000100f0901c600340e05030f61004a01440c1c80300e00303c10300f503006c82c2091042aa850f20743d0b6544000180803940c4034000e1790004598501080c4500c0b002c3d0b00001e001c2c0c901079614a80c994a4003000c100c85160690448007101d90000d25044041c0e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 271622733 1250 271621483 271621499
    0xb031305030406271202040509010f06140a12020d06020c120a1206050901060926010516081f0b18130204030b010509092109030a0c0e0703090309 64
    0x40540594205840140810001581400608050611035682d0503130444800d10f14a0003900000d500910f00380c00d9901071002c2801c14280c0c0701c2045d0141d90104040d120441070300e004100c0c400d404006540b500c2400314003c448540c441818040881b4000409034941c44000e03501650814020b40c00800c41d00d00c032001940d182c0107840d9030907020080d02d08030341c00300c02c81c400f15510440031940090380c1c400034100c42e03c3c1544142c2d07010b40320503501d1881660410380007500d500c00c80d000b840e440342800c509241019031400f03140984480c0d14002480b850510025420703000c0c4031a001d503004101c540d030006401c040c070412540343c5c01d400c0c0d00c02c02c9449490a0f0982d01c1c243e01400f591085050b90000e10689a1515a1002c0307100544001c0140d940b40795040240c607070b11040c0c00240c4215114001c2c841e40203400038030040041c2c901c4014a1080703010010140c014460b80c004d26416016008030b00b003d11905050308000c4881c15400c1100642ea0200d044084501d5058003c010985200e81400795030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 271623983 1250 271622733 271622737
    0x41e05060a120f0603080301091d0c150d06090506090f09030a11160609180504080712021f0221130b070903050601090b042304080d111206030d050c06010b 68
    0x82e80e034040c0020301e008504048025a5202c0d0010f035104103001004100b0b01c3d000303102e5200511141540e04200c501040c178059183c102d00700040c5c0c8a81082c0e861a1844004001240c0414901030420000035030344650790005800201c075054405c1c5014070014030241e244c103034a0b07885260303040003442c0b900341f9000e02940d946074030f4480b094040c42140c4060b007803803125014103005051a600c0d101c88613131030884442140c1c0d040d40b900709101c5040c8020f2000061201c3c080c0c50541e43c0c0088544400105030200303d2074024005895410381d40580340d10410900070303900500701003041000d03075105120b9000000703821440550701c0203045855001e2036400f0440361006150040362614041101c83c1d40c84e122039241c24001e80045140b00da035084024002e1400d8401c415052004c070400407080300c4000000b00034510007d1025010000002c2d00707004122090b40081080318083d600d264403407041d1040d41c1c00350f1070704948641c021300c02c058026404c240101c1c10b0f108504181001011385a080041c841a15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 271625233 1250 271623983 271624007
    0x11403090a050c010f120f02090d11030c01020c010509060a03020f070f022407150605030a140f06060306160c0204020a020c01080606030c07021e0a030b2211040e100c0203041e05060a 80
    0x12350130701071003020380d4030200c4210a40c1c0c024000c80007600f10720410541840e40e05040241554030203600e48041c0d903003000c04d5580c2a20b044030050344600c46218140d002e807140b0751240450340000a00601004150101c0502c0b95009443c141c090361802d041140c4200c00a0461114a440500420340040c9003013003100303020a031811380460001e03501c0012030302e4000300580840d070300c07100ba07200c0c01c0d1660010055251141c1c109001070043d0b04000000c41c2d00d5100140030f0b46140d40750000d00d0b044890080c0c54051145078050021599030b40000300c02034984101c1013646000490070340c0071038040d2804405582c0240301200b104c526003803031039007044201e01a10700c07264002d054208146400d580e0b012000030066004000000c001d16080c002701070240502e07a921141c2140c420204000b050b525800090030780d0b01582d00083c05402c5040e035a10b81522150001002800c0601001407030b6408005802152500000c40e4002c3c032110980c081c40046a00465070400000e01070808064491250f00c296 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 271626483 1250 271625233 271625261
    0x9041506050406060e040b0a140d110a03080a0206101a13030b28090f060b0121060f272706020301030312050f04020609011403090a050c010f12 63
    0x2101e40d039902050654a85500c40310218400c00c0c6000340710706040c010800094011038290f5611820100400300c081052101c4074042c2c082060101c2c00c10100f032824801d4154000d14032005641e0741c1c41c216a1719030000c45444010700401000c00d14a40c50780810780180c43c030202154412483c4061000c42540022040021801840c01d0010110300d150340945e00a003d400781034028592101c0c00040030300148503e02480d140761407400d101013403004180351161035004501047c400318010049503d071070034402d000c0041d208021036a002081c0c40d4171500c11030b80d00300b0707088201d1640ca640b50090000340340b0390f445c50121002c0b1884030450340e41c0e005844119140b140b29006000c01381e09600d080c0c502410884001d5400001802070681005d40440350000d0954280040d15010700041d041e502c0c0588000c1c06180007180340c81842c2e014480040082c0d080e00d9649440c0d10702003800b0740d50b880c88003900340d81901400e060045194421803000c1c00a8103503031250342aa000f1000614014420f02c1c0c0c042031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 271627733 1250 271626483 271626491
    0x50319110d051303090b03100b0c0d0809120f03060a081015170a110448170702070308030403020d080c090f12071a03160e090415 57
    0x2000429034800d8624480c14480c40c140c841508140d0502100c002800e44031052500c00c0c10540081d0f480844a015510390111907501c0b9110069580a01c1300d99400000c22000c000c00e030b41024020008014881c0d41e829902c00d03566841e009001d64070351002d0740c40d000082c0000c0140c40b0a92450400554106001030400e5850303035035460b003080c2000e0260312000000344e1a440403000f00658825203201820092036a80220a42012065928854540d0082101290f0003000c0300a681e20740c01040f04003000245200055602215421511039044a10341d0070020108041d03011800201d42203005070381612519102155801e20160341100148010210b00c10500080005800a40518000c600c030b80c005000020740c503803010b04182d600074004210389000303110400c400c1c1d44048c4084109407045d540d0300f21034051054440d05088468004280c0881c1c100d14041006948100640c89050014041c1106400c4100700301c5d5028ec0442c96103905c44822401308011540e108400c5c4116034400d10002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 271628983 1250 271627733 271627771
    0x515100305240f030604080a09050103060f030b1f12020103111206010815130506120a0302030d1d031815070b0103020909010e0106080106080f010b1005091c05010207031106160503 79
    0x246808411141111503440100781d103030350ba270b4102e45804060700003400c0c144109420080891960801440090015001e079404242081d003d4001190911040f8661440c019202d09031040784110000c4200d00003860001035151802c103000580f0f40074444d00c1c8006105403548801100d0515000c0d20010310a0100e00d00c0240d140d0b901880c1461071091414003081602e0854104901080b10324042011500170000ba46d0010764040b00703d5802d401c10810004201d9a0214050101308022000310124803000401c9011801e8050502c81ca011046418000301c038101d0340b540490740600100104103011035401072006290500206038803148000000500c3c81c0511986829604660f000e403c05964801341407100000c103200141f80d243d10600203120400860000c2401c3d0480340b000781c81080404143d080d45982e41080c03440c080702c0d965048829040c09410158000c0d40502400c038080f0303445504401c40c445011441510482c100300a4240c0700c25a810240d800b07500051009002500940c080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 271630233 1250 271628983 271628989
    0x3110a06023f031302100516080307090504060b0304060b15030c0a05090402161403071505040201030204030506090c09100302060304031103130f030c0b090901060c0804090515100305240f 82
    0x503612030145142244504d10182c010321030303a50298403241c030401004000043c200c000f040e00ca00b4a0360303880b000082c3d59988855040f04d40c654190081a481400c0c0f2000003443e00744000a94061400364400b08540324950007080303540705038258aa00400f600f80001076504a4080142207801c1d00f40c04d01d6850000f040e00040c08070f81c041d0300300a01c4409803841201c14407043c1444004082003130700c010340c58040d05841e1003100a400448a01d862034a4a00003802c591182c1c040e00c00469006080f90312900b89060301380d440300d40c402152070281c00b9220004056800074140c40d0100c94020709458990348a944044800c2c0c0c0b04500301818510040000300b2001c60004062001050b41d44200c519590440c0b40009400420350f000001b03404e000d11030202c1030364403e14001e0442e5000c2c288a022020a403a2241a900841e80480c220314502000c0010403499240c050380c0da20340403541b00440c00043d041c145c0880d9030550b262803540d84c10710318480c06240c07101c5a103000d0b01300017080881401001000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 271631483 1250 271630233 271630237
    0x15030209040f061206050f090a14030919210f0f020409080309010218040606080f2d01140109030305040b0c031905130e0402011e031503110a06023f 65
    0x80180a500c1a41c0e800901010b8401c040d08a65a40c1c508825824111000c65643d05480c00180024000c5128800250820000c9400d544409040855001107207111128200c07054828003031a8089102d2041c003448902c0d0002d0728280d40009e440c0b800314070685074409207443185102203800c80e507900d035501c010921040242d842044a8400036a0744c40c840c410784403000e41052403032030003241002418410141c10181c05a8402118011096140d0340d800c44440310070701c03600749000c074090f0b039102d191442c08042d90128141c4005091124403071418000443d131280d03041c0f0010340040c1d0203000c2804959500e03401810000404800c90307040000a0040f00d6200b40c0700c0c4603040100d08005150001104480f546400901d02d0b80c51445942c40e041d00064160b0850a50000e8100c0d900d240300c0c0595401f075801103060b010081d07428601281c40b85440d490b080381143c083c9104040241002410302d00c00a8240f1000401d0010859800400303840e0540344522912606503591010340e42d1a15000b8200c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 271632733 1250 271631483 271631489
    0x30308180a0611040501120905060402040507021f0c0f050a021e01060b03150a1a0301030b19140106020628020a091512051003030e0f0312040608040c0504050115030209040f06 77
    0xc1d41e5031720740390000d0b022070306503400c508401d820708282e42d011402c0460440c1e40680c050313a0105165496803c12418130741a0035001c643c0076090405040c40d118580e010349020701c01500c4124a2044034101a2907c0c000c1a5009005034410000900c40390b4402e42148903840c1c1c4c0da800800c8154443c095000e298200301c0c2c40038103040500b44525628640302541e44011310030302003030000c084040d036508000c901c014040908501441c80c08940d1011880d1b8804400c204141030811a503031080f41841d181000a11407400144a01d0012940c45030229150b143c10004c0c00008000f42c1140c4802c0b00042e4000310080707001d10101400c0021080c4400c0302222403035141c0c0d0345030128001c0c0c0c8110f80d0100c58010300048618544680140002901302e485450001c00844a00c1845858800081d20381000300c0300d41e003c0c02c8004034002920390b801414841c0641c3c07244a1141c40c0903141c03414041110401d00c11703203507410644145804035900030f900806407010b0180010600360070480120302a40c100c1d40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 271633983 1250 271632733 271632761
    0x60e011d0c120423240c040e01032a0608070e040528020c070602030a090803070b22020a150207120302060c070302030405041b0e031618020904140103031701030308180a06 75
    0x8030030360000c21550851981d0100c80c0c480c40c1d030708190508d202c2d40710840c0c050200404a0300c42d80c40d1010a01c0038075803452049400140e40082240c0c0b5190014001c0000362680c001060451400e22901e01c0c2c240501485021b00082c15206084d040200703144c42d2483c12325101209908003e0301803c40f00a00481000e0308081e00216550340014100824002c0c0a0380300c40c03902e400c180000c4000070041d0006507081043c441e188911300c03040c5e43c0c0601d401c2c6080034000f94082043c400014040c1c1801d5071304c1000c68002d8080e229416660103a000380380010184c010b0041e04401c00050114155501402d4410301a00c11a07080c151201c0c0420102e469088011585001d214012044281d0040190f5800802074019081c00d050fa0890305199048900032428100f41d0040c4594072247d095040c2c03005580003c0041c4039100f12115590340d846002e0105030000b460401785614142c0c10070003514100caa1640d9030700281d03a14100c00c0444c6146040e200080c27400b0b0301b412400421003e00514290103055 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 271635233 1250 271633983 271634023
    0x1d0d030302070507081e0a0c05040b03030c0a060618020f04030609050a0501090506040b070f020714130915060602030a17180a05060906060a12020d0501060e011d0c120423 75
    0xd441c5c2e0349030003806c0c3e005209681d0b00800b0014005040c448400048580581d0003040c21044040064258056040c0c0b1456920860f1820300a000f0283c000750211040860094509120400c500040c1d2007081130440001104000400001c0c4095004c100c03018003402c01c0c0c40201c0d0490f55403d00350b40b143d140545a90348a002840140409003001c282c000d8050700345035040604100e000b9403115060300c44d103441080f42003540c5c910341e01d44030715115005520250811000141e8601007414480c1e42160349907461030310201142c03070750000040340c5916030540c80305034600c0d08040402001080042420200401580301c1c540c0c0c0920400200380010320540190911307142c96614107140003401428544100b0212004005102e42e084206070110b0301510701114103001400d01c940984060352080300030b0502c0000009411074800c145030a050703038005061a003030321941071042d058003440b10305148200782840414005109110441071044014400110180720700b540c4c50705204240c000b01c001c030140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 271636483 1250 271635233 271635253
    0x3030d09060506040c08060108040311030a050712030509071a07060c02010e0105060a1d1f06020708010b04090b061306051e0307082b020c10031b1d0d03030207050708 73
    0x40d00540da030010098078100b0140c40801d200a000c6c01d00580044d040c0580c51011405151244110180d81a0031004890352080d00d0400204660b03c0104240c1d00d50700240c07903580c0c0561084c000c10380a684000014542113040490001900703c19000364440030000b0424003000510300c0c0a5a0b0b448006074000007000344046280c0c81c02c0d81c000800062284460010610260340940c031009514541a0040000c0307a54050704581040d802036030404030080c80302c0d000074006a0005210003078400e0000244001c030a0001401b054070000300f4004c00400340c1c5030000c0e1083c104005020805000b0001c003194941c1c1d6640420110b04050680c0c04081950109070081c80c1400c000e00703802170443c1001025064091013005141281104682d00384034911051140000c0c400c010760780d01118010610840f182c0100400b4000b030001c00d24001602c1580781031405014041c0d0481c031501c00150010707984108400041006004042c01c0480515030b092102101184003080b1060182c458400208420f1507 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 271637733 1250 271636483 271636493
    0x6150c0d0824130f090f0c06180503070b0c0c090c09120c03120a260709050301150501030e070e0c0405010e03121206060d05041b0510051608070203030d09 68
    0x40c0c081a40ea46481c8150b190070707142d103402c07080718410341110b000091800419407480000d41100c110240c5071840610818040c440c2d208400c0048901d503407206501d10032404402040340c40303184039050385504400c0c1c0c00c00108485600415003140900c054421040310074002a070307009003d4640201c01c4801140d00740e80c3d810b1204030b0074803a0030940c004010088106c0c0000c1d903a40350240059078580000316250500900403c44002003454041e140121812110705007001030784115005000504165400502d5040620801c4440014418075022080c10080150058203030031005102511540d600012545414540940258034a0148954070381c42c0c640014030084079031030b140f44250000022200428584c2048420080c4400d110752041e650300070010b40d050041e11548001c1c10b0410003000104240311030905444021800d2001889403030b00c09000124a400c1c4c00080450010001e100c1c0d00c0d50303500e00d030b800083d2284103800e14020741d80d40480e055404c4040044002074441a04804003e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 271638983 1250 271637733 271637761
    0x112020c010507030e0c0901031104110309010506180118090c0b04080304030512030f04060b0105040315020901030507020f12090d020d140709110f03130c0f050a090501060806150c0d08 81
    0x101c01c5400800c00007400d06c00107420307400c0612005011000c801030030700140d101c5070802c10080c980750b680541c0b00d20701813010a010b06412505180b144052414101e0300ba07422203051810b9400c0c503400030440641c7c00a1900003802c3d07859054600503110a0000744402041c0003c00c0900494405191181d20f9880d00d80d1810ba0028440d1a01d0403081c004c0001c2401e44180035030b4059004540440d0380401840161a54401c80d04050f01d80f004420a8044080480c1c0051a1050f000ea804110700e07500c1d41d100720388510001c03640e4a0250080022021243c1c80304002d458103550042081d84080181e078000303040c500b0440c070b08a4042c2819641c540b104d403c01c0c0a2040144900301003400f8030b0b02c44440040c0035200c0c00380035103800700001c8045811304801c441c5003c80c05900001411095440741c5003050302003500c0c032131940724080704e400120b4242280d009031412541d154450070010b483c1c0c04100515040e001e05500003484043c0691f03401c03160100000c00802c1500e44075141d0500b4502031413240c3c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 271640233 1250 271638983 271639001
    0xa0f05011701050d080a0309061107050d020a030e01032307020703050d0302040305070b030403030b0406181109060403031b151d0c0d0204020f09191e0807140112020c01050703 77
    0x301010401009240c8400c54a040340170b07406100a5640c01035140c003a00200985900038100c43d01d04031a044c0040e444030018031005006004440b05c0352074094080ba920782c51024020009403540b099140654002d070841c1600c0844c80e020340901c80c640840c90030a1420840300303600180e119420410a01c07000340013010400f0201d250075898241961102a9078084502c1030176445040000064280f51080e8840c00201d44020801d06c10316541d0f600003038081c00c0d02804d8403001494410341c00e045000c1c030070480b0800718029014074141451920191094a1240c00d40c00640c2100e05c100070020384c5609a42402c000c5000d000070344100c0744c1201c1241c451280c2c1129100d64408c035012041c0d42d0380c10f01c0500e01c4960485015940718804007100300140100c115043d0001c603440070082c000410f0400c5030f000e5850740800052401d070f44030070300d400c0c03801c56125410035500103034030511580b1540500101d254130103040ca0341c2159850802c91080760f208400200944c1d640380d050041c0c6a82c18002d074102c6c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 271641483 1250 271640233 271640267
    0xc04080105040501230f0c07060f02130e0703060e0f0402060c06041a0c0304031707120c03050405160302060301090218090115090503070b0a030915020f04170102030c0901120b0a0f0501 81
    0x85468041c0003c2c001c0c46c006000c5403c182000701d00b0408101d1503030401d4295840c01d0405544400c1c122242d0080144903014001c1420114000525014803030700c2405d048500f40c02481243d0b0301c0364025424400da0240050340c11032420405003140503020400b6034000c07442103848a40e40b40100c981131017100c9024007011801c000400074040403d60007403010034840200c01b404801511200419602c0c260030201e400703441070902c0c00c1d03d00f8207070301a8002c030700c214017a500780d030b4005291030082d52504819000080d4010401c0c001880070341016400342c06503c1940e8412200740d01a41d002443c0c2c01c009901c1700340801c954075000300300e8a5001d01c010b0b00034a004c1e00102001c0341418480f400d14000c9184d007000301507854140d0400d00142e4643e242000b01c098004550701c0c40c00c400d5031140f40d4018002d224600c1c5e03817003a020703010400510840b4428012401598149512007004641e26082e91044050b81d0303455900c2816182e0702c0702c01d08001007282c0390014415500d480d002404528050a892035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 271642733 1250 271641483 271641551
    0x3050606060304021509041506020f060c071a04030210480c03090b0403080a0206010f0e0103120512070806040e071a0f120106050417010c02150c04080105040501 71
    0x41c0c845480c8100d504c1c0c03040400941b100e84407004500207103041000d1a91a070581c4000041d0180c002c02c3c440c5401c2044015150b165481501e640e030310f4403a04d50028140c1461034280380c0b09038900036015800611a1043d50034151444d0b5001d007d072461201c903c0441032a40c00105940d0000240390f4021426110403183c042c0b04010600186d0420a030740b0009024540300080100f40c0300d040b441d0060f01055420681381d545034140100075030007901d240380c094403035080040f404044d0901100c04840103070801c1001030382560740c1c0d200e9000700c0c1d502480500009201c3e8401c04030340c008901d071003160b065803526417901c0d00f00c040006481c1e03071800313880c0c60344c01103141400b030100c0001e01c42480c02c41140106070b903071002c8200412a88950007051040c52000400481c01990100c000c00858503031046841450200d2030301217080f50381480310800582d20581a07801090181460305602000380201c9505250365880103d0a4910031a0100c0352a50340d200400c0c9158034401000900d10250100c40e6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 271643983 1250 271642733 271642741
    0x70b0a09090203072a030806040e0703150527030418020405043305031518061303081b0904050a0209031f050c0903070b0f04050a1214010219030b030a0219030506060603 74
    0x150624001a21690013140c40d00300b0302b1440340342000071400642d800751020481082c1048090002c14040d01d0020f102e100035119022224409030010b82d020342244040c51805241900102e444e80c1c3d41c0c24401078554090000145d40d60f03c900c0313190f0981d04000031810707404d151031610310742070640716000c06425a12100e051101c3c0c0ca00003591521910b00301c01c20300c0152540f40750f851200c06601c800031007034400e000c00c0081c4592011280c8501c03604c2510b4100180e00e49040c0d5a02d840c211400d105c04c0e64a003030001d125140360039008a60003004052005150026070030120f81820f0709500800341207002020441212149481500d0b40700c03030500311450601d003422000940b281503d1003082408017000c21b070744500c1e482c0a402c540050900502100d2038540d250498034000c440960140c0e09550380c541290040c200c180221400c11665151000000c2d034240c030190000c00c8002c2c000e5426124102c90280143c0301c5c0c400d00c5805210545144c4013051952808520700600104441d000301c8083c0184 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 271645233 1250 271643983 271643987
    0x711010b09160e04022b091e030e0306040b040f020f040203010611061e0601230a03061e03031b1502030f041b0506030118090506010e0612010e070b0a09090203072a03 73
    0x8486c4540c40685400b21021009008001412002c0c4000d0801481542e10b990620803800c0c4954641e0301c41d481d6400120559020143c40c0e400403039001d4400c880900000c0c00182003182c000325145c3c0f006000c64200030820020408130382091b000100482c0c9681d9650400140400800358080301e101c01140c0c0a600b00581a5144035014010905015040110a03e0403808200640ca516888440345896507120180103000d0b250b10f1103281d05a1540d00c2b5420b18910807508241d090720b4060f00d070148130501848400c0600720b000c0c201928048220110b441210507940011070166181101f002c0440c182400c2001c61400d100c51942103090083d0410841d81d117501301948e04551a00484038844426142900051300c018040104240103401c0040340341d0a44030500b42c0500015079072010641e800d0307109503007212189036203a40e56501516040020010383d40090200305100d02e00040c065580b10201d905030b0f0019640380c1c1c08111911504403030303000d4401900d0444140344000501e088059180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 271646483 1250 271645233 271645267
    0x1c0914030a0f2312040f090203041703090102090405100f0b270112051003061803120209010e0a121a07050304060b0f0d11030d0c08030711010b09160e0402 68
    0x501c1e42e10f841000b4812000c0c202004440403a80209545024139101c805034410340c410b02501d50304060014012135080001d20070b8912469005c8072180300c184080030040380716000207042c070725659020803941ca1540c60b1070040e180500480e1910240342410104c52410111058110b040c64050a00130414484540042200340f540300c0118031440d48802c0b401250001e642c0d80041c0c00c0107092506000c80f0030301c081000c40440f80204e0007001900240a0070b80c554180c0c0c240c0280000d0003101217403001d519a0b03402041d41000504010111054bd0000300303001d0585580703c05080101009480c0601085050122505581c015620205d1814a8002d4000e000c090400b0f84130598031200c00e03019880304887e8030303002c0c2e900400c081c404403520f02e006200540c4404065010f8040c0251440c9003078000c51600800e954004945400c660b14154126450740803034054107099900c581c003100158403801d4041d4081c17407941824400503150301c0f1003e007203110855413540c0a14810441c1c0e42441c0701d4548 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 271647733 1250 271646483 271646513
    0x405070e0705040302090103050f1204050d08160c0e0a0f05040b0103032001050a0f0e0703030f0c060204120b15220e0c09070207080706090501080a09051c0914030a 72
    0x300981107450710341d07045415009039000250484000c000100620000117200c1e9241d034810710496040c0005c401e8044900d0081e0700c00d0f50f4000018415006c0050320401c0070740f0041c2409010301c01510000d0301d17a0800e99420b6030240f07201c98540001e0160b00c2da01c0d80a42c0f0342d0088500341c140000c4c10550340355111100140703c041c0800644540f000c0140b10510003480f03c0c611100004c0c4042d041c492a104020006c2d120080d041a2403d50690381c0c01101050780c8007140d030951101181000280c02c10b80d00c60000c6071003102c505a0800000c0f40c101016602038618a01482c0250136501e055900100f0700343d146c0c4603603445500584541d5100691300d08048881510082c03020032450501281c00d85407603031701c41c0001d91120403d0304000c2c210794001100802c0710072540881b0041c580e00c00d1300340c502100e14040e490003d14040300103101030360103400414080348901c049546643d490619142c038a03448400d900d00050320751408103e0402a0300e07101d0090903003140a410004a90744c0d60140c03d00c0004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 271648983 1250 271647733 271647749
    0x31e0c06070c111315092f0a03020f07210809060609010306110705070803030a060b180411070b07080a050c04120b090f060f070237060f06080109110405040507 70
    0xd0300034000910b07000f03000c6070100c00321117420080e00c03a0010743c09005161502c0c440c540781f442000d081421010040190f2a40034100369250841c1030300304070b01a62111100400d503803000c104400c00901d000c1c1d0030700440312100221420031401c1040003428030034051f0441100e58040e000f80482c540d603c40c0d241e030440e64881400220031242c00c0380c00d107a034003a40b540a405400356440010f41c242c80807004600c079244031082004003039241c126048807401640c810600001c0080e080310540c0c207107603000d0300350240c42000d02c1c0c0c2807140c59030745c10600341412200f1070006070000050280d00183c80c01202e410031907002c280c900702401c10301d5004600030200d202401c1c191186010480b607600a1000c4000c404901c015201d441c81c10101d41da4181c401034800030014410020080000019044c41e6842e8851030010440d034000114643c0e45180070524050324040da032804104e1641c0d4042c071a840c000c040e100b0001c9000007150501885201184aa15005504260410000403000318204082d00c2c084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 271650233 1250 271648983 271648999
    0x120e0d0e0f060a0804060b120703141c0c020f040501060c0305090a120506090c0f0a0e190c0c0203010f05010b03011a0f130302040c110717031e0c06070c11 68
    0x640005841024a480e1458200c800003d55044055000c05402e108600030032082c00001000000d01c609246003018000098118020034400038074000c11039070070405032000f01c601c818520010059100708e02e009460108040300401000c60520090691101c2d8040710200110f41c9014070290941c401e02100408220000418000c2035030f860031b4a0014080301504d141140d0500d103003003642d802c1c09440320300c441d2003603110308992440c010421548280e0040c0c01c5017081403525505070800007001e442002c3d000ca034904031074100c10301c0e4441c1446d642c1082d0750b0410000214010705007100c2c048a207860110f410000144581004031044a0464254001142c0f1a12941c19800264000d20205a4051030300151036008a0749844c40082568001c5608100d545840c80c030a846c0da8003002c158220607000000100401c5902d00d014900c2110f007402503070b140c0700c00c5403d411180115200140300e028004540d064142c0010400c00c1c0e80305110381020a0b82d1511a00c0341c2040740e80c030305823491040c080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 271651483 1250 271650233 271650257
    0x8150301053718031e020309010f03020903060f0703060f080d0e030a081c0c021f020a0e060f0a03060b0f090f040f0e0d0806010c0206160201020a020a08010c120e0d 72
    0x314100c00c1e0404002c41c0304010001c048402c401080c01c50303050030750000d00c540ca040d031021400351000c0c0a842045800440ca46010301c40191612320300c152002050581c2440f1600382ea890600550f4440c080185e1b0b11121894802000b5045401982225480c4034508801f8443c20a0015940201e40018181351800c101080c001074036015000c02c00038003ca8001c90307001e6000c26075550740c4a000368030b103a0070b010010f4200d80407642e520596031451902d1000d4008010301d1105a4020924290b5901d00344450440410215217180d01c440d4602c1c007a0b8100151900c8034603410301c41e0002a00850301c503980b4200c0d00003c119400d00070b00340000d2040c0703c44000b6040540d43c030740c000c442c211948070061112601c115a0f007601c0e10700c1104110089041940060380961140080e598101e40c0244000d06058040345d0100e104000c44c54103e0552003400302100140c1d480860403001407108100215000f011030800504814000002001040c2410341030060320f0008100407000203c3d43c0303420a501c1c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 271652733 1250 271651483 271651561
    0x6020607090825030c0803190503150f0310020f0702090907080a0314120106020307021002010b0604091e1805010c090e0a0b041b020102040509011a03130f0c060815030105 75
    0x502a13200424040c1054400564910048054026003c625148143c8030b20700481c181c40904c01200c0d8607154500304454005c00e4a8131410550081d60007070121401c80010242800032a44a082c032070f42d6120001c281401145402010a544030441101a00c0c0c03440c58010f20030360351070061030010203011081002d14a01160f8000381c0d6207402018214007075a584d1050080c6d1240c0c0700d0764040c6c1c012550b42d004401ca850050040c01075445000e42550b141a02c1c1000d00380c0141020300e10280380040c05568054507181c0c600400350a080d6048100704021440d141c810f00315040468800300f0b00c80784000401409080c43c909a41c011000040412114003040001e002403d0080364803031040c214040103050b41d0750550203803058680c10764039640320b0f076240d4945618160f1482c021240c44101040020343e04500082d001b4240740c4500003a080d903205036030b1080015000f54205000240805007002017040703080007694034103074080c1c000b045242000800b091400b8002801c00404222102110000719 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 271653983 1250 271652733 271652803
    0x91005040e211c0606171f06110f0a06060e011202010807050d090209040c060306081c0c2d06180201090509090f0708010b03061b0703080601030608030c0106060206070908 75
    0x81195108000b0507481d40c0001c2d2105540311103000034000f0705400107e001d940d1a8182014140d0034118a407a286003001c101c4a402032114401d54078090b02d04040b4064204101c0c40c25064440c1c00c01040305402c004003113112143c1648074011000e5183c0400c5c002d40d03044509541c011100f40350007980c45132030481c0308000d09003054009401245100410090000042d03800050362403a603410b0242640c3c0303481d8036072748084e401d0840c810705400503c90788a80d4007030351144030030512031010b2080c0c01c0b5001101d11140308104250f0b8180c034003402403c5081005502c02c02c14082140f0f43d80701060721741758000811011540c0181d030b014890000206040f83c2003080b1142540c0f43e20000c68494075141d090090107482d0780e0410f103000744a0080071609019030404c3e00310507082e04040107418015592001c0b10f0940303001d01980c0c141580c0d00800702d0944000c2c802464680c1c840400804c00a29200c002450700380000e254104004801d54103106840300414040d0001c011130000f080e2464902000000d94 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 271655233 1250 271653983 271654027
    0xa11040e1f030f030c06062402011d100504140a0303060f0e25021c0c050606060306100e0109030804031a0c04080705060d0b180f010b031513060302091005040e21 71
    0x240601c0b852380c4001c0d8165030b5029400c9a116402804040803406c1004070741a00e18101c1c0405410025658411180b96404180e0160244050740300d8000d4508540d42040301d1290190002a242e54081c040b000030802c00d00010541c0c0030a5a21914061808441e01d00c1c0744801c140c84289030805000c0030510800a41588900320f41030600d00100418010344504d1030190119060300416002840c2c40c1b800c078060f80d00c5418007801243c1e01101380071044503003500150800703040c4100c114011021403100b2010340702851251450b01010140c52449183d904d400a0a107e20550204018003105d080855460200e9505031401070300c03803a0140c0110003604100c085180c101c0800a801ea14500c001980507004000c0895003550a90b01da04c07000010b88000c480c910f43c1010100e03203c1c4881e0402010341681440501e030006805500c036400202420700c11750359480400300303421050142d40750912501c8001440340008040d000e540c6242c05042d80c419454154510201140246240a140b01c01c4684 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 271656483 1250 271655233 271655249
    0x302010e0102160219080607050c15010f030506150604050d0c03060f0504020a170303042405041202100e0c060f0705010f06180506030a0b0a11040e1f030f030c0606 72
    0x16440b0032450602d05110003e0b090744076071100681e20481c003a020030b04105682c42c51015103000d995100c8103840560102015822911400348983d0b008070021100501810290410740a114078508001d0305e4402c024084e0642c2c0e03903642000038031a035269011039044031819a1f042340b041c40c803410f04241a540c2a84043d01d0340b8140022803560000c0340d03222511842c402c076042180e06807104042a946c00c0b100081c45001c1e84208082004540c61400c0e0384510301c03100350043c82e01652101c858096032415a42201c40025014121020f150140201c200c160b40801080140e42c10f110b0303403203540701d910030800b5005030030009500c04070444403400c5508064001000b0f01402d00052403480082400d40300300309010f80d040400c08119042c13406041e010f8013004005042c0035020781c641c940f114030050165035030503540746400c0c0d0080a1a902400c0100354142d00c0304140c3c9406039030041c0c0a160100d4504044a05130002e200003a4520300058919800d403412220525540c0380c00310080126400c0010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 271657733 1250 271656483 271656487
    0xd030f020f0619111206091005030d0309290415020c1b09010504020c0303180c04060e040b07020313091a040623030c13090501020712020d0206160e010c0302010e0102 73
    0xc8081110300c21490101c1c90a80f00300140c045924092009002d800c80441090360900007240b030310724250b4202900031031454004a0425981c0c00000d28100c00032181c000465202c2c0c03a094188403101c40e0700c00380e4100610001e26040140f4885846181c00100000c0084000062104000c0b049606036034250900c08100d84810361302441078440201c0c1210650b00c07807178403400089851301709402500c15000e981401541182c0701c0342200d20300c01410003a241d141f8410300b041c1c5810766469000d20402007020b24044071940c01d05d130601e0319203903074024103078010340d0300c200604602d00d41114074207004c8074451900041e1440c910107038800f402e5010178000e68003034140007010440340480103511020103a00c03048007035030f0000700c818144c990041b0951244c0c08841b008044030f08000b660808501c00d48144001131804e09166904014080283c00c90801039000719039550426804100c2c00d138100403241e116014118919100a2003402000242810000b045c40203d0415000b50000d50b8030302c0191000799 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 271658983 1250 271657733 271657741
    0x8090316110918070602280201030b13020d0b0402030403020604020907110303160f02070819080705010e0f0f0c031e0a0b010b0306040b0402070b07050708070b0c180f0d030f020f06 79
    0x280300c3c080750080d58841c3e40600a03001840700c0c0001071119149120520202c818003001484030494030b044101a41455122425850640d4071100844191f0b00030210044c0c980c0107502c40740e0b048810498406010354410403e002c0425000900706500581c11038030700d00c0da5507410208030f4007450761020442240c800070003480004070a4012540c86281ca039560311022201c6030340202ea4445140c416400c103508450284004070481c0d6600940705800307000303003500d820140e40d00d10342143c00c8000c802800b40c000c0048899010418010310344001309060041c00002c0c842c4000986400c100c00001100394204500d000605d6000d20807a059542c000713030b5081d0a0341c6e40f00c84030f000d030750302c1100c0b039910803407410001044914092098540040e003200c19600c0c550350350070091300d407a8031035103060380d403001d092224000041c4407042c1603100702001d18019440301c10160b00500000441d02ca128403800c17003090191040d07250b0642100d42c042d05440d0a88555002060680c10130218414034141401000108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 271660233 1250 271658983 271659001
    0x6041404111b06071b170a020a05070b0a08060901080c0d0f0f11090a09110609030a080c011e0603031d01050409180209070806091302030c0a18060501080903161109 72
    0x30f58070442c0603444050110004640d08425003a41400c010103200c02c0c0030400c2d0288410b90003034488550b4034012114009455154503141c0305041d07114052111001910b4083d40e030340480c6468100c01d0a807500b0303c040d410000010388071413034141c407240140c110300c80304003c3c8482090624138403908140043d880c024030341003c40200300140c0c03555004040410100748642824400d4000654019040354102e034040d0302001055406208010361502c1500c84910229010100800501e40a01c000094000c5032446504020b5420041028014074000303040020a0f0050400d0050103d40c0c86001c00c401c8102006940d64000c90b00a54901d034a0b1855101200c0894101d04401c03500859031041503070b5601e4000c540300300c000c44045401c0308920002c9007130300852403164540c0700c2c40201a60808050704001c101502071942c000da0b1031800d900c010080240d0030380708081c080d040c00c1c80e082190340382c0032100ea42d03039101d40c1ca003001d50001041707828014084907000c05400341900074040303140d07400c0601d40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 271661483 1250 271660233 271660243
    0xf031112090d09061b11060c031c060503070302090115110607050d050c0307091203020f0615011e0207050d0503040302030102160b10030c17030c07180b06041404111b 73
    0x148021652500c3c001c581e840c01020007071081d6964640e0b0004041d0b02e81d0f280c440545a00007807680103002804400300e08002800948601300070704002c83e0150310f038041100e050707c1c0141d0015009801140c2c092001d40c50b0300d40007505503030495030b40822005070b002c800c8641504101c0c080d41c0d980100c1050141e0070750f00400801c3d52503003110080c040758072040211407261105442c00c6012921a0004000c0ca0f107245400842440c00381c01502c1008d030031200494100030080f40c001c0b41ea00c501c15981c0825680007200652744041d003850828038465032150180d42d680060140070720880101500c541001010802c039405143d028000b9134449403901c201c20b145044040003100e40000e1000000c0a506985c0c918030b0450b0380006500346550324080580c92108d4110302624005e000410a60040302d80c00c00428008014420719000100b021101102c00c903020181518464402040308004055100f80444880c0e82c0469000540d51101d1032019020f128940007441005540f80018030386034800320b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 271662733 1250 271661483 271661503
    0x25020c040b060f0403020907110d09060f02060f012102060403151d0a06090201090305010911100e0303030c0a05041d0405010b0a03081c061e0f0e06010f03111209 71
    0x1820710190000408202c66405a9245660580001c0c4410009454000181ea070484040e040c801c000c0404c1d420958201405000c00c60081142a801003000f1030744501c0b282141c074541e102070040c2c1d0521440c01c1a6400040c807a504400083d00c0b810703054200b4500300c010240f6402040c896865640380703889400803541441145019240003c0c85c44e103170596046c0c0090052401014140300c90556039400700520640f1020390400500407808000a0001d00c80c41045038040c2d100066403030038030410841440d0011820008000c070081c1c40003020303207001041c4da4016643e40c080a490b4414000c08540500642e03118805c2a801c882c44511101c1d5482e00c41c0f40980d0041001340308800b008014014048664400102108010014841d041e8588030b041c2600201406011a074181d0b58031507030903000810381c5034540d0400300000800151020490348001440290717240071142c1f50840010f0140002da0f0300f85401d050316055016282d0034004105c0d050004e0441d001d5005013040b69003e030340d400d4061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 271663983 1250 271662733 271662739
    0x5012a030e03030408062508040f1a010603050906090102130e04061b051b07031101110c0301050702010e0c041406013006030308090c060405060a050f07050322060203040e25020c 78
    0x1424a5600d044615092014070141e850300b59230b644450341c680c1d070608120007040d9030404219030003c81c0b480c020b482d010f00070326040e6000300e03450409441c0e1905201c0050481300c21a1b01c100700c507001c2d451291500b003007110414107082a45603201e051200140c101101d090144500c403d1800b40042d400c0000341031061110811482e4442e400f26a80f0b54400785800090869004400305804540c0329045108a84810400b0f980039840b05601203401c3d03038029a01c00c80940d448a01210002030b0800680340c60740030440e0706000c018480c4400d00f04440010f48000e04008200e071114000100c0340303d98043c7c8134190234410030074200a108601c01801c9a00080f800981d040c008200b102d10001a40510500000c21075841d0a281100b000166030002c0740d4141805828080c081c150809074000d0007141d801113002e540d079003040f1503104107a840320f90303030f820407041c0301d0b600c103010541d40002554240c402540c00902070b91070710007072052048500841c4001c500141ca50b47c603006980072603458218001a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 271665233 1250 271663983 271664011
    0x41d101a09040e25080a1e05011506021b27040203150c071203151710150e07022b11030309010603030f0c02010e1e150901020705012a030e0303040806 66
    0x81d22480343c0380c00d02e40c02c0113402002a40c041f0002484841e401d120094810000040c0f0b22043c07a035100841c80b400c1d13000c40d004d6000400450810061400070f0701c5d0150044503005699803c00132034107181003000c60120240000325000078115281044828543c904540801000b45401c00a110b403a83c0030799011075901115000d4054401c0c081d0081c44558503a4103d0003161504101d1410203001d003a805920540c4589004034007918414400c0f00050071900720320842c41c504003984460680c001602890844d403084644494440400c0b4002d00960521882241d04030034406041314011002e40e1070720b13031a00000041c8005402c0550040e41101d110791110840914079020648000d1010340010b0f004c203092150707000711840d01013100001d074030301d505a400404401c0b001150924442071820040d04200040e1940340d50780401078000107100900e00842e00c1d92460781611085100540da03890b1808200e2100d1040501804400401c100b019003240c1c4c8960b55007000e10394801042e11500240003035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 271666483 1250 271665233 271665239
    0x1838120103050d080402031c03110f090a0501080402090a0e0703060501180f0c090323010612140109020f0f010905030102030907091a030303010b1b03041d101a09040e25 74
    0x3808014485c40e00240941506100a1140e00c2d4201ca80b000a4080503924041c0a01c6821038201400742c080480c00080e07103d80d0f085050160100460b080581030240e54010840141d036202903869100c6030403030f0b0200d488101c00e082c0c4c920b0088243c000030040d9060100100b25803110303945031003814100c00c9040c4504c44014482c2011114448105c4000a403900820701c04107080580e0440c120800d01d840c0020128001da03070701d0071289140c0100301d00c0d0740b402004005100484ca406140e01c10314000070840c00340250f000070800d18450850600459401980700d1140c0e002d201d04000621010b00255502e00e010b500c0366407590a41d001c0c200000b440c02c2000b803004e03029040c100b030300745030f020340110f1031a400d00c0c1d0400015042602000081000c0122800f44502c00344003902c020491041e08500c1c0310610070200c0d806070310080440d0364540e48400104219501e0607200460700030b4244a00d5502c2001c24045005000ca10284080e50300c52026032003214822918200c03080303200500c5101075151 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 271667733 1250 271666483 271666487
    0x40311010e0a03030e0f010e0306040b06152b090c03111201020301030809040509070b0703020105010f060206100501110c1504080f190308130b070806011838120103050d 74
    0x481804044c002654804040c0407509000181c24951441410184003018084000070702d020000c450031900b0304124400d00545051501c0b2946284403440700031818081240b507030201d541010306001400003403002190f20102d9059104d00301080c2c026030f4254071581c50b810a801000e4008007198003a240050030314400c014103209980c1605e5100001c6441c10450404104c06050081d240d03922034000c03504002000c1c0c04a000034140e4620a800200f86903141c64030074080203846030b1025003590800c604011004040c1c24168058800c2402d02860300082100028a48103103101c0ba541c00419580060682c240c0c00c101501c2286c6140341182e0010000c060481e482d209041c001c94200c8201c9440d20001a0040440581c0010008103803e100501030300c2e8050311210583d9818080f84010040c40a1541c0c498400a101c0c80340c418082c128a183c40c9051190181000e0f164054406021000800020b0142c00c1c0003071800031a00342d51550070f00300343c0c94082142848102c403684a50003024109074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 271668983 1250 271667733 271667749
    0xc11070605160b060a05091e01050f09071d1203070c050109050607060c020a0f030e0a0806060a09152c010603110406030c02010e160303120e030a050a0e06040311010e 73
    0x6074200702c081101d06540e0380702001d41101500d01640520050404100c0e525414001c80c030440e003190103d80c0e010300160180b1441c0606030440d900900c159013000a50f91101c0d95407641002c1180b800688012450041c00548003032381190690058071100c212009040020250074031a0103100c4601c49141d0790b00044d0351060700f0f403040390341040c0140310b081c02049460340a4400d058003401030340c7d00c150196880c1e49041e5903103d800c03404201c05174501e070a14104070700090040c002c608000d14250400ca00000e258001c20f21941c7d14040d281c40d0954030610390303564024000d0494440c02491260071300da08010107910109206180d244100000560034842c1c0a4000b40341d140005451a003414410118091702c1d0762000b0909640d03ca2105409206042040d0340b1078400c043d0000e01034a085260042226001200000704181031000418082e2008400c42d0380c0c1c41e08a0501541c1e44034000c0042d26540501c494035540190b01143c00014803032074010030004804240d80f2100884001c00c10030600d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 271670233 1250 271668983 271668997
    0x501110c0a03150204030c030c080f0f12090a05030d021f1a010e0103230601020f01090507051011010204080606041d0c060d060b03040809012c1009090c11070605 71
    0x150302041c00c00c041022803103001c2a120001d60050316040d02ca444014000025502c00c03240212040410000d50005014401c90180000040c004610003141c1c030650740c003100c03a48000c42d0000069410700d5581c884401c0e00040c41c000c3c0503501181e00d80c42c0081d4442c1c403156481604d4814004525000b00768912513007540d89032a0814000000040b00111031026010405505040d074840d4000100c6180360150a0204001041842c0701c1c40c0010009080c40c001e5943e20340c1c0c07a8105400308000034404680b40040d41c1d816a50303000c42442e54641102c0e02112080c000385d40e9480080c0208214001148083c41160180d5082c0100307550800414103c0c0d440030f10b0103680e50403a800c000c101d480d00700005c20a252900c18081070040d01c2c1c40341c600065000303840c00c0343d402c0d10019095a4075600b012001022520246800046401c0e104050303002c2251940481d1060030f904030301e0f080b806c2c007800c209405004a00010410300e01d40704806060800c401005100e030b48500c4000203201c40c840c00c200c2d009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 271671483 1250 271670233 271670239
    0x902180403020a150b062701050a05120a060b13030b070903120807140a0804111909020a14181302031b090607050f10050a11040b0904061e0501110c 65
    0x200f80d0545a200021420010341020340380c03920240482c42da50000a0312402d141004640b120a5038040d0066110361300c1c80041d0305210f0300740508034266410206440c1c280843c0d0000d40c80f6640c0e8910414000e2541d900002c010380d5010864101c2000c0301c00000d030503284540a12400764586000580f8000784503c001028034105140308119684240181504085d250914038800b540c821400d009075004190036100160b16002000103014620003003504054042e5603a00ca100c404c0c01351000311191901481130320940000381c03421494460502017680a0b5202c555503114080c001003031880d002c581c00315600c900208296480d1056461003100d000710301500f0440c454080c04e80c0810900d030010000c20f41c1c03201003846028041001440711100008070300c0045c00030841440702e001c084440140c55044031906d800004001500c1c11000c41c1c0940710450a25503c96400500060240013283c0000400101808400780d40340980b41c035210543c1e00c01d885003241006c00034802980d8100380c06005034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 271672733 1250 271671483 271671493
    0x70804080c06070b070c06090b070c030e0402041d190203190b0f060a030c11070b0a0206010602070e0f1510080115021b0f0a09050c040611010c08190204051201090218040302 76
    0x171400c0d001d880d0305143d945c0305001c003140140a5450320100710104694541c040f540f102003990805038001c242c1e2100540444045040608240d15092000c00035103c0c01e031007500920208130541150b04400d0404203142406655900e070055201c200d038100c00d030507011800d0503c0c1a82503d4501600d49050000f4081d0a150504070328140031000342900d03220800038441c00b07842449800304148007410103408445541c03907a502d1035240c000d140600517030003c0110b40010b8070600c440440c050042d0740106105e11180459103c2c46050b41c40303610194030007036200d0302d0000c0c2d100e9400c0d04096858100c070280f02d0300f102400c400840580e218002d0304003200c901a0f403440388100c1c91420b0840301c000244040c140709404c544400e540e0040343d4056414070340da40c1020808204060303001c110220510b1114000780462a101c43c0042d10b0902d01034001d2502c1c11070400f641c81003189a9050320002c1500600c0034041c0d042000106008201c900380907805581640e40c01c60642c00f408402d580074a5055000344 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 271673983 1250 271672733 271672741
    0xf0306050c03060d17041e060e12060103030513180b0a0501030b150d090212010501051009030b0f04030203090406030c050405010b121f0f03140d0905010c0813030206070804080c06070b 81
    0xc1c060396070000380c12044005c18000450964003019a000380444c040008170421810448040c162001407401644540c280d406401c096120110b2010f0440354182851926920b0201c0502c0b41d4480d29045102005403402090320320b961107811a000302034065031300306140e036121b00c0110709440c1c40035081900000c400721103107003000990b0010201c001034500002529505540080c2c0861092201404107a4417036006012a2070b00c00720307503403000680b8140b01141307a1a41d0348600d001c2c0d000030f003186031600070a000101494000c0c001c0324103540c401041048565200c0c504401224000d0080c0303400746103030000104035140d15500b158450040391200b0740050f40c070184c118240100301180d8983c01c0b13803445000034060418589407809107128003582c504528049812500d4117594000d40c100708507159404100c0d42e41c00604042070301c0d400501c22a6106412074114010f2a0b13140c0c03000750002b00c00031f4290140322000020b0020b03900b8090030b5681c0d500c00c0e0801c0010341c3c02441400b401c03a4020b00086 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 271675233 1250 271673983 271673993
    0x40f03030f0b15070507030803040f0b07020c0109090507021203070527060418060e1602010c0e0a1401020f12070309350109060f0b0a081506090903040f0f0306050c03060d 75
    0x2138450903202e0000c6600e40360700d075900c00c485900300781c41c12642e1502084240041145003e212035001da1944020a588140800001c15a030764511039500500e07601c0f004101151300c240402c104404803601003d80d40c0c10038002c010701680c07010500c00c919815110f1143d484403040740c0811440400144160300341400e0000a05011140c9190a400141c1e6001c001480c1d03d00a107140b44522030701a2602c00c000b0035650064251074200c1d119004101510305603140319960303042c0003402d403550080704920189040c0b005038075140100803030b4100345c424424100103814080000301b5819109a540c1c000d9143e0354031202820104170ba4040f001c001c400030354081d1210020b2800404036041038000700c1c0e1821642c40317100854408411080702d20b0303181c5450742c0041c01c28050680080100b84000c1404040041c00000b03020070180540c1d105820703140106c1c00d0b51808200340c402070107010410b01903032030390f405421003001550310007260101c1c01c090010700900380c66016a881420080c001d111005181d03615 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 271676483 1250 271675233 271675237
    0xa0803070804140d0501090302030403060f05040528050f06071403010315020703030222051f05090d0812100f0e010e0403182c0a0501030203031801030b09040f03030f0b15 75
    0x1a44c22421440050000c034100340101d0004034041d802642d981c03420f605001090b504900c807045081410f1400b4040018070020302c01d00c0000c481480303448e09192050075421704200410b0f010302135218a146803140d00401090050181c00c05032a03400070703070303100c41103180300350009101c00740c4407810000312aa0b05040d51740040103905c0c070911b4010301d00460924640c8507400346d0400d103000395204040601060406c2c082180200c489400700510b407000725800100148148080d00d4041d08000440c207041110460a17203110445681c40004180340070f58080d03070f001c0110702c51100d4040380524002040c0b500800420306940180c04060a213030b58a071400d45802c2611403101c91205000b450004140301414503004084150001c0c0041031980079a074a00c40c4900506403092081c908801000140da0000071502c48030384101243c40e14110220060340101650080d90b908156001c081004000420440140561090310104000041c65903032300200d5149c2c041c6940c104260030700b811010860000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 271677733 1250 271676483 271676519
    0x206041106120702010506010f031e09080d02070302060a0c03060302090606030601090b0301080304031b0803030708040804030510050f101401051b030c1f020304110607020f1e0a0803070804 83
    0x300040c500741e0400302c0201d98540440c0c00500503503682041c0a00b5603400300d80340680c46414541401030301c03070401075203003205102d24040b08159034910b0603d040001d0b40041e1400c0c02d0742681c00315142c1000e402c0283d00e40204a0f094403030706241100f52140b55000344581c2c02681c0e0050321107180c9030345880c1881312581c00070704160305204a50400050b078a0004001354041e20745080515212403661034850081c0c00650f0900c2400c2c4000c140c03c1c84840310000c1980d034042c000786004040c07511a17080401c918840c682024215001c0c230180c21641240507003000d40144504881032440303a8414004405c2d584a5000d00b003800b46005510440300d40c0301e40301404201200e02d2140e00e204022032000b13461584220082031441d0020b00c0f41003810301c40340614802e0f00c0c0615000354074526050395184260124000b40e81d10503640450410103645a24420060280002c1d15102c0d5192031055141199a500b4402511070310300b145001c61458008402c2d1488190b104a0050810342070007101485030203224 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 271678983 1250 271677733 271677739
    0x10506090310050709141206130f12031e0b031b04060801060f06230715061d011a2a150f0405070b0f070605041b080c0301060e0702060411 61
    0x42c4020044641c18410720703015400e01d88821010624041c0840684040c80e1202803048007404c28a0368284004a047c56014800714940b0311042114503220880c21203606014041c0389141a150250395003584c8001c0c40344010000c80d11502700707e0200300341034078000b4508607019001084e4001ca00d414009021800e290001d0000c1800342d240d03094142110080c2d44464a031900c031540070000b55801949046980c01080d1824a0700b01080180c80c1d907900c144107004180390803c40e00100a6030090740600094030590641c01c00488500403900c6410f170081c0280644c281c459915480099041030132034101800341103080c031703c60320b0b010001401c0190004058803580503d01400216660013014540b040004003011056810b00e824107624055454001c10181c42040180075a600480000d484045600200c042440c8d0303a14a0218022a402111441002049000899140c2000c20402c50703040c0164004c00c20a56a607c0c4825207074410794a030b0015030004400718020900302a08080c05240c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 271680233 1250 271678983 271678993
    0x5010b041d18150a14100e060402040b1b011b020c0d08070b04081c0c08041401060b04080c0909060c0f0c0a021c030f0c03080a0f0b1201051b120105060903 68
    0xd081d0240c10300e401c5590301d8881203941c2d420802400c440340300d400385c10003903010ba284030f07403414152001c001d001e54003134030381101600400110540c1da030781c04842c0030f002004030b856140c0908400315195050400c01000d0710b542088102464220140c40c0e41500340510f074010300c1c942d202d000503c08110498901520000c1c810081500810303504ea5455010354031829a00b40e0300c80c030001c207203c2a0200f80b50310500e01401e0a94a1611662200610b0f0700981c11500758404402d440781c0c0c1e2401010340f03074000000444041400610002c010540c104101402c0c1c0d21240103030707910201e05803034003422600c0c0c0d4214482802680241d00c03c0d04007a0149102c1c07042198600d08058001812103003a560800482104280c0c10100b015803100d181c2000712190300381001011f0079541c019105101c018a10800c1c250703255400240c2400981010020b200c0c0030782000400b18070b07070915034040c1404503008460714103403e4900c4944002d1030205c0315003840d011980e410a901703220030030049a01c45a4415414418 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 271681483 1250 271680233 271680271
    0x4140c070312090b0f09070b0a1412090c10090b03011715040f0c060e0f240f07031b03020a033915020f040510021e010b0405010b041d 59
    0xb20300c105800d450003207191100b245003004032003501042c010b00070003954100c480e00700200503450095850103c0e0b0f074289188000f8090421a6940c000c42c501c1603d020140810b101200b1004a2032242140090fa500204043c03800303400c0d501d00709140b2134a1700c00503003003004021022940000340240100c1c2d009443c410003070003403085050700701603405582800103074901c41c080191614020000b02100d0501a15204013078000614202d104e0200900801881a81d829509940d05441900ca81c5c0c42da0320700d85555500000c1ca02030340100800310301140c0c0203050300d004064000700985051340e159004045440140d41d084401688660400b1004200700a424040c04500031401e81ea410b5100301e02c09030380307056060904c1d694041c03c000d040036520400800d1602c46550007141c040d180144c0e000070030409980c500b00c2c03a00f0308a103001c0454482c0c0c2020042903e2040d0421070050204590510041c0d80f1410186000d108030311a0030042c4400749032038100d1074100c0b80f03019481005c0080310700440c0c80c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 271682733 1250 271681483 271681517
    0x9060f2901020a05100605190308090f03070906060509030f120313060612060e01050f060d0803190504080a0201060b030c041401020c040f0603031710060c11210c04140c0703 76
    0x8204000000c000386c0310b000c10b000714103128000b030005440c46030300c106070146180c64002c454811800424022120450306214a44041181200500b0910b200b0000f042d99450014116003015404610a024204800c5402000062485d0014076115078040c5035880380340031aa990b07210b1b04811102030303850740c800045416107000e20004190180d000800d860078624401801c40380c00130843d04505c0c211070300f4410a0380350701c40401c82072503101c0d00c015681e445035030382680217800c50800c94404a0030074042100304200d10001c0c050030002ca80082c800d082e2600040581400304a41d6400201001d02081044005040410146010600554428203101c8000c10f0540d074849207035142094440c14104105039101c116240f08048180b25020b0390309107840807251040240c4211820400019000340600c0231880e482c0420107002401007480d185804002c190011180358402c400f4010341c10705101604040c05100130700e0032040c0b05c414450b6103403629441150401c40d000c0c1c1c1000582034030b92100e00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 271683983 1250 271682733 271682743
    0x20c030114010504051b0a0f020709020304110a06020307030507020d061d0105090c03030405060d020a1413090b090f06010807051c051012030203040605090409050303070309060f2901020a05 83
    0x71980c11400c0c9010740c1803009100075980050419580e810900a502c9450351009040e54203264043c80c151104041810049242c00101e420140401c0c1c8004107000802c100e0990000c120b43c01600c0c140300c11035440c3c400780e0702d82c0146840075002c15000c010403001440c00d910f002e140240314500026101c0c2d000001c04016110100d00754849a54030b4060204540d4100725010341d020f0100c00541c900780c145008216140510202507004c8ca4020450442490042c07030481d0161540507801c940320400a00300308045000741c425005101d286c030f19940d48030f04080841e14480d40007101c10a8464447c41d004441960008108400304001805443d44c40101840742c0240d0740c000050100e443c4c180103c3e00070a03a8400c8d0300c05030700d40403c3d018110010342c010058404484103414030070b8440c0010400b10740036100c3c60f003005203207000000c20410229059800680803901500040107118044101c040403a4050390340d001560b6002e4450281c0e143d0080d000440c0288184140d0321011040d44d40c0c64070b01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 271685233 1250 271683983 271684001
    0x9040207150c1209021804060b10050702091605032811120f0106080106050904060306020403030201020703080a0e0a0b06060d021215031f090f02060f040f121110020c0301 75
    0x3540c2c0311600310200c0c40d0f00031610181007000b00401c000032071465001482c0d610f00c01ca500001c81306c880780045c040c84481e9000780080c5201030403400740c00c28203000003001944054000c074401c12109000c241d00b98586075281800103640c2e1206480c40e00c5580c3e80d09144440b4880c034651031a0b03811403800c401c800f203002d601e4070340481790061030b1143c100019400382d40764020141103100c107000d0010483c5580c0400203604407210f6082a9913100394070000300e0040c00454102030303c6640009000000c0690550042c44018060ba4a82c0e01e02c7e00c841c5c054005903584e04407500c0c800d40c4820b4040b03010039a0420010381017000200000e20309241021600d0a0340c1009007044081c2d0884401c0040c81c101c222005001800300314050507482e20503185044d1656490040c00c0701040d95401e01d4010007401c1c0502d0741400c1d40042089444052401c690055603100c0d010300e641c040c00e0390200041c164030b801030700184294010710607119510b4500034000c1c402e40524101e01142b1500c1c180c0d02c40c5460070701ca0907004e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 271686483 1250 271685233 271685273
    0x4080913020f18030c030a1b081204090506030c10050a0203041a0406170702060106030506030a020d05010506210c0d0206040b030f070e01020a0507050609060409060906090c110d030209040207 84
    0x441d080c80e00f0103800454040103d038041c1e000b004813100750b0b5a012400f00d21841e03100d0340d0180c3c494a1110300c83c41ea004903400c10410b5110358131000d400c2118090150003111640c00d802d11469036144241030b00c40c5c80c0e102c80c540c1c1241035180c1c1000c03843d000710058403168520388101d0f401d0a5450540c103140c0301c3c12001250b207a6034000344c1400465400030341c205090442d581490303440c0c109008000c0d40c03004144620130400d81c1c3e650204400b075405002a655894004100b585a242e02d414542d000f00b105680c0c141c800e04081080c41c4005840780c82150081c2c0c03400c3c015182e54031180d0140007000e01c841c201240e020004000c04211800c09070007a5001d09202c0441d10554030b05214007405440d5164002815580301c80d01d18400503900040e5802603d006490498580c07500300c01040c000d00494200d1040c135401d00e00c0229165040b0341c0f1580845001c0b40040c8010748410b0011343d44000ca803101440b036900042d407042c00f450701940040000200c0508010720304403250322140521041d004039456 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 271687733 1250 271686483 271686487
    0x180f0302030105010b03040c0513020d020c0c0901120c2904030b060907082a13030b041b030b01090510030204020403151103070210051e16080106030203010e04080913020f 75
    0x20640c182403040354003500c0d010040d9481c500309921111030044991042505c02e0080c1000381f4000416501a9400b210b200c080a40d100c0b0f054060302c0392620340321b045450003000301e1000040d03040240751040f061650014002d0074610b003403013954640c03c03c4402020303c40342c2c0509088255002442d00500040d80141d540c00e4590401c0b4041040c01807002e81070000f00543c5c041440091109940c0143c01d200c00c440d501c0c0e01101e070b60043d54003d80034800900315003c001c1c81c0d001040c40468159a03100d10720400c2d00c110740144d80200000134815030702001d0040307507100c40103000c02010f6501064001d11022812142030342c0d25070000e010399102d9001111004150f140440f070720020b40c01440d06804148070310908526104100a5541c400c94000300212911100818655a1b01500085800c80910200b0f80e1502e0724060090440400310b08080c006940700c00000350041c0320744280e038103039100b400242d0b07082d48603a00d81d0040382d0400a0300c0c603400002c080010012140d1440200044427011600320303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 271688983 1250 271687733 271687739
    0x131a040f0e06090a0c05010c0c0513090204020d0b01080a0212061c060908041410050901141204060b120303040506010b0d1e201606150b031f05031c0f180f 68
    0x17400004c4a03030b02050600a60b800b01100040d5248540010380d2820703642d0040590fa0000200c015061840b0065000362000900148002040e000481181000c0e2950364643e01c9140c0e00e50100e00c40e07003419000b40c04210002c16901c1c0707001d00752502201541d80e8a280810600c2d00c81c01c04139007460701d044031a01c00008040001d002c0040304140312502c2101c0c050034041c83d465006c4d0040c400c0b044211304000f03002050008100d651006d5840d00180d007801c2e00b405142c02e1500038002c00401c1c0030603104003061124a05180030001c2200c0c4196405400303020a41d107002c02c012203071b030800340402e82d00d02d13114048a81016903500700340e980c85054860104140700305400501c801c8038021105c0b082c4000c100b01200c80d4619154650390015807001000484140500c56540d05200c0c580003801c03004000020301207200d84c82d0703c40c218540c0301030300d1610b410b030b070348908240d41c070406500e03541c0901c205400203652490240c0715403000710000d03007058603445105540c07803d03920005030050141c04400020034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 271690233 1250 271688983 271688993
    0x102090a05010219080d061a0a090e09030d09080d02030a050105010917120a0311070302010c12020c0d0c03030e0a0506010e01080609060a1a0904080306131a040f0e06090a 75
    0x8880148003c2c000b4102c0c06003080b000d107210003035005003d80080c400084081c000151540000002c240080218000000300c40104036681d10580950f0f00240089078017140d616480343d1500d0281c030142e401189041184c44c000009042c0f030210580709204103001c0890400000d00055208041c000070014032036040400250444903590071a03812076034059902803d1410002d030301c1c1c0c4520901190a51100b0304044103c019201d180b800c0b42c40e003040451217104160f01500302e044641c040d0b03154035190104030700c00d043c220f000d00800f80c87c082c2e10200010281d85e00420a51448500a28000c03c0004403041081d1a000d42c0c0542210107030700c001c0042004030b2403101c00c207000d84068406040c05082c0b1031a800d0392110081d010b500a2036480c80340d5070b02505400300f001d0400901405c0b400321450541030042c0180c10444110340520080d400c41d98414034103114440360003182c030710b89400c2d105c044000c1c00002c09540c031501a280b079460300f605c84001d8040000a105561007801408000c0305072903c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 271691483 1250 271690233 271690249
    0xa06050112020a1e0302010e030a020301060807080c010e0d11010908010c02101407020a0308070306080d030207060b030610091a0405040b09070e070e010c0312060303021605030c0906090403051b010209 88
    0x488079004d0300190114041c054000c660000322502441e046520810340300010342407030042e0348020360648c42c0040004000101058900443d942c1609550040c440080150b80003000207100075480741c0a1803130000014400c0e105002c0b00714042c0b41440d0b0154031035881e2800c54081c41c401744091780c07088002e4050310001d030051041101d20080342581c941403504c00a5a5010b8035070000302800704240c0080d414a11940c03210b00100402011600419030301c2c14041c0081d40100380613070b600382c00c0c885518800e05001030342a000f80018018032a1740c44c07410725080c0040100f00f0500d10055a01d51280d15542d58600410b0b0040b4003034000c171000c80c10048020791130003000b60b1125130b42c410640c0800c01c41c10b030084030030b112404007070800d44c1d82c0084034501102c0c8001c03c19030005000e46001008000d06034000b59504030a4601d1140e502d101c0c5e1078000b007655401c2100c0c005503202119200190035030078000704143d0824868241642090301c00720710302002c0001c07400d0750034442e07502085907465440d060007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 271692733 1250 271691483 271691489
    0x70c03031107060309080409020717031e060316180b060d060e0f040309030f21020d03150f0b0705150f0412030b010e010305060f0d080301090b04020f0a08090a06050112020a 76
    0x4d08120b003a110341d441c011180928420591300c1503000c00c00e00c0a1007582032041540350b4040c0c1156582e40b802540014840c41e880c0b06401c0c840c030000c00040d940d401c000480881e4000311034031010140c2d182079082c9007641003803d8246102d40d2541a213a070301d601c840e0302038403145c0711040c000f1480d241000d20a01120b4001090100340c088a42d0901010982201c51041980d800603015400c103401410052200341c09482e8205010404004410601e03a01040018109003259001c1c013225240280d20002040c1034020b40300004000c01080204a60701002007450900c40c0c2c096a001d4101c60744041120a0300302c4615800265010801c010840000c201c8003440240d0f0804202282c0160300084c05200410201030516a80e10b000c54032075a0b44010764031003110000c040f00198009464080300640003840740c080c8650404020941901c1d0074003da41600c900200d51a050127510f0100b1108204054440103c500840184001007100c501440f8040c0520422030644440607105100d01c400c2268 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 271693983 1250 271692733 271692737
    0xf081605270f0a06050a05071a09060a15050307050613090c0210060902120f0a0908030a0b0a090b0603060d030e09150f040b0618030c120105071112041a070c0303110706 74
    0xa004d001c8130b83c010099440e15034091800e43d4070b82030309241402036508509405880848000100b180c00000003900901c5074186250500080d07801c0034424941090502610398140c210b10010303c05401e000c009803070440d01d0620381c0009180e44030055003c41d070150010400503001141031807090080b0b80194401498503d004510b400950781c2c0301c0409000140c094035417003002a01003901154540c104032038281e000001240d80b402c000040300018921501958025040c0344800100450184590403540401510242c515928a070412042c01e036820300c11024001d40ea1520142910b4403480c5071703c80c1d40d0000c2c260041040c0c4000300202440e808018600c1a8141001401151109020788803003a01c05c031201e040e03000f01540060300f0003402881d6030f5009295400ea10300ca611741500242c0c001c0e5510303280c03416101d0318242c0440e2207501140d50740301509020801081610000ca9450b0003007030301b003040c045c240802c0303685983c21640c1e56402a400125240144801da81090004200a00c0c0074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 271695233 1250 271693983 271693999
    0xb150a020604210504060e040905060c180a030819020f0d09051e0109090b0a0302031006090c05030103050d050307090e070804051b03070b0d0b0607120f0f081605270f 73
    0x110300004d0503032003240070300410001d50282c1c4000c0d68030b440e0860005294040180d542c07519007002a408142c000e0f4403680400f0744030210525240c240507034031741f0981e90000981d81ca801040d1080600800b1100080c03400c500c60703405a95402031080c00421000c120555a00004603c1d1404110661112158155186d20f650090000c503070381000c00c2d003003140d4104c200401c41070b1910780011000207403584060b405002d842e4403051910a10750110303003030310314104c0d00b041410701441044507640400d0000500c5c60303010b00c0101c0b001c1e600030340296601c50060f1034039405440d10b451590101d050142c900c400400c41020901081110500018440d98000150300c440100d000300065510b0b5024071510800b010b00244480004207207811540c1c0742040a4401ca0780d861180c540303018034101c84806180041e200000c0d50000600c1600e41d40385410195a13186201d8850b001d402044002181220f0103010003008581c0402108805100440482250220b0100004014012031074444000180324000e9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 271696483 1250 271695233 271695293
    0xf120a020306070f0e0f0301020c0d080118020405010c060917040b07050601170c012d050715060501271e03020906061905180307090504060c08010305100b150a020604 73
    0x8400717683d00d01548211095020032070450082402442040070701d035510b00480c2040801d03181c0018000c0d0484409071103d80135540544400000c80c01030740102800540c0400c4060045451a00f2010000d40184401d845e54003070000d83c80002da009034010303072100d0000318100e000e0020604c102401414041e030b050751095100c004068569410211085c1070048411030780a01d40411185a1600703400c0303441c841848000c0980250003900003660482d2064002c41051400078110f00600d01143c1c810b03103e1425221040440881d0080d103c114010740902510000651507500442000d50f08505d03089010030906600501c140003000910780c0e070056400300b0507103c8489481c002603003d214030b403a10139121a040b4440601e1020f4103640903a05125032800031400141e00c1d40f205010b5841400100280c001e030000507100a00d00344406001c039008107190b41340008068210100003a030003020320076100a030f00d1001030190000e1041d0320040c1e00a034204010824110707800b0301e9081c1104515801410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 271697733 1250 271696483 271696487
    0x51e090c0f0c071d0106031125150219080609130c0b0309070e0112030e09070c021c0302010612080a031802060c0115060e1c020f120a020306070f 64
    0x40050541210090005158505070141c0c505640190260030195880b013551804c4100202e029540800a002c0c024000051907a000b8417462002c000705c1c0b070401d030800704001f00b141c2c04143d100001094155217081c410340000d945a00b010303100140740d00300585400000e50840c48280c8211418410b100514051242d030780d440d60806503200e040781e41c0d86400080c3c0e48c603020014121640c4000da18010200500c100e4001c04035000090b07600b9102c0c1030100340c3e84c072100501250104031018002c1402c56544403a0b50500004036a440841820045150049540803039210040c080c5822001c21011000c50200341e070a000d0034008213005000c50f000181c3c681c95113003241c4640e00403001807507610f598800e100395500840d0080690014085511042c100ea1018060288245440070140c1c0780b120200300240a865800c140700c4c8043c100c4a00f11500b070140c09038403070444070140d1f80414480c0364140300303a444130031059102c0c0c000800b90400c6022441818a441c84c054104001d000c120110a65515 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 271698983 1250 271697733 271697749
    0xa0b0f0f0f06040f031416050906130e0f030c07140a12030c20030606060c1b030109050706020706020d0309110108070e0a06030b0a0806070203030f0414010501060801051e 75
    0x1401160702034075100c20300c8002041ca101e26413201441103a01c0000209108408610b51000c408035025180d61030788044c0941084000c46c000ca540c0407107001e0110300c81e810154100c09400030507000004412403000c603a10f10f03240710001d221200760310000308501d4002c0309000140040910243c0140344400d9600010150001d0740203480300580e0244255040c50b1113500144c42458000301419071505061110341d0010a044058138020322131b00d07020a1a90406000700c409000040c1c018001d642c05140450b80c0c14104c0345c250540c035648406184010800c00d100000041c00700d41c0061403000d240000182c1090301c201d100b04281841d28610310042900b090341c60510302c070240b070046485da40d41c03841900c1414520f040c16411041205003c205540c06600101ca10701e8220f500c0070310302c0e80e254015940c400040787c810b401604284007241a1086034203000d50800c4c4038611a4402da12100b1040f42111426030016001800c0c4100400c000d0070700401c008045a65038428070703a081c2650002c10010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 271700233 1250 271698983 271699009
    0xc01030f0e07211e05010e0a0215180a09050414010b061602130609060501020f03031e04030c080703021509030a0c110a0315050f0c0c06070810031a0a0b0f 68
    0xa001d40c9000c640d5041c43c080307002091140d01c403814a1210264400c55041c0301290720084841c0d40c80c3c0307036207210000c40c000780c000405036008000c203c0c5102461041401c54000540e0302403c55454243c4100542c0c41c1c0d440030010b482da20030009401d1419045c003680300820000c0b00381069150021101564460b14102c0b8501d580400007000003000300d20104414000048032584034030b20b806404030b14020140c10080c00c0718401d90031168140c40103040143c5912064484114894a8601161404081c04803e40c1d10500a052020000388161030f1280c0550105200710b006070822001c2404080d141c0c0e4004e034025030400d0040d800c200c2c80502c00303411400b084001426910a4205490080e50707505d00707090145030300c80c00e039503491218914402c01800b030903a1800d03081c400490000300240400130580e101400103c0080180740c607200000c1d00d02007c0940400c4808440d1200030011518104031026100e41c07040e01d4107076520300009128100e9030005000c80c800c0c0c0c03c02c000e4604950781d000300d402c41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 271701483 1250 271700233 271700249
    0x61609050402030c040503030c071701020a090510032004050a17030d0506030115092306130b010c06141501050a0203040905060406080a0804030c08010612030c11120c01030f0e07 78
    0xf80e07842e0b0f08104c100a000d02d41c0f0030755040c03200050310704030179501250361012180210b1004048002244080c2c2c280e01072806006e0010310105010049460a0480f0000145042c10001144030b0f45403881009004a881e26600d0010009401c104a05101e21a50300800a12825918a0001500c4551640319891041c1d51a64a079008210390340c1d03003984842c0700b1100c5000c8074080c0565440511024080b4841030350f102030340d410b0301b40f050b81440482013885200001c0c840500c84181c80e000000501080100da4100031082c072130400021080e11034040480307206104a02c0300d1034044440360000c90410800c0d81081400e100359525590000203450a8070300b00c4001040030b40c1c0355800304000344801c0c1d0000d480e500c0303203003505010301c07485400a005a80c02330f84001412034070384038000c0c00d0301c005100e20b8010003c0380580c0d00202c0c1c440c0d0710b801001880344c42071658a80d03101c4001115414a0350001a154110009001d05c80d80c1501c1104800e0b40086000d01805804008480e110b0720786108640d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 271702733 1250 271701483 271701487
    0x1060e0c07030e130e150103050c120709051e07030b0a090b0d05030f0c0d0f14070812240d050607081801020c0619050609060f12060f060102061609050402 68
    0x10070540200c030350044484004d030100c2c201d1100862000e02410119130190518040c0b80c00c4c10f907501c01e500d003100d8140c035040b40017001a56610014040300c01001b09401c3c08501888e02c0216a0300c0d46805000d000b040e041d408007440702414004d500303940700080d01d00000e040c80c000c407000c500e0b1150402141120014400010888114030203d0344048203000e0080060100081188400151202504500c54490100d51144248100c1621098450101c5001050150310403011560007035009203030580c45080d0342410000210a414150350040e075a00c1508a0039150070199039124088541c8959802c48010b0b500c07088640310144c44950160a040400c503c101c0014485481c0c84603441c1e5041c280b0f8021503941a045c40f025031a154103803011084500c051841030a4a80d02d4040d1500407000248008280e0b1035541c20006944200200b40d50480c0802d1001c055464060010f43c4c8520f0418140034400d01c0c0000009080c01c90050003580304440051050f030000380d008003c10142d58054038010307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 271703983 1250 271702733 271702747
    0x30100906050a2c01020c01020316021e100c030209130e010506010314010b0714030307030506030c010f200c030f071d010305060406020a0201020702150d1401060509041a061b0f01060e0c 81
    0x42c4c0a4401c05054400545c0000140b000b00f0690300a4891004d2080e0300740d4005c0204510304920300115200c0c0803009511038502840c440d4201e90005401c03c8940c05c0062421030103e02140300352a0003c070f02140f050390b0b42d065030382100f02809043d500541c246010813288030032082d6405504d01c1030040400c003000100380082003050746000c05c0000241e51040b82e842c0d2070081c0f00100504000c44203d80070b4055540f048a8550080300103414101070f50721000c0d2035040c00c00001c02e4514400c0800c40307040c810200c241045407020b11040507681d800380040c2c1082401d1114016a88600c00e484000510005004001140011944940240e4032074070250365001000c0c0124064022002301940c0440c09420341d0074118078041c01043c0707000700060700384040081d8404040b42d5681c24800c020100b86c007004030802920307143d404004d000b104084003500900044010400e1a08002000a0414448652180040c8041080811099150300240011814820400d107454070103000c0b00003580000c1148 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 271705233 1250 271703983 271704071
    0x30c0e01091403070f0803130501020102090a120c03020a0b0d110a05040e100803030f180c0306060d020a0305070b04031406310203010c050a03060509010530100906050a 74
    0x140c401170256601902c88a602e030850540ca941c0700098104c164002103400041a5006000b92807841900800008000780780000e00074134580319100881f040311000d01e02100607500c0005d0203014240d2801c0c450f8460044d00909800c85098105480c9506000e0102c003503403640c09030407101695904090350300240c48100600d01c0400661304011507901020081104c00100030340c21901c1400f491040008291301c0140c61512000801012901900804001140c03420084040c04401e032000e490b603030000b07a0f6600c4041c01c0003882c0d00211050351000504005000c6260f800b5051084544060046403c00c40c24a44604c261003a00d0300c0800010501c0b1071401d20510b07450401c054001d00248462064958010002c0d030103410a40b000c40c1c0303400800320f170341d041807c5254140d81018021a803d600094110840b102c404105051032000750462a6000d00f001d0125061f40e0213140f1011400381094500380055a10080c031201519203400c003410400e86041d08120b40000a5150720003001903c1201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 271706483 1250 271705233 271705243
    0x6010e03010905072102060f131205030d0f140411120f1b030d0801090504061b0804060e010b03120903030412080405030601090e1903090b13080c012105060f1f030c0e01091403 77
    0xac2c0c007404074050f400512102000816201800100802043c100700d41240121481c490780c4060810000001400068108140d5160600d00a0992500c43e000540c401d240030948050001e1507004802103c0d81c500708148011a0008128040d1000708142080280380c110140300e0031244540725008602844903643c412800406c080303200c0c0074030448808000e481100e080d00e01311780561505400e5101d41406210f00c940207000107002c0c2407000c80380401240c03030b07802150004d0380c140002c2200288004002d0150729115110b640501d4941d8600800c150424005a1021110600346040c11030124000304000e43c401c0c50346a580200720902d03003411a013041240e00842c100c65000981d280006d4414ae0300c101c206e03514030303003210b641103505801199000d280c0b424050495198012010070b40b4145d070045030703200c2400340501200800101c0061802403000013601900091401011001c03949400303200b481024a081038803107150200c000030f1682c842c522544420052007040ca001e03543d41402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 271707733 1250 271706483 271706489
    0x1401150203251a1005010203040f050904020613030c181b12090506092a03031213020301050403031b0f021906021309020a170708010e06010e03010905072102060f13 72
    0x40703480c3c40c020700c006001c0303115002c1c0e03140d1100c0700260600080c3ca610000840741a40c4500b1b0750060103502c0c180901907801390180c0200e0b44100140b2001014840c40e5101000440c0910001c01d0154540362022120414080c0034103035080c01d1520b01c540c0c07613002c00f40e0201c04602d10b180c018075042850641200500075040000c00d1805148140920101d0024104400e98494021003c810710180444ca400212180e9895090342080c0202c95104882041080d0b0000203011400544101c0c3c2e800a82140c1044070b04a02180d034602e603642181400c0040c000b0102d0060030501c3d0140110100603544441710803840c04403003082d42c5400c0402513590107888a8544040701120b00700c2d21007142c0d401075003044900d400014507460919100740356082c01c05024031065103401c400740e401e04a4442260100821181c14410913822454090320244107200002d07000710040c001803418819124240da01c15050b214a2a0640404070702699403801220801003e040d100e0307584551020160902c406503074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 271708983 1250 271707733 271707743
    0x601180306050714030f060609150a03050411040902030a02091008121905030c0904090f0b0f01150906081807080709060311010c080a0f02030d020d140115020325 71
    0x160000100003894000a0050103183c5481203065a051495002400304552118005081d00b0104100b8203080004080d40311001d4500b14480e071002640981951215040c00c0000c1c0d41d8030100020b1026002620071200c6084805010040b8545c0010796601281c680180c42244d1040110740c071010964800c400501541e4142c62004807809140d0145400c030180351007059408109848a052041c000c80c3e1245050b002918142a00101840020070038820304403880f070a99028000440c00081103148505000b0546042e158103028094000542c400c0032035083c0942000180b1100e0780142c00b07564044c0c4c03091100c56066660103281e5180c40724030340c401d041c00d00078103e0200300109642c01500030341c0d0244414a01c0010310000459035100c03031541c090301d2410244040c448807803250064108444003803044a080c52400000c42d02241c0c80840103100040e80d0718a1003c1d0041200c81d1240109040d00712035404200c01440139440b4494000c05004010013800d4810f800190a100003102d15000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 271710233 1250 271708983 271709027
    0xb0a0302131d0a051005130b0106110304030c14130501081e07120f1a0601120e100606020c01020705060a090513020d05040308010303081008030a110a06020d051b0f030705030601 78
    0x1900b1300907100c82c080c0c000500040c0c1050006543c2203500035081c0005a405203c440c0d9582c0b9106049460b04030011030b6075807034081044000007055103407080c000607100500c203040d0001400410001c206a0101c020f5541c241031000401004070f000c20020f0402c1e80702c1c80100d0411210321811418001a40c2008105101e81c2c0412414089000d000c01d542030308c00c02c2c0b458400d0125000113407100f181200c034980016105000c0340c0f485041c1d504400100b810300f0040390226483e503207000050f40c0c295000800140c2c8840c8443d4010f60341084981c0c01030009903082d501e0919202e90060905d105400780a0080110500040341d01c20380343c0c11100d140d840701d10200140d0a0901d0002c3c103801003807005400107403030040410700081c0146014401c450800004510740200f0510654000300312510400e014003a031903441c0f011400c140000c1902c01d80d010302c006a64a032142e201c040500c0750700803000150100f409070049054040c82201d401c1240750500a88999441004803071060613000e8000c400204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 271711483 1250 271710233 271710253
    0xa1409040c080f0a0207110f030c040905060712110405040b0102030c070329131101030e16060f02060c0405011b060f0905190807060507090e090304090b0a0302131d 72
    0x121403920b038000c2a50105002d501d4540546001c10f034040d160000d00044030780d4803040e50302e00c3c03c007030400c94005001c3c09440c03c1038000d800107011950402c3c8156401c0d0001e00400400c50b9110159051020341ca0201300140e8480c2d8a03000554040c178051180990750b100310071140c6a0080003030700c00211f42003040302c0342c190b101c0c980414800c08400030b1b1281ca0264502010031010400c88203071140500d111240c003c4041910759004ca0804990100d050640d40e030000608500c05200000088140d040007142080c50000014009981c0a84103000c54109005109a81c9608002ca9084030000d02e04041d40156241a0504550541c400141041c2c54150310b8070100b80b4541000502ca4000c0041d0780c16001228141c05a080007410020031092042007c00c00041d940c0d409540c0005103490091140c540310080202d0004068688403441e41c000f003401c2000c0c0845000700403000c1c4090f02c925803146d2455012030f0300c07000210400d40d605611503007001140001085000c88080c1c05004503000f20342 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 271712733 1250 271711483 271711487
    0xa120807060e06101a07020d0b0604020409090614070e061b0c09090c010f03180b04060204030b10080106120b01061b0227060a03050d1d0402131e03080a1409040c 71
    0x1034621418443c0050f1010300341c82c1001c05c4068400c210340217441e8091400c0d042c3d0741c1c2052040004c01860384940c1c20300012404440c0361040c2480a4414940011444c0c0c4005042c040d040d0010600401c10404d00703d4501940c91b40000d40304400c040c501d0465550308422aa80d05000c042510550031503461300030400442e000040950301c0035004e03216405070740b107800802c1b41903410b03c0e031220b4281c2c0d41640307109c0e000980c69007107254040d009000050415850b40e951920400c0c1c2683c2c41c82001000d07042c1806601070a1107044014403514940040140303c541e92030203411014402d410522160880c58003c40355800d0b00c0c3c10300c841d07000b000701480d800a0704a9564040760005120035a032442000a85a41070040450040d01d1b00000145424684004115850481072940035800d002d00d4510450503140c1d400607101c0c03070124100c0d5030002070502c058081d020106240c0b0b4038026800e50410004203000300d08032242c404040c5050b000081080e4002c034601e1181800c03da40040c54042c808070669 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 271713983 1250 271712733 271712761
    0xd0c0909030504091407080115180605090901080a020f041a03070305100c02060408040911070605010b0316050306181e01090c0f0507080306090a0e0a031d0a120807060e06 75
    0x44d021303070003c10455261081c10240080211440e501040b803550043c8802100783c03600d40728800007403400f109251141d660012550007968008000324002040c0000107281c09400750b03015042005c000d10364030300b440c0c0000d07100340110151036001d82c1d40d0340425a0b244c40780400800c258a80a0100c408180c0d0360302d051661401c0142c0d410b0003036840c0c0600d0440007403000c5036090040d60082040c50826044c444000000c012840302c03140101c100700f00c0b4000003a550700480e40240540c280e00340c1c6900d0080740f101004808820008108001041040700540e01c0107600340104180301c254010b07a540344418882000e003440079150701c0c0302640000042082e0381c2e8120368401403030b91756030006042c030031030341900d49008a0750000d120650174800281c1504105089552140520901080075082400c0e91406e01a095100740c0004681d0110491034140c400b1107400407440a0712401c098900d094042070030400030103001403a0020000b40c0c001880381d190007041c0085184c10a40e2017a040c5060034203490 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 271715233 1250 271713983 271713989
    0x3123402030a150509012d021207020d09050d08030a0b03010f090501091101090509010e06011e020c0102060609131401020c0f0a050607080c030a09061b0302090f0402070c050d0c0909030504 83
    0x450404000a0540c0810f0044047d42d48040c11f44200031452941040c034200700044503103802e03550074041e80c003408e112220460b0182c80e0302d4025000501041000078031010703164000354000d48006140c1000035140004403a480700b0444030005080e00d1210000f4007410b0800030403156141004002000d122040d4844243e0030710880601031461404001958103010781d00c2416880081c4000402030088000a80f07544800140341030b107450100445055a203501d000400401030f0305c800b400a0340c81d42c04100e0150003000407500395506150041c602c500001c91603100414182e070144d0211040b036003d4054031848207011040c0c400f03100c080c81140d031f40e0b0081940d042e942c80c45650f01140700a8003070503109010b040181c0d040f81c61540c03600c0152003d0054010115000d80c1e441c00b1000c004481c0d901d43d034103031401994026959203240c42c20001a003d0034142180f08510410048001504c215030000481f541a84c4005501020f820140020030841e4490000c060030402081c0030594844000c0081d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 271716483 1250 271715233 271715273
    0x405011d19140f030109030206190b03060f0a140910150b07110a06080603030a270905060109080c030616090b03010605071e051518030f0903123402030a 67
    0x503941030f030001c1600740c0e0001e030302c0600960000e401041c1c900300da41c020a03100c0d400310349000c80e4004130385010a141c21411540e946042d00c00d4028013038487c841e401020100c0c0180303104400d150911011072600c40031414946840c2580e120f8910f01e080f02e40c0c0c181000200b0008454a44030001d03800c210940140b0200040e2041d001c0305404500d10f030142d05614082d00c80900150300307003103152070305648038041441c40a104006950054091010103800b41c0082c100b0303000c2c00b0500341441e034005070002032183c0101c00706801140e00408203032400103a199218106501c01d0b01e0030740007440103451950706504003401001c0f00000104045800c04001d0284a20420114111181d860700002080c41510402011900b000c06265443d4040410a6030004c00705060401c4c5100101e800500d0b40d80400c10201e030042c804901c52805140031b1242855611035106840c0c0b41c06100441c50b14640d02c6100c00501440040481c991078402c03111100401380d40c040c00322800ea400034100074100b161007000e5154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 271717733 1250 271716483 271716499
    0x8040609080a0819050d0912020105090307030215061f0c0b01120f11011202071406010611070905090703060507020604020916090303030203150414160201020405011d1914 75
    0xe000e0600140c0800c442c1d0f0880e00300d0342804401042501c682c080d224072002088000e0080c4824039946100d00e001c1c40384a2000e41211403450305001c1e007904e03001041c03d4025081441031501003500419442d45c01c020407801804a65038035000104113142c102d554030082001c108486403801d4000700800341050082000000ca0780e80c4910700032004402d8080200030072030301109a00080c0006103140c0028905040004413030002e80680400c82e0071020056866404841c001c8400d06000c0c0922405004039240110b09507031000c0e4501c4e9118520f1007500011556000080d0300702400784141005550301c1a0300b40101d0030f0408009541c0ea2060302e06034422506a804215114085195004078007416142c0050b9540356032401e9000707410040203011460014200c1c440c10b582c035407084440c0000c1803950401c0c0e50034074a44842c581d110078180c00f425a0302c10441071002d40c1e006a99007201d104071500c44003000c07258402150100342c0106240d14060840d07c408641140c040c1d00c03074440318905503441f130 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 271718983 1250 271717733 271717739
    0x6080a050604061a0f09060a0b1801091a03041b0305060a020c1903020c01030b120f060414010b0d0b0403020313081b010504050d080705240703060509040b0f1803040308040609 77
    0x108013400d1184501c2d5108048014038079039420503100050340000000d01c0000c006a45603c03a10440d44440f810700080d010340c1030550815a0040042000390240305c0030507001d00107139225402c9620000d080074040c00e80d404e401100841c0c0102150002d154040146c2e400c0d81001c55460000e5041030a001003640034240090030104130100c000844c00b038059000b4400c003020040103500420908801c0d40d04000c01c614240c00c040b40421001c01603c58400090886140c1410690511901c482c01c209069040c42c10030b405541d610001d0601c996003000300280c4a81711841d003030f491841451500c030f6400d003440500007921040070400c102403005210b0020b03085d0106d10300444680c81980034a81e4030484c1c130006c0b1030100b1103000c040e180743c07880f0340c0456901d1320b10700740f800a080c0c1c1100c4c15070354160552010014403590500409000b00000ea40e03481c0300c0d051070b56500514001c0244292614814840001c003100c1c140301220b00984c40c01f0f01940d50355500d0303081c100711651040c02080c0229191040c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 271720233 1250 271718983 271719011
    0x409021f051801111c020f0304080303040b0105091e060f1c11180c0f040b040b03010f0b040b03280c020a06060b0a021b04020d020a031a1f1206080a05060406 69
    0x803818210030368000c0c1c0b0551645c0800050105c45001404e401c40c4035200021017800070801c01440070f4a4030708000c60b26450310303241c01030303c2441c145c0040780100345041c140844502d00c81d0f04440303502d240403040041c0b995403a02081c004484606d04aa006503c0ca1070001c03040000b07101e20000c2c40c091040412500010006d100002d1001512020703d00c90f0940088c4078640310f5000b414020845103803213071909564940320750080c0c000384c00c5509000d80c000010403031071401d00f10040040c00c00c0783c142814680f515014481d0350000803c0004110700e11885c6840303000700c034074043c0001c0c041810204076414007804000e40c0e80303c2e240021200d05191130008503480920006582c0c0a00b0a54014404240b1100c0c02079082e003400050650403075001c3c01090241041c600103003c000741c00c1c4d600080d00d040b01041035065410b1500229000d01e800001d0f00c03042c04100c0351400203008171401e001c4145151600c0b03d6005000c244e01c945024068005108200a000b20b1402c2c0030714052007090110f040400ba81d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 271721483 1250 271720233 271720247
    0xb07020d0f090905131208070201050a15030b0a0e0708070314030909060d0602070b010b0901021c081302190602030a0909110403061d0601081f140103020409021f051801 74
    0x501010a014140421042c10079070040340c0e0020aa041c820b02e10714243d540d8011382c0706982034250201f00703d18200800c1e41e6091041d2907200300740303503814007228213800711703030300906405020280104444000184140c40300d900503280c2500d2140840301a05d44c1c60b00001d48816443c003084456942850550303640410000948180c001c00030002c100c01e85510041101780001011304030f50a40d000d02044c1c01168107104154002d01010035466a9401500f00090604880540441d42403c1e2950120001544001a20340c800014025203c0c0d400705400010707180711407030544455a03c00303080041005540070001c0d1803141c4042c0c4520440b251928401000e80340c03d4048500c3c20302040c401000419440d400c100800c034507509680b03503141d00074a03095003401d0f030907080360035290300caa028076800c2402050044103008151104100c1c60002c2590015200018480079102c1c42d1220761010035980d4141201a402d0503801d80950030300d4010602030041e805c0342c01400e24004040d0201c080d994040c402d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 271722733 1250 271721483 271721507
    0x50319140a0507050a0b0907031542080d0905060309030315360a020a2c18090d1103030a0c020c03030a030204030501150f0308090415030b07020d 64
    0xe480e04090255600325025001000c05075505d00c244458039022615074260140600b05803806002014158104a1111000d480042004a1a001c01d03124605181403541c21404800c1074800010004811518050420441803200542c2e02a030001a001c0e800038490803c102c41d81c0700c4650181c0d4440c104002070004841c41d1b8143d03041000040c205c80303200c00c0c034108440c0e001032040b14510140d5094420005141d103c10340e0f004191401c048a02140701c585640c00600000c00390f00d05020400300400751540c8001c0c88071020840d010349540242d00f14a6138090f1f410103000f8000000d000300300c03011022419110340d8101c1c00b0b8108940a01449010940c660f00141d0004510b0358a6054078000103220900906c402c6010b1800a5102550107000030300d5502c9080d5030250319141141000c900319282c940c60f2040c8216150400c10085081d00c00580c11a504100507039210100f01c170110b0003402a00600807810740824801200b0406440e1280d4010320403a8211a888200e00106a4200488003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 271723983 1250 271722733 271722767
    0x1205042312030f0409020d090c06080601110705030a0201050d02042418030308010605180604060309020a0509090a03050a0905040204061e090b090f13050403080403020f070f090b0418050319 83
    0x1101788280714a64000b0500e50900d14000074001305030b91628101019a90031003000101c666040c0301540d130740018003d000e070034001c000d0007000e4036007000170740d8803141884000c1c1880320204030a82ca120099040c3c900421014400000544050082c1e080c1d100681500902240a011100030321000000d002d00a81c4d034951180700b00c503400c2800c1900d154100c031075280c420342074140003120315481d402d0280000388150744000c038050206104005450ba940c2e04440e02a003151010441807840024400096580604046a0700c03107035030300202c5080c142030b004240c02c10300010b80018141d50042603942940f41c0c0d1400c1c038240c400300a0b4210f03090141c1e4400c15200510900c59000c452a000c054803805030300081c0f444c1c0540384080c0c1c211094450840701039012403012400c0005247d014020307102e00c081030741f001d000d03420700b407002252030484280240c5011175900c822280042d241c551000c2090036034590091844a0f052070305a5580c0c0c03141d403c02c1101c2c074610f250021818042c50401d501041a6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 271725233 1250 271723983 271723987
    0x3140a0606051209190605070e0312090607020117010e040201030f020a1e021603211b0b04020d02030604050d110c0616021c060501031712041205042312030f 69
    0x198030003015106000d0205081400352210140003240825002e1351814070031080820285050072340540401e0050900d02d01a400c40d03505404103049060494240301c10450303009448a0441c00120307520041480f08001c401c8180b000840e0700038000d07401503c900e100741c4c1d09000b00d1804498120590080320342000c0842d054036510001500c042c55416100d0015104850200755031030030380d000e41400d641c4213580101c2460201c0140314055202d01140e104142095103a0381100d030104021812003c1000d040400410701089c11540c1f110001c0c4a0550020115021130030241400c4c3d4032513120800380750100d91071210030a9084000300751100440802800681820200c8180c1d40460502c200200d912848120706400d2034959000310b400024002e0500103507a43c110721302421480f441e640c100c200c66074180180d11155200b50440c070b51181d4418804003040181400a490b94090f6800950a02c04040400c54445c2090113000c03000c030600300c41e181904030782c903088203440f40f00710760b0200220001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 271726483 1250 271725233 271725247
    0x1103100204141011011107050f0303060303042d1805070e011b300e01020705130b01120e0114010b0a230409110901020606010806030309010c03050f04030303140a060605 74
    0x150050b02d10341140c50070721360016981e88000c05d0031295001030603004550041401018000c0c10007180c030440074044000c41c51400c0c4040080da80b4002c81c810110701c0300901d085000f01050090001030700500c0d40407010b84491b11400c10b0360031081660189810036203400d00040403944a00c5510b08524010385a1514203030084624440700240d0071b8060741c98030704144030284114040e04c0f5180e1521520035450561004144009022462450b0f20504662028009010301c0d40c441103400e0010110000c0002d02d0500e41006882c080c0b80203409181441c0b0b0241c110500c60f4064204580c0302c12400340445141c4c0c1c8a1000d510700740100040300d4000f0307170890400710456079804001d8440d005850f80e020304296403800c0d41400da90710240c50301c40003080407440c0384595804212464001d40700742040c038402d00c0c1000200e0b82c1ca020b210340d05030400c05082606000c0c18098021034102254000780c82341c1c0d598490038041e0240160301c0708480054806d00000f0400d114034420700040d82c0095440b5858201 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 271727733 1250 271726483 271726489
    0x21c050f0c0703020a171e0c030f0c01090f0c17010e0a08031806090d0f0305070e0402030601050d0f021222031404050907110f0c060301150306030f110310020414 71
    0x425107049040d4450170785608049081403840000d040d8200d0b555035a00c80000015068405d00e003094508a4030f42030012400d000d001005582000702b107030040648500340703840309074003619102c00007402002003164040b061148041800c015140690801c000a4511a80381401c13a0012507030400c5c00d17040b464180000801107001950461800b001081501c8066440c4608024042d80e030480d480d070007210000c111035000f11103440c000d21217040400c60380c90454005040c00318003080035407003141d0000015080d41c2c01b541c10b9030440c1403080c0041003a1564803024200a41c45100e00210b0684a6800280146610001000315001004003002128081c0c3e509a50f00c2041401400e8090424040401d00740c4803414218803521640c1c1d20302030b540300c09002c45420000c0003010220030340c000c0c0c265007156440750000c4904503010886503001c003d0b0032540440c0244416007000b030021003100004800e10080107020030010000301d080c1d44580510501c0c0d4803c9124174400c4e02d45516903050980030b43c1ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 271728983 1250 271727733 271727737
    0x606090603010e060c07020306060a0b0a0c050723030c03011503060e0c0603040602070b01050102070510140c0a0f031d0a0509041703010f030507050303120118020408030a03021c050f0c 81
    0xd5000c1c0003c240c00840846244c00d002c1c0413101100e000c03101191407800d40c6002c0000e945c00c210162a4279216900b0034034904079502c03440504405000341c0d0302d2510100701e001c00100c001025035006024200c0c00070150000c50700008501e007442445201100b400510301031240c01c9805404150082440f4a9580c449004d44070b0030000346aa03002c1d101e45e100d65610307030200035880780f4450140140c1c1e4064515254140324030603080780b07045512002c3c0c1072105480c2c3c1c480211440301c10742020804801c0085901c4001d21440c813500030117004d071240d00d004101e0391201c5010040e1094403a503c2d50b0000c00b2080b444c03aa001c86503d035010110500800540c10001822604a40200100d2056040030a10041958401e9200a040134030507942042400801e02809016050803405507282c00501c401540381904180611440ca444000c0d18030000580396044030002c011110035a52610400d05003c0c000350000c0302c0d042440c0300b5450b08200311007030500c2070520441070608620305070389592860300a0743d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 271730233 1250 271728983 271728991
    0x210020703080414040e01090b130c050a0609060f05030c0409051f080609010b15071b08070b091f02070b090d0b010e090d020307050c0f0622031211060609 68
    0x94012140044041250701c0b006001501c0f0440030410a015084180412142c00b400103103550303458403105100054122103166009556540c01c00004921070030800c89410300c552101d680100940c00c0003562a820501c540101c44090310361003520300800340309803013510044078880341244041100748002c007995800142c22000006001262a6404480b0104441c040d04500c045500032810041900700074007504165210903125598204080c9481203c00c0c000c000e4021700584040780181c00140180742258000c00741d00c001c03101610f0307036100909070b182d00580c42d40740200d0440414401c0c066070003880600b9a8000e50040c0642454581c0c080155003044403400e5002070180040c2d800715a00c40d00060282c000e001e9510418104034842528003014050b0860640d081403184001140c00400c030101c070f09005984030f54115250313100064581c4642009481d2488400c1c4000303151804411185007581c1c40f400d121000401036801c20b40d100103045008e40656480a4006040c03810118591504 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 271731483 1250 271730233 271730237
    0x703150e071d03030c07050a06021f1a1c02031b2809020c06010915030c061101020d0c08090c04060b0d020d0609050c0717030402060403060203070207031202070611030c07030210 78
    0x400310300400084d0540c0d02403842040340794002c4a0900403890070740c54020040005000401c0098020800c0b0180281d11003070809601d50784100d4a650003101c84480c00802000138601d4410451321461a1b0541104a4040e8003e10403c032248501e5070184050341e00c0000c000744003100003a15000f1140700c010a900102c001840c0145000803c58400d0001e800002d4110001d04002d40c1000291800c0365012010f00e068100464030030400f180e41000143d098032441c0c580001510b100480d0b543c0a4410411400503240c036061384408415030201600d8007802e4588143c510441c4a5801c20064400b540103510f6490b00400904500014950081c500d01422040110f20300759501145030481e04100c9010100142c001020820411003082e0b0100280390005100e0542c02e140c0c02280042c061800700814150340000400c007c01c1c001c100c0d800045512155450007481c21110007915050a8461080820480c115014a014001c82aa480340e01b2031002090305c0c515540070410526034034075135202 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 271732733 1250 271731483 271731527
    0xd051801030b1908060901021305061305060304060902010809120307030c0e10020601150f0c06380103140402030a0206030408120108011d0a0506060420120703150e07 73
    0x1d5110155243d6001030040511420185005070040c24400014010016a441004107841d42620070b0350a6066034000d9800c7d03038445070801000c015070750107a003012380e003e18048100310401044c0d800070384c405ca100782d903140441d0b1556100540d44400450080284034014000204440d1103527000d940d00e4005894030031901317143c000208005601c002c0c18500182c02c5540144079800380030b1001d80f10042d2514000408255480c0001c4c000c401d02a030003006a42c4a026416182d10480400c0718100070030001900c401d22101c01696407200c011418070b000c24108009413800304050191244200e801802a040c841241c3e4201f0003241e02c001c00444e000c0768103002c440605001c119116002c0c21620b8000200e0550320034108080e511800e0960401c1d6214110b40800284089146a0010010350300402c7d1501c180e980c1c81010001d032507001304510000304500e84800c140c1c5208502404039620101b00b44031015070703110f841700580c0c06a10180d4032650301207032240340302d00b01103d071164040840034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 271733983 1250 271732733 271732751
    0x4020a05101b08040501020607050a09150905180603060a0b06070f060e0f07080c040c0509100306050d03020309120a050d0c0804030b090c040c02010b0a12020d0515180d05180103 78
    0x100b03010002582034450180101d03045c046540c04214942e00880e0070304005d0f0600210b280001c1c2071000500078911f02400d02c1440d03100d10b41c02070f2100b0f00a40001403900030a003040990002400004541a500c6442254042020790600d0b00c62040c200d44003130702580c41c12690340c8070080c2c600c070745810403184940d5070315444007507080610241d41c80300d2040b070141c0b01152804800c0b61822040c00d024034444d41c50030341c2c1d1000c1c0035045400c0391003084080e12205007000c55403000b46c2c014100e40e440325812104042d564410140d010004150504080710703909102500c40082d40e55a40e24071200034510341c0402600c900c50760050703c1c0314420622070300005182c25169520100d05050540d100c6440760300020a00a4603d0700380280e50180a01d4030080000340b0041c400900400300030f1103a04140a540c82d03900c415925100700b14001c2a41103012600c41c0f8180c02c2d2041001e40d002c40e070300c0980d05502e050751524880c0120341c1d22290803041d03807942e082c10001e080b407082d52402c01170311605155442440d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 271735233 1250 271733983 271734017
    0x204051e010807030b0a1a0d020d0203100c020616050a200d0509100305160507020a0b0309060103021309110103020c03070b0103080306030c010c020603010b03071b061a0904020a0510 80
    0x78040c09260000d412101d10f10300d41910310b41030180491800500305a800c070041c11a500e4000c2e0351444c01c60f40d5182d10780003030010843c40c440000020350503010791515041d03100304503041a49940b1440d400c4800a0b9a00120343c4071600410400c40000350f4104035014001e481207642d030b41a2a10760b4408541c0384001c40e80c540c030f82049900554045000441d2454440c6000d0030b500a082d1024202030111303150012a455000e0080480c40041c42004602d034001d540743ca1a526019120394903c03240c3d64100f8507110327595001c1c00d1008034400e400112040b2108180c41c02006400c65124189441c00b0407404d0040d40603401a82d101803803031105100c5e03400400c50b4440200d000394010079903585d40c2c1c100202494104a0725481c400c0c1030140840915006071100b008490444107030904043c4c5a4864213001c0340e1465a401c0d00c0306010311341008030800d2005582c490100d82404207151a014101181401240c0c1400c035030181d400300b518031040003241030101e255159080765103400a1450440022 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 271736483 1250 271735233 271735291
    0x72003030c010204122a0611010b06180a0602070b030f250c06060801060509040b04020307030c061e210c030b040207030c1115160201020c090109020d1407020703020405 74
    0x629400d449115401440101c0d864070040d030b4200829001c00003000f0311001c8214025101f50010004070f6075020742c00950a43c026098500001c12141da00d500e21a003a41500041c080c1c00d03485500440030001e043c9000003044011141d0001ca210f041d070b030b901c031400032403a440106052008800b003503e44003200e904000031850581103031600005400c5908010b000c035143c642020445038500f103c18821540c402072401c0e03009070b21581060807661544003090420409a00c014600c1000380d10214040d60012980c0100c0e400c4403011060a00001e20b04a0700c02417140d558800b451550764500605042ea42c00248403622036007008546d100020010400f2640800310030b074001003074a8082c0040000c00d90500040210440d41028080060340300b0b00601d01c07502c040128802201d80c030703250445e402400710b1246203034001e04030860713581d4925045010f944034541e4401e8072403030240116015883e40803c03901441480d8010306842d421036080c00028580502031184c800c40001042e240800300e401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 271737733 1250 271736483 271736489
    0xc05040b0309030c01060504020406120b040e01020703050a03110306101b0b090a060f0204030218040c030605040807020301200a0f021e03120903040b090f0f04050c1905072003030c010204 82
    0xc003c55941c004460300c5030865841d40c00407031056004100421a013a481150034000308104503000590b014030200117001003000c40d0510801e54004034080c000e06070800003a0000d0706d05070720244002c900020000c0b5144c4001c89100d41e01c00105a0f020322614400d4034040d40000031941c01c099809555102d842e0101c0d01240c44404135030101c0d061008002c12809080208801c0c490300303508150540c0e0003d010a0141c010f104c034a0940c420004041c4041076202030b00031a0054030400440c10f0a09001d130403907204103001c1c4d0196082c0740200d0840c90b80c1701c00d03800e054291150111b0401e08180000c407000c070050403160f001c41c030174100e44215041c140042681c5030200384009503030b120240721061360701500007014500b00e500248070402940051f00304607801d25004917102e4050000c0c801c0010880040703243c0702034011703240800300655080c228005000011108842244041d25a00210394a104101c0000c00128419003105980710008010703403800e94004054034181698180c4090883e086a8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 271738983 1250 271737733 271737751
    0x5061c140108161d01060e0102100603120314070e09090f0f06070f0503070c2301230a020901021504052b0305010f140f150f040302030c100207090c05040b03 69
    0x12010441100310071420f1401040340302e08100c440010341c03240089900051140205201c58001c80d4030f9681c1c030a2001e0749004a5107081080141c1d00c2c3e042690686902c8680000807034501404400701102000800e07224012035a90711a0440c180c0d0305020005a0140c460301c030030700c940c1c0f1081c22035041c1802106c45442d07030040105001c1c580403100030b0400c10100e1404007480b50401c00c0c0301c85258050949040907800442e40b80c10000140d07452514a444000e6052403546000d4034020020181c04a035010001e0f070b00f00c03d0865072540f90310041280b0030000c4d1213000da440601c0307404c10201104049540240100300f620317004010b11030300b00500ca00d05200341c00510039440c1e0000000d501882094003402443c0581d030382e4641400e00c000901075a000c0d6491050f51015849140c607542c4002c255211150801e0441e2101c01070005051950010f0104030322034000d00c20080f0302801c208012104501c2668001c0c0700c17091604107000001c0610103075800070010100004030315460420003d41c055000b072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 271740233 1250 271738983 271738993
    0x170318130216110907080103080703020307080c03030a0b060c0c0d060f1103040c0e061008150411040611062703071209031e151104030c03110112050105061c140108 72
    0x9450300700c01003e40000c586100700802ea0500007010744c030500381c1c1e064907030080500e6a0385a00c0e0034180d00d18001c0f94070043c401c0c240040c580c0c030b140d0f00120141d0700809442d5018001560b80e0710801445002d403e0003e80d20f0b070f005201d200c280f460700c000d0810000303014400c001690408016080c06440404c50b01400e650700020912040102d1444034100520b1280764280c0c2a0510a0000380710b0340195102d0320401c5096404a410810821106958100010401c0101700e020b40300c5c8581d180c101d403261801058051000d071113918804180c0d203228408030180303484051250322240c0380744044035000d8112440180540000603d20074501c0050710f0300d84d19010f1145113503140c0303100c05880d000c01ca140003184a00711a070006030400390b03000b00e000000401140140c4013606240c1c49000b40d41c409005105820400824401082c1d1109209c500c00e82e00e40743c050258404080c2640c900380700320380c1c0041c010045210002402c6084a05240c0d40035004107070105400b444940c40b44080c0c210503c0c076086 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 271741483 1250 271740233 271740277
    0x151d07060504171207080901031409100f0b09010605130f1d13050c010e030a020a0902030a0b0a060c1709060d0b0a052b050c09041104061703181302 65
    0xf0009034188102c84450040c1161400700318070304c4403801200c400802c29140441d00c0890742e03019800131000241c2c07489540b01c851401ca10303580e60f2210400c10440840c0d10b80082c1c80e8100c8070b14095600184000340c664030f41c3d03910b001d40440f00d541c00306120580c80c40701c0e444081004150904079000030400c01d034641c0100d4a2543d0b042c58400c81c040e1840002d0382d050403171040050700c0411200c1e500c1d0713800d0905030041d402000101e0b0404180c0d0340000c0d44401c3c0681c0101d4940a81d03030155000f4480c02d002041007034501414407410310400d0003443c001c10060600000065500150403002c80102500d0038201a007900c0460110b412a920444440740c46285804e114184010031400502e411255240401d80200c000e050011100c05e500c00810042c40b005000d1000400c01c6030780100c07000e8940155450b01d402c04601119043c0c0d42180302e01d00744540012101e50050b12951a01c51a03005145041180025510101e45001d81e5030780085450707204079004002c0f480580318408104060781d82c4540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 271742733 1250 271741483 271741499
    0x908031005100521090705062101050909070e0c190c020301150b09040515030a1209050907080f0907091b021603080a0c1b0909140109151d07060504 65
    0x400b02c02403030200b1009108028060580103203148407009070000489554542c11021424046140c0000c0d80281000521803851440d00c082c194075940540c01020040c4d0701c4404110300c0c1001501c0400860b40900c10038090b41c80112a1587c01c29000150f4034500071080d0035044060780349102c5000484c1d4080305400a60400b03001d9412580645145c1607041e50400c002da44490044148a501032a50f0b200000c11102000c0d1103403a41c030300010201c8080414070320b42400b0000488030150f00181c01d6110000f6241000c103c5d0a0145130143c4415055940d524482183d01d000203040ca039061084190000b00c040840c40343d140c82d01c040c4094400c0045181e000646440155a0b0400b60002c1c95002080070941d01000d5490710710300da107040320051605007400c4115080806140324841440c083c0001d46080e55405454070740d00c9030461081014a2b9005c8a08842d0940d2b4003402041848115450071b0b55a580415090070070030385480d444407800c040a6150003000d41106000c1400060b007400030380 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 271743983 1250 271742733 271742749
    0xc0d0c0510110307050903030f030109020301030c0905150607020301091b17030301080c1c1703010e070c1a07050d1a0306060a061407060b130f18050a0b06040908031005 74
    0x180d4400418054800d00320000b03403207484002e145000700440882c28240d2581c0074003c40d4400e0024104103900d03940c50700b051000940c0284000c0f204034aa080c0d00054944d00da02903540b094201000c42c1c04141524414401c0d039512285049901d0b559030340ca900000b880d95030030110440850740701c040c0d0b500d062000c500c1c0c0c600e26825443e92640c0c014401007106000c0010304680c0c3c1d0406807044000314800c0441281d200b108941c00400d81181d401140c0f001050060281d8100c0719602d5055503e502c0d800e0080d14a00042d001c007130304406296200441c0d01ca1101031550b0481e0161814074608600c0181c28421241614a04100b0044820303840c0300300e2400704221398000b031040b07500b030b0162490000301034659540400c080110350008100a4148000b80e032010002185c040c3c8400140d1a0566550340248103450708428680d18190400d10b03000704800d07403180410f512000601c8942190f4486001007000140301d190b0154907007151000107020000998002e10b40160a07806441c14a01045101c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 271745233 1250 271743983 271744003
    0xd0c0207090e0a140102040b16120306060503060d0302031611190e1801020405130209010210200702030109020a03230a030905100c0803011203030605030a02030706050a050c0d0c05 79
    0x1241c14402e952244030400305908041940c01038152010708103060106000e801580d124800b100c034081215110034542501e40500103202e28107861400c008614160f007105c8142c05000c00241d405c0c40004e003a410040b040401141c0640112400d106841001c3c00901480d000111040c02c0c2420040c0c24a0400c105250448900c003100300b2489410070300d00307040c10302001f4030304060592520074002c04130000b0360486000c0c00340030305581040c0391200e0f85500698020b440035030052082401d0365803100300d036100c0c0325030f114500c0110440c1d500e1480c10150b0542c00c410801e81e4503558889580005950700120304005503c14100421401c1e40400d0001c8507103140244840d03550041780d20721000030350012200c0d094510894405070720036001e14084034070416401005220000000c00410003000020b800c5060510039074003072041585401c14540c0b07178880c0d108020341550042c0b20070f120302e03400756014010001462600c10308203000501007a241a070b10b1040d00700800c00c4821100d00f070001c280121098 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 271746483 1250 271745233 271745249
    0xd03140609060907050721110c0d0206160203010b06040e061c05070e04080c01051f0b0405091512120a080c030709030210050d060b09010f020f03090103020913020d0c0207 75
    0x745240042c0400c583d440f0080801d01007240000c0c0304c1c000c0003040c204c442c10088200014078205074085002415110162230366195030310403020300042c3d07841c00e00c00405400b5809003400303082201e80c007003100855039103a03000c9070705549403c0c100032a80c803200007800c001c20b0042c400380700301d08001040c4020718142c03c050705103d802c00c1c2001400f0a00008640040700c1401498107004d640340d0805402c60700031a000f59000c0d5080000b0b00c5a41c106003210480c0e00000e107070b5175071071007a0b8641c10404244150b01c0f5440d00b00480c000040c0c61005000c29a01070b80c1c01c0074002d200f1581c07607501b030036091401d41118000c070040042400070f02c0950000ea0154401508440c0610b1030030318074009404d10001c1c0c40024854403d4081e049202445082900c9085102c0c26040c0503a6440e051025515008541218005401c0e1142e0140d803903c0003600d405503520b072801651800c1b4005004501a5102910b4660045031101c00100040840e00c01800c80d4490004005075030b004400000b414805190310801c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 271747733 1250 271746483 271746499
    0x4060e0307210c0506120a0c0f1403091207051b060333040204080109050d141204020406030b04030f03060e060a05040b0301090c03030203280c0f02120d031406 70
    0x300404600c41648280001203640c4a54000c0928125401e0f40d00d5030043e0340c0106000c2400840404c0a10310390740181c00100050180e1a0800c40031a81988811b090000090030040400c10544403034004540040d460010b589044403002889001a0b0040c8400c9540707500105410184090201e030880e19814125500d602d941003001341c0a410007203440c0b076159081400d000c8484244243e09a50052041c040c00c25922541e9a0302418000d008554081d209402004445440c0a106048040301c1117094000305037050720080408001c5040184101e030001e40d9504080041000d10402a1080c0d200c0d0b5211038243e102c0b0400101924060303841800030203032003001d02800d81c2e41c4c1d04041e02079400a46002407140e02550019000d401c403684090200b14101802005041d03010009000e21001280440b4003070b01d8116401c1e41503000c0c0e69503035000a61140003000065440d0320714410300740c0020700354245101d0060310035040081c0e41007141c0c0802d03616403d130021522250801d5a0022040761808 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 271748983 1250 271747733 271747739
    0x1090c030b010f050d06091107050705041b080907031a01170c0306011e090c09030b0f06090402010f0329100201020705150907030f0b06040605033405060c010204060e0307 75
    0xa4800014000120b0130300001151501d015140e40d80110005e04450300c0234030480c0c1c138200484441d5401114180c445020388000803506017024020680941c99102072001032030179030007049698071030151030000680250800003000c00c4003070b8000030002e080d180d600d1035594074040741c030030b102c18018041d0350158100016081c90b540d030108201c0d0449111002150758440340c044062000c40203074000741449454088958582d6501c0007918042c0d92150b0304900e416111101601820a03085030f031107510140d888002001548a100303041c00c0d4140301c1c2004161510f040243c003c01207080580040600c0310040d084040d8603000381c0b42601d004050000310301e0a28992606038803442d40114100c40308601a021a00301c130410050403000f503402031241005140149403609010105035076003885039003406001301f070304e2074041400302010702c050000040c6181c0c6c002004c2850400075040c0343c1e130a4000500050710b42c59141c018040f504070b0400050f07881c0d0400030050080361072000000e01031b034804c84042c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 271750233 1250 271748983 271748987
    0x4060818070b0a090f0905010807170a230d17010b0403031202091206070309020933010522030203120f0409110915070c080316080c150f01090c030b01 66
    0x26006440000c030b522a561070300d8500644221515601068051008010029035030480341e019070b043c0c1c0c25502c10380380401c0d42c41c03984105c120b01404551800da0403403580741002a1180310302e00d0b1a100e0442c986c1403c810f042c0c0b80c00342490342c1d14001e940403580480b940051425413540c032501518004242d903080606507240140070103083c0321007864943d030006040705a6035420404c0e0b00700147c1c000464110340f8204400902503d400d1108901840c1e649021403407003200b50500c54186000340351025440103041302d0211255541201035414060704000300081c200d051041d800400e440031a90241843ca0340c810b161803c034a03220358120130002484280d03885881c0070200d60440f83d0b03040c404901c114640c9111036a0f07104400c200f540c070031005542004405000310280000c0b80c021444244040d03982c800304ca1b00c9214881000d2007008042c0d201100148603d00a8051602450110340001d0010150000340d00340a80d08079650309a181c0041188940d1402100320a000030b24040c03080c90000e03000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 271751483 1250 271750233 271750243
    0x309020a082424060706060303050408011811010f090509010807050108060301022803110d050a0c0e0a17030c01020d1506020706050d1e0f0c02010b040213051207081204060818 77
    0x12043c1a04004400c80c05641da8501510304e4160042010400036a5074500074001e94001d00c2071608039424000100038094054071708041e0241c00041040900f003a840c0112000c0c814075130188140b00d50044040b03a540c941c90402c3c0d01070003404e00101000b6080c03200144c9003100c0208424420fa004110301e00341846c1e50700d610807000900f8265502d4070846414140c0207080008011030341c0c180c0c0030800180d5007440b40c00840c0103005010080110085c4101c0c02c55070a603064070780d180c0083c4105c004100e0300c0c1000c92a000b0202440301682d041c100000300b00c03400d90380015000c01ca1a61640d8000c900384400e00d201c0e10081030140010301d007807480c00c00050224012203012501d842e65440c15010005c0b070034400d06290704202e610070800081c030100040002d09150103c0c0c001903180942151080c03c0c14400c0300c1c5005400c0c0c1703080d20380500d0a020440c0e80d402c01c141c200c016005900000803e24400c00607828500031040045c2e88450a241d00180408802040c40907080441c180740030143c040410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 271752733 1250 271751483 271751521
    0xf11040f06030c050f2205010303080c0711011b0b040501090605090d091809120c030809070608010302040c030b09040b06040c08060904110a08070f08070603060b0f0306010309020a0824 81
    0xa009884217202c400000d401c10120107032841152250030350008081030b1940704606a900c243c448403201d4641c60844002070040300c0b8000c3c03d6100d05d003142103280d03019070a046202103d82c0c04a00c240d010b9650360390311505065030200c072641c0d141c210b510304200060003a584e00c42d41407002442800c40a1a004024000c644240c1280008010542c0785100050f004040c0c01d80c1c00c6400f4108144000c503004012803511a01540050340c0c20340481c0b406400883c0d10301c11204260303038990a0340d003181c08000003005813820340030502d030350303113200186035200d2035600d40c413803030081004a00702e140900920042e01d540c03540d12400c00440300100565075491202080d00309400507144c01d0481902004110481c00b690000c00c101d01c1150000030b04014510f2100341910104c0050b03800c0c0340c0c1d4603a4282c0c29104a4080c00312409400d00c8090050705d2004043e550124051602154000c4180c011401502c1180c01c190346da80c1005140c4444201c2e00c0d501c51032403003130040c00d0018a2805030415001e000a40b5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 271753983 1250 271752733 271752739
    0x31b050304080d020301030f0201030c05041203180f150207080303070c0f0213060915140d02013c1803020a0b09040906020f03091902010f03020a0302070f11040f06030c05 75
    0x100c042000c2c0140402030343c0101060b900c0465807541c582c00c1101e44030850500407070009040806a1030041e10440c1550102c840f4070181c3d803450282e955040e0b8040080450030300c55001d0109000410501c02c80c2120020810105007500d09020f07800020308144003500107050951040050206080c2c1c0708002021103504500c45044421003840052500781003440002d07201414000041003501072540300080074120144070000d03017550780350405041010080c3c0a94400f02c1c200720003001d0750013040003c1d0320204009940c8032591000c0c85c0751030580c100030604045003208000403441e007908500600c80b01c2c041d104504940c3c0c0e146a0026011807524050500464030105482c002500caa82004074542c2e40082d0540d2900605690a20240c2003240c80f11024412401105002e172000c0a01140081e010ba60b6510b100000b118180c000c0e60111250100709903007000f800e004103042d0900d41980302d108040c49002a458031040009070b91480c0c200d806607138030304007082000480690b18981203c5040d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 271755233 1250 271753983 271753987
    0x6272306031006060e01030b0a1202062107080727090c09050901030b04020f0a141e1c0c060921030203040b120702190209130809030a0303050a0c031b05 67
    0xc004242001990550600c46034107240010500c60307044100c5080300c0100383da00300620b00d404010007140c0080c40c0310f19001084010800000350401900034034240f990b681211410704101041070700c900004450490008842006119160b50300c005a00f05840700703401600b07103003041d03079440741d002c0c1700c0510611045a40ea42e40440d01036008601c00c1000b84002031111850390781d2030402d540c0c40d0800301da00320f11441c550300a041d414500081390341d0a8038148504011800300d01740900032006407001d0702a1a814940c07203444100e5a44844482000480c140980c1c500c10705460580c401810540195003030028a00d4140100b10720a1048107140001d000d14102c10051030400360708610454000100d0540002882c502d0502241c58013405101a42e080310440548218001c0c8031901d0544025400000b000c0404d1240d2030b190f5088580b00e014400d52864441c599000900d0a000d070305040300807949a100700121040b441c8642008040541000c2c82001603d400810034014009012800c0c4440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 271756483 1250 271755233 271755241
    0x60303172e0f17011503030f08060d0c0305011d0f0d080c2206080a0207080f2107090501020f0d08160203070606090204181a0121062723 60
    0x140540c4030380100b1010b04008000c9484142c2c0c90141034440342c00c4100c540c2812100c1843d01d0407000390900302c03500347c5e99907409200c140e4011540400c1c0a040c03541d00010700320a0401041002c208540203601c174500002e403544100d580203094440314991017105400400040a08100c040f5020440c501e89240040b002d84c0c440841c18800e014107100d065444622640342000b90300070030900c2d41030361072507210126690f452403c80401d920900703000074000030301809200e400c20300c4500608031440650440249a0700c28035203050061404030382c03d01c002600c04108000d2560148044511920340d00042c20742985240d4003e450164060140c0a00048041604035070601c03c2c0141c40d849617100a050091702c2c4d5901802019400500400c150402c4a480417005440705101d10685c032080b4503044c0c048444902d0043d138803004507004a00030504a00c640c2582940300f0f1182401800c8100c21401409650b00700c05000c0100c02c08049251504c5c001200d00a03040c220146154080c041d800606a591 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 271757733 1250 271756483 271756561
    0xc0504090f05040b3114070b0c030a050a030b0306071d010503160c020109030803010e0121030f031a0415171605090414100e0c06130902070f0804060306030317 70
    0xc80203a250103005c2c4c0b00c8000d100304800c211180c8a400085170803130341142c2c1c69040d0304902e4400c00c100c8080c5a80100174000b450307800303500a01600003140c04c0004170788000c0c0000c00d007420703000c6030a4400220115400282d05007155104c846981003803a00c1402c515184071440c40d4510541d0080090040c5041b041c01168400c601c201e024513032210182e6181e50351090303180040c00c0203000f00c24001c11144039a2000c000c1c9581c1a14585d41c2544d41c0100f030342488030b030a50041007000c11800c80c02d0b0080034400c501c1c4d2224000e80140d01c450030100f0b03003c00c5c0b030f0508580c6540c07a41e082c40840c503040800449007111084542106441003101c12000c0781e101e501d064404514000350765800740c0524002d46400c883c05a200100d01c00b203042c00d07181c912440c0f0003080000c1c40343c8290014a0700b0080018888032010f58054664280b140c0140d441c803a1003529003074411b40041d030180300002d0f00c801c010302c10940d1000320f07180c3c0c3c03004503a50440a400c0484580686c0e0b0b06c03024007090615800300356281408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 271758983 1250 271757733 271757791
    0xb03030f040923040302030702011d060406111606050d0507090909061505010509150f071a011d0123010c14240403270503010c0504090f05040b 63
    0x4034024010340d5115030300c08400d0098802489030800c0d0f00412502440c845001d4182c0911036a4568040c6241003403640c01507569906590324020701b84041d500c4803504d61039040041014140b16211f005004021300e00c200d107040c0c4514a040c0c0f038114061010032100e41c200017a02d80301c41c1c640a02003510b54801800f12a00d01060380f01c07940e005c0c05e18030402e00f805165441b902d107001000751815481c54403000192940c2c85011003107034000b210349a0342005e048111010b001c3c4504052030581c5000c80304c0e101c44e804200c03460380410b01c1901d61070040000c59040d214410050300e400310013140541c5080d4818000807600213010315a40c00d146410803450b0712072a00d158078554041e201c0600709881d40b011540c3c0e01c045080103441e0003080819184030007230000116210707650507681c400c00410340e0b101e882440003c2051766100c48400a0005c1703500d641c03e024801880000d80e84181e107680c41c240a0070217071032440d00343d51000d51404e000d02000c01c3c01075070a107522001d80d2000419004003510607220781 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 271760233 1250 271758983 271758997
    0xc06020705010501030303050609060f01080a0f0605030304170609160302060a18271e110f03040302100c050c071406040306060e041a091506041d0105061c020307090b0303 75
    0x30b510304000442059056071000d402018242c50b515102c0d030b60001400f0240b4104031132140801c04003c0042c50809680d045082c06640110f070201d20159030790013080c40d60300b282c2c00c0b900b0303800c00112403080c0e04101044201d81c00b80341a402040440ca14403030354490b5200a00000c5d00407071001400c403002e6401400d80a0f03041c044040096070f03290307a515801d400c4105420000141003461483c0e20301501d0305018040c184281e01031108074648610100900805105042c60346180c010b01030000b1308008080614850350007038001c0c0014880c2860420115808609003000307010007440410418040040c800d8140c030900586121403400940015041d805998001481c540c00e00401140c1c654865040302d001e00d1103481049203400d120b0307030040944c4d641140c20200303540c091005068901d007582246908800080c0001400d600c0918190700021402c5860715120307034541c818440c0900b4030740c001100c000602d040c4040402e03904e0b80025101c050300e1061580d034a03100c42c08080b80e680c01380101c54803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 271761483 1250 271760233 271760243
    0x16090906060b0a0f0305060411042115050603071d070e01030e030c0c040c0509101b0b07030b03070503031801080a0f060e1009021c0203190e0312010b090f010c060207 73
    0x50741d510382d03030041469104d01c40500000781840041011428580545007900c58124946410907041030140d02c00c410441c07010b440301010000265010800300310310000100b00d080000328036880c2000a251900e44290f1182c1c1031020819a00c518444004030920340040680c61700c41c3d0910480c4004801401003003080314440d0000240305460740400294160782c40200380d800f400366085000043e05c65005408070f1540118400113285c1d880e42c820145102865140001d008126005803281100b03020110394403004a5034400c1c0c280d01601d0b04100b031000030003003280118901100d020a8070f008101702c2100034148110702010920400a540017040c1d0b02d800c0c1c403420480300b551038801076004201511000c3c1072801f05407020034030b6401402260746c03040b0003601c2442241000c86020000358802004d80d400355101c034040402d444614002d0040702c1c1c12180085480d03980142c5040000041a8044010b407401004038125a45440b40003181e105030900304404403481d64200388019200394500104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 271762589 1106 271761483 271761487
    0x1721060d020d05101a010219050715020a050a0812070504030c120213060e0105040e1b010c15050c0d18020d06020306130504080d0e16090906060b 64
    0x1030742c24030450494a0054040c58001c1c210394010400d01d5585881c100c05009030341c1d0400001c1a410210000110740642c00d5440716a0f9180522507440b0500d822030110300b0031030007409034a0cc85078014040d01e480b104d541c03034446901d901c004004221080c1020106807000e11481c10b650541c0d9008841ca64242d00700f12107000399015240b002c0703a10554480c2ca540702c108440c050f80b030052140c403010100c40e50408040006884c406103005035030b030348124100031383c100306da9a454034061000c0c00d2008400c2500c1c144205803841c00c01407810b01d507003032009000601e449a00200061030001e1010004100400880d0350008004400654005c40100c400300c0030654660003541c22220003044002c030311a0720b0a40d035040d102c0440d02034039152404602500b526400b40140074540000001405142030301100b0304161040794042c509441e6940d00c000701c10080c2c04c1d8404800742c44030950245e = true := by decide +kernel

theorem cover : BRFrame.Cov 271582733 271762589 := by
  have h0 := BRFrame.cov_init 271582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 271582733 ≤ n) (h2 : n < 271762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
