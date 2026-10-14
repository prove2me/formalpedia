-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1903
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:05:50.575436+00:00
-- url     : https://prove2.me/submissions/61072a71-10e6-4483-8e5d-419521db358d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 342086330 ≤ n < 342266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 342087580 1250 342086330 342086347
    0x16030f02090711030408030a030b01020c10030509070905040f0c0e04030203070209070512040b150d0203031e0f1605011b021b01090b1606150f1710050a0f0b090106050f 74
    0xf90f07a0001c01020340c4500000c0f8000c01e005400002070840c92800e42e9083c44452a401c0045e0313100c002001c02c0c43c0c1c001c00e4100c4004d0407076000c1d8001d150030060040c201e40c84a03907a8107003039086a00c141d8007150111040c000903c1070080700d441e808007400a0703224000581c2460780e4065902d00c14514000c1c003482c001d50016540c14000d2081d2030f036841b40440c0c5c0284504e05450b2404d681501140c180744800c41c07101d6443c01d1410003495440304268090001c4d4a0f144082425980c0403000e014000403180e010001010741d01ea009001e09541c000740c0961407045034151070481d0a41b0f4148e017081000344d00300000303082403075800120108006400c03a590740c41e054000004903a05100e94018208a0304000ba40a81d2038000300c21004000f40a110100868000e40e4255604c0191512410b074021055034000e001040b810116000b0140620045505000c9065085010341e18100e031041c103c0c558030300c0001c40b00c40d4140100c0c041074404661200240d0b050000140c42c50203403281249100001060300c50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 342088830 1250 342087580 342087587
    0x60c0711060912010c181d0901090f03021005010506090609040b03101a120a08030106050c0309101d09040c170a020414010f0b090604060c030e130e16030f020907 71
    0x100b4410700645501c0410b0000c070f00c1d2034080c21036140400001030070010040c4076030700810741c020159507121801c3c0c0c00781041441440300001d800340c18124555030395983e080000e00980017005015200782c02400030040008a948201c62059000e03d014150401105d00ba50307551340112409460200c0b4006804000e94000c64a00030aa00000d0850340c54408029082c1d04400344404281d44112440d48407240c1818441d501d07495403110082040300144014400140074a010f050741c00114400c80f4104501c0d0400108011010714018000c1203200ca120b4181400303042075056000401d854076a06406c3c1540ca4220031841480b4000e071040c0694951030b0044020320001b05141e400410038801404d44000c0042c41c0d40080c418490340c5054204000740414954080c0d84c92500010720749804c04e4600310041d10304085480003102040f05292032000f4a80c5c401103480c0d5810081400000c16004040310180303022074908100d0304100d0260300400000e03e01c46d06061041f581622110200c3d260a40c0a8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 342090080 1250 342088830 342088837
    0x2060a050a4d06010306052508060a050609010f050a09030203011e0516091e0b0a0207060921020f03010b10030e0c18042a06020f0708060c071106 64
    0x841007041c0e8540c008008071280b41e00601520b510181e1222003400d000c0d003244812201032600c40d4541100c00108082003480e440940c0c0038401464402e001c0c6080442011074101d410094001705040b08203205950404900450260030261082490052108000303442c6240c0d0901d2001000b000003449507480c1c0c8114540701c000c5501070000c0c040841c1c410300d0303002d11140444d07442200a1900d0000780000003406412002c8044c10b44a504c035240c02c001c00030aa41e141c01c0314101e40e458000d140003401c2481680240560040340e40680112402c3c07480007050ba007a0b9a100808041c900324074002102d032507054500c6411790440d85005600c0c1d0310008039001d88510740415030b0200d01c1e040c52100d421740613000a43c0181c15002a6808003802001704902c03800154600c0400d512090300160004403112545c1d41c4d00c1103416900601d00c03d50554042503d151600044010303040352a2070306000000f000703114044c1c142c5d44064880d619081181c45100d014021b0090300c41450982072020303c4d03c030740046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 342091330 1250 342090080 342090107
    0x90a1401060f0e041205130b0d02070804030b0402121b09150604031a0603070b16050f0105010b0a08090601060c03050a050706050112150501180c020c12160f0302060a050a 75
    0x20140120703a40c1182280c4a00300b213070251807820032004110009842902101c03000701c049488002ea003800e00d65a00c0241d000340d24075024040d400c1003603e001c00c401d00080e00081d44034000700949850640305120f80d0b90180395801a069000c0c050780000031300d1040101881140030707204428542e40c0c80004030855a60041ca413a0804400600403041c00162a070140c104420503080b1500c81c0c4586085c1551107005129640320b0600500c200d46460b08003c002d03903a160b0140382155080d045c900007140c00c640084e80314016881000418442058002142c1a88007030b44130080c2c807582d031414601a18040c450758004081102c00030302c801880b0700400075a1410f0b50001c100b0407456854907280111001600010354150000c046c0c000b600c910280295816201001031041c0e00003403a0503414060604482c1e41c20550184041d11100c64941d00b8000034540101d00060078020541440d241c1458101d41004005a81880d030500158580600b1038003951081e107005992500e0740b030021201150200007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 342092580 1250 342091330 342091349
    0x11160201050403020409110909160905130203060a0506100206010e0c0c0a060c0210180317062d0117070503010b0a051b0f0d031a09040c0305031b15090a140106 70
    0x44000520002e20304807e407110342601c02d0440c1c1d80b02d80400d0303580c8941c280c03000c0780821a0048107005100581e045541c0003418228849400125540040e041080448103e43c1341a520802c1000b2071410110001a401d501c1c000b07015694140300552070f0000001340385c00c02e1803200007944907094108201003505250015010032144003603581c02500c5503129820108142e00f8188480340c1c504502d418001c800f503160b10340c040001c40d064034000040070000e10407540402440074221558031402c41c1710b44404030160020500600c0e4100140005220070121545c003c4850b00b04103149401604681c1540c10034070031552119040341c0111400e1250303031840c081c41d00004494290f0303c0070016603040400701c000280c034402c00d902081101220410f0300001000c01250051180a0604e1403105400c140201e80394021b554980d102c040ca141d101a04010060a4148030107450f04e5003032003070300e1101d0b0300e0f502c1058560a140d10359a070348800c40c00e0090058174040d280a91040002d5000ca001401e4445 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 342093830 1250 342092580 342092591
    0xd020a03060c0c0821060414070e1f120509070b0703080408040f0e0a0e01180f1109040819020a03120f141306061502070b0c0a020405010f030213111602010504030204 73
    0x1c4419214800c0c1002190445040385c02140151909002d10700030781400c140c0245140c0d84824086991440f446611a0844254421502c2e07107801e280b41c46806000c2504c0d80c1040d054060030b510122600200742c07011540100c1428016405e504040b02c11443c0c051a142c503a64440b42448003107881198020140070481c1e0700c002402c0703400e40c003480e84130380307840702c41001048180c0700c1e458280da04403c41e01c201100e2480c141c00009540c1070180208902902d0100b060126000104120400a68080d1480800480e0303459807000c80303015100c2403075070b94405461038860a54018140c201000140c510554440c1a4030142d03842540c400358800c51642003031091410135810240300728941400035075284e420f2900c0400c0001d0391045001c0d1151450b8000d10465140062054403a008282c400b4424050030030a00056551401000d010727100c0d42c244418001e1452040120016400703400c0c01506007002c101c8080da000c3c1b0019902c06800b0301051003030802c0c40c1c1c0b0040f9200d1007240c000030361061400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 342095080 1250 342093830 342093847
    0xe04030329120d210609020a020a0519170304060f090b090d080108070b1c05090d030605040507080f19050a05010303090501140301140d080c0d0e0d020a03060c0c08 72
    0x20414900010603685441007041c04405030ba210f6402041440c0070400d401c4c040304281040086075680b12039142000620315031a02e04d8041603074881c404440043e44030300c00d1003050020600001c8403e20040000080358500d507603942c40301c101d0040c0282c001c02c10100000e020712119070400d4040c0d841d4000200299006c510f000c8044e24001c0e00d205600b8030030541307448103e60040d0380f140e040e10306202c02002d40b140380a07002d030b1403544540c050806201511f8401c1c0380c042c20a000322405580044090107058250f17401c010100c4031343d80c0c0420322541c01c2100788a00d068008a80f95009101041030310419683d0310310000389001150905544680f6040802402d607041d6807056041e80d10135601e9007030003590b80f4011201007004004020b24144204010804202e8080003107038608030241800021082c01d0316007510981000000c94030076048064030305e4019034040208525030f1001c450300d640500740d80d000b041100080d4040100603543d02c040d221030040c000c05025500079800310520b036644415 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 342096330 1250 342095080 342095141
    0xe0409060c090801020703080103021207080f0705101b03201b1c15090f0c060804052104090f020d110c06060f100c0312020301080c0910030b010e040303 67
    0x5034100100103010b40101040c0000103008490a40e80c141c0d9500c1d0b2140d00356020451070f950718848060b444d1160700f0000803014814840c40c803900c903150300a411000d1a16040c0000781643d22183c008011200c0800d11300011141d001d40030543c0c162034009081380b000007080c40b0805929850003014480e41520300e9914002d11441e003200c00c025111480a0301401c9a0300e540c81c910b1800c0240140031100d510141044250f22442c000781c018029401061a25200c27042d25100c281c11880c00070302e501d0100014008100003010f0b80469401c048402c4207144504005140154010b910300307240c544030307441d01d104030a8050300c41203503c4200c02c001012074402c03c1402d035484461500c020380a85230015099203002c00403a060508050112070701010b81080c05c403807000c4036034812400e00c610140101801195840518040c020301c4004013030700d200fa6010041c1802c0002c1050510681c02c404c1400060315031303803016044880240c01c00300c598407146403c2c2c0142506580f4481ca1310613806809000026 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 342097580 1250 342096330 342096341
    0x5060420130e100807090b06041707030b070f020114040b010603020a09181b020316080901110a0c0807171b06160803071b021807030e011a030f0a0309060f0e040906 72
    0x300d2000c45507038a6544502c4070644d440c606041e42e0200041c40308000c105002e05204121800c0d050903600c0080ccc6a81c2e46442503d408e440100020340340300710118000d90248603000c500c20340750454007030b289095030703d03a001d00005000b5541010b8012036000109805511040098022800c0c1400b2102610305910014010070307130412a90b00343d404196038411300100c11218107032001d00135a4212511522492440e0340011890350400a4041440e02e07020030a010008407148500241f021861404e03400c3d615202d65904140010180c071180d2202619000032229045044048103000199004001500d240a201c001110b02008606001c0c00c005400c401584074a109850700c400d0401d0119102d03110101c1c4036070081d0041000719030041113003040035129502082d507280104084002d24280d9085d1107001144109200103009014400c2c40e0510000800c0c0050200501041c940c94400034003418062042c201440204440100380300d116255030841200c010b031061026984c9494110b00030b02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 342098830 1250 342097580 342097589
    0x9050a020306180a081305040906050a320a06050a0b13060806011719090501021c020c06011703210a0b100e061308150a05060420130e10 60
    0x2c1c1c4030014040020800384412501d94030070040c82c1540007990303007880d0760740700401d0307040a102d9180c40064650703654000c4040e824481e04003c82c041c10000d00c40001c3c0d48a000d02d80000c0340380030005078001c202011a154212042206840c020388601c02c0b8000100079a40080d6040186c0b5100030821841d0500244500380000301694213003603582508490400c1c0555500d800500d10707110810302c1c0c031180b10403503800c282c3c030018039001d402071030012030b04880b400301045038117940200b00440030384170301c41031040c0302080b684041d4a80300a9011882c3c50350b070705009036884503410680d019502c010030415619901980c400d60f080300c081c0541e0313007445101c0c00c65120101d01d0501c82140c549042407004a81c0d100d4894407000760400e6000104071140c0c0118590b038101001800000480c0f92040080028111010b020010941042c0740780303000380c0e200100924002c5c1d0815009403500b10388a440002035000f20740e0810346441030360948405118141d403100c51000b00020901013680c0f8401400720485 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 342100080 1250 342098830 342098833
    0xf0304140d090f05010c061d070306050903030402090118020415080a0b0a03080a0e0d0c0605070b13080702010e03031606061e0b030c090d140106030b150a051504050409050a0203 78
    0x12580d181c0c045400c2c030464014240c640d407031040d00b0400e55000d1050014550700c04e810208282d90303861111802d0100608607080c40b41c0c0001402c0050050511510340c0103100300f8091440c0d0300e46034005ca0008103041c0300701e0b079401d11450500821b859003541a580900001003500340041c0014800911030b60080d102c50001603d410040c9a9501e4041c1e076003001c43c1d03805800641401c030500340a480d20b03001090110b030001510750040000440d0075102c00003505081d110350380ca5138181e05040da4002402403203400041584544400030910890070b41c0c0d034090b42440e0455980134528046400c3d80608034072440e0700400e055841d801c010326a00040b007a5120000017455201401d01c0c000602c401c548599540507400f000420350140c80b04005180050001d0610040c0c080b0079a01c060402c15911100d56250b55200414403c112262840581160142e40c0300c14041c6902070000e41e00d01003610902d4407900d08a0304510344c0312003480540f002440010400c20950b001d40c00c01e20b03102d62004404a104c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 342101330 1250 342100080 342100093
    0xd1704090501050306240a050a15020606010c030230030a0c030f02090a0e0c120103140c01110312061c0501091208071d0102031918090b060f0306060f030414 69
    0x54100011014811ba2003110304400703103080203851494006100031010340082a86101088580359443c080300248004882030604120210f40242032001c0980820304210070049040f020940c002502000345403032080d4050780000002c40e01c1c0710710d540d81008842c0048040100b100321a241d91008035542059201808030261041d81e01e401c07407045d14800340d846a8140410b00c2860170300e4646507400300072403458030b00d000c2194030400d1040b0750983c01100d210700c44600120204205000500c0713542e0003824032038800c02400000a849004200c81060b4100d4600c00003299030380c0f19408a1000000902d8040400b0040d080c0103000c4c001340c2c9001d64010780807030ba0b07840c1c1d254400d41502d0f00c0f404c00e0b1742c2c52a14038100e007006420074107003032802d042c111302c400d120402107071041146090728120140c840d00868049038680c42442e5001da4000030b10a80b901222003650745404084505507000140226239a5662600203100e9005129016500c82d4001c420081001403a000d111070b00041c1c030301103400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 342102580 1250 342101330 342101339
    0x4142113090905160e0601050d090227010f05010f050f03070c20010201050c0405030a0f030c05010501120201020f150606070323090a080f07061b2103060b0c1b0d1704090501 76
    0x45c907a0152080780c0021000c020700101e00c4c155034000362026100520b90510b901b60040f03014498084101045800e000c4100100401300300841132000030f03d07081c01c11a0b03845108100c0078009000d051030704135000000000055640c0d1040e040d6100055110282020705040c0d03124000091014401c064059031034500440c0d05400f6902c00d035000c071040100140a050700c50b554070403904505150440a00c0040b40c2c0030703400107200f030241e140030b85500c0b080d00d880808580002460100c08100c2d024641c0c001010118451440511083d0300500c2038449a136500341e5854100c400f417004014942c660751151000000c0701c50005e0003030800031001c540c00c5900b03c1d220681d40340c540400034034082e030301d5001a00030041640681102010342e03144e29000c0000d05019113414480900c1c058038405401e0321310b6480380619402d4803480c405070a034440400d00700880106050303611040c1c5401c00c0440038904075a201165222030070b14440c5c41d8824814840d01840f444144d000380c10a0298070005d0782040000704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 342103830 1250 342102580 342102599
    0x131e0902031c120606020604110d03051e0a0e0603060a1a0702030115080705030706050d051506070f03080c0403050a0f02030304030c0905010306110702010507061e0608060414211309090516 83
    0x203008927041205254141c101d40308004540300090390480a0140c1030040d8000c1c2c5100c0c07888600890320008841e90303200c0ca0100000c00f0501c41080603840341505009000040c1c0310804282e080e2440000c0450560741c00303180d1480d240c0110b4000a5040d070800f040407058025131042c0b10201c136100c10407100c010b5112420140c8034000c0d4040d03000015020b201041d410b208a800a681007103040c10802c480c03c942001084c5d803988010000d032150708100242c0c0b000c0545c000040b80c0d0100d000701d6541e04080c29607403155107413225014060f2070309061009020541d03400740226401140d2040304003800507034585046000c0c0030b0034802540c3c4145031502004200800100b12111503905948980c0751404680e210300041034044100000307100b83c403080d001c0b092000e10465015090142c0202160f1500d40791611806009071035007216030304140101401103d030350b6081d242c45540c0313000864a0320403488a644c40b148141d0312104181d4180001c842c00d00201040c0c10041d00602e010400b0095100d13a40038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 342105080 1250 342103830 342103843
    0x120204361a0301050f16050f040b18090a1b050d14090604050f12091e091906210803040602070c0303050406180806012d14131e0902031c12060602 64
    0x506c0c0145607401e503645550301c100010311007040700c2400c5070f0820752030350036a0103150818040c07030303100c5d82001020002c0c41c54080101c40d405829040d050049800d89001a44c403140d510560609004010940040c200c10740d40003440f40c3c0f00852108403451402c901c0d081e64400003170718240c0d0741b07018420454401890103d85800c0f040220a0b41504e00716004041c0a1440c06070b10070841aa48900e900c029030f95105103002e40103050080c40c0c5114540c008203404200c83e0a90f0000081440039030900200102c025107908195401003001600ca6866042c80b0000c3c2c407a034140204075001041c000f104168010020b00150b400a035500740c1042c151110300a04510389001d55030031644041d00401c065481c0707103880d644044080440040c050041c07004500e004d092508000d030000c000c401c10320000d040c00c01080489294202040c04000004000c401a902d01102042003598032510001c1c2592420440c040c00180406c0b49000e50500b4040018050311084003403a4200c0d060030170000340103100180e603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 342106330 1250 342105080 342105091
    0x12090204020c34052205070203090f0d12081b040f150c051b06040305100c140403030801030f0f0519021c03020709050403090b03100501120204361a0301050f 69
    0x4500004d042204000b01d202c84201581540e0448280c4040305040a010301d60040c21240c000315101c00302a02000111520810454080c004c01c01221010075901554419841c0d10f9007004900d0341c0b1112090802c40580002401440f403002800103000001c0b40110300456403000f02c0e012081c03405100c112180369095902406542c40049500c0140b003002c18580c006400c0207088604d05944c0e82c0c0c865047c80101502e0500e541e54030000040f0481d00000e1064885a80000d290724003411a50041c1a010040c00054480002882140704000d6091540203400307030488125140ca21040c6c00b50074292040b400c0403402880e070440c1080b4480440c9070640305565254014142090038400003d004020007403086d070800c104500300046507030300c0c01c0040d4080c50003031512002030f0341004000340900726101c0840006610420007080803020840090083c1d40460001d041080143c00c42601b0000c1d001828509141c0342c4244000590a04a81594180d40a03002800a41d85448a080d0b90b004111103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 342107580 1250 342106330 342106423
    0xc010503040f0b0603011506030b03060a1b05070c0e1303030e0303090c010c02041d16140a0306180804091409030313020d03020f120301090b0d03090612090204020c 72
    0x219100007083d91102c0e5502c540050000904800d90503480503074032240d82d0005003c2942c03109002070703a041c140402a13102c203030020280080390005080c00d0051a0158060040000100e5800704000081800d08010140c100c0d12541d2130074190101d08c40b070791051000b2004246060f0b4020303845900801034900c01d0b0041c6019200c03c220301801501d130231f031207008101e0340035640da08040180704071000e68040c0324680b0700041800246400350300094010301c6e0400800010740160301d1046540c2c5030360140c1500c0d40180082421045251880c11089542c00010004500860003180c400c10a0f4000902106400174810381ca8a0744d8580940380e100c00c0c2c40c1c0c2201c04605400030405400d0140a040308c01d403181c4125111100e4030815030341013050841c0041902e070400801044424501c0c014118854801c40380c4000304641a0381c0908012542d210b0360701406503400d402640608103520442c03420303801810555882c1c1c004032086486010221078060240213030360800d62208100301c20b20038910034158 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 342108830 1250 342107580 342107603
    0x80f0601270212090d09211401021603110c1c02040213080120040302100e0a03080f121f06210509070305010c050f07061805010c02070302040e030c100f020c16080c01050304 76
    0x3402c8687c0085031000d8607441040c00c400c00c000e880034401065245c0d480008983d1a004a03d0000c1044000c007410b9840d582c482511000310f541c1d00b0382d0b03c9404100100e0a40d405503220310115012f03004890026250400c0b0000c0051104410b401c0080590507202c5011040c005072038404140d40200e00000e904001304054000c1e00c2409010381c6029a140100303002c20b01030362035488182c40d62280400050035100400c8a019030100c1c64280364000c07203e44900000c500e05134090807144a400c1c46040304116101260031b045a41068040100c42c1410406101c03920381705041c5a80c90070644021105580f81415a45220b0300c11410f45d603c890300b084900d451f20055803030b410090400e442c00340c002003010180800004009120781e100002140d0041d03d038562440c0100812241d80b50072410258004122a0f0010303100891144020840104005207900414a40c10000c2c0980c00003409181b091048a03c0c2c040b1400000740c0c1144c1c1c02104484203d0030400c0112000e00007030b03500400b50b41094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 342110080 1250 342108830 342108869
    0xd03080a020904140108031317060f07090f0303180905130f03030f141f050112020c0c0303040308130902090f060a021002160606080f0601270212090d09 67
    0x3030700240701e039a10080003c00c10441004451a412000707034043d00040c1e1000030801151911100407400400301102400f0315403040a19040c5c031840010711270700d540c045d944c00090300d660223100514090031174041041515500c91078064080800d46180c5014a047c070400018480c91030301030144950359501c2d684c2c0c0000c40503a2158110100c0a80031428180c403102d44030316800343e5124055594141c840440a1414004200120139420240c482d4012206140510141c2d0700040c8207141d40d13812013401a41c82c0f1501180c1400c00c550401413a030716000004001051107400d001804000c2c0b0096803000d00d00d40d032a03d90b00201c4c8034550b00540c01110503012104039103002409400080350703c1c0183c0d0090310303a80701841c040344c0c4000780305800d4040c81c03c02201404603503c61040a07012042c01882c0a00e0381c0d050896440b04148181b141f40199080d00c51842e41b072041d805010060110b2081d921400342c040342008080b0111440e05070b5120b07020010b0180ca202e24410421142110044103100130a07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 342111330 1250 342110080 342110101
    0x40e010605012a1b03030e03061006110309060a03051e0402010207090c02030903010606020706020f071404200a0f0806060702130f2d0b060c03030703020a1b0c030209060d0308 77
    0xf0740c110300101540c00004070000ca8071550040c9500d03680d0f00900b414072419443c025010102104059000744d0040e42041048401c80d00d000050310510b0900c6044891440c02c1d180c950700c24100101d8201e02e010444008444d09a044a800f44900d00b148591f622001103002081c054200d80103801070744040f004001e49011940100c200122510640345020003002c0420300351038180d4403c60040e40084800c114803a81170029201581b5400003824803d490322052403445484601d48600c110b03907480b4101c0d500c20f54211282130041d05000c02c01c1d00c5020703181d07010307110111001c00700010403a00800644070385000c1c0200e50b06036900030001100301030701d0b941d003100400b03c110f90440c0d1140da0310645030300d20b0110603449103030000000005255025803030302c41c0b0a4075007426155004203018421a00c0b82007010003560390086140c41c0050300d07610742a1003156400e2502040300080d07003002203d1410701942698132010b41c1d0090362720030550384583c001c0c012840a420009400a0800000310310345104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 342112580 1250 342111330 342111377
    0x7020a052d040f2c0312010513060e040b01031a04050a06091407031b0f06020706140d06080a0b01080d0c0204090807050f0d08060102010902100503061305070e040e01060501 76
    0x80280000841100c1c000c8140102e031024110710308004900724004404d1129440c44100d100701d00c2c0051800e10b242800c107081d55084c18000c4034803802101c40c0025107010668000310013048030303160544942c181401c205001c0301c803c1c0416241010b0322041c0380b940703543c1e949100c0e0180da801001444840c0c0c0035110b03031004155154003118010215002000341100400081019500a800603011000148101030a03440b40d40e000c901a003800d10003c0003840d8020480600b101c90a04041101300b44800206142c4d11802c4100c1c100c403441c0c40004280e00c0c01c002914405a8401c903645001d0b40d80303e00f0220350f10b2070000e2408000440344001c450043c28143c002441c207030f200c0c84107641007100a0b41c803903041041c4c1440803480c40e44008140036115a2002d102a0040300030f0008100d4503c494011039030b142410009a02480030000c08210103448101540c2c4100c10f440d4801c01a50500c408014a02c1140b4071515105905000c080c001d514410705c0f440d021144141c490760841541b80ea103d101800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 342113830 1250 342112580 342112669
    0xb07030c0b13021003020a03050f010f0501050c0c150c0105060d21050c0f01050708130201120c110d12060b0903060406051305010912201b0a05031207020a05 69
    0x6400d001c0700040c1c8484030400c080b130030035450141c1c42c0c0072040d00c0141122002800041d4843c8968010030140141083c00d00a40710f00386041c0f40d45034185140c1c103250035020380d003c6800008119880841d0440750340078111807020003009000035103400e401c00ca5484284000901030105408840c4c9080e0402d0244213245107003814201d08148060101d54148100d0112003c0140d448204003c1c0ca10f6201040550000b16152892603045984d00006d03c0c0000c13a00d40b0220540d0780d180300c1045540500e400c014a4401c1c1e10031110800f28009000740146114522104024103010000c10105225810b13038841c04405401020303140d0382ca03200c640c0502009068544040c81e84101900031074800c0c0104480c1d0fa0144400d0000003001c0e550040c0244903903c2160740d00750003180a1400d007800450b0340b000380c090901200a049042c080092007029039580111381c18880ea24003204450b40c20300c0604203180c002c075901101c107913481080c0003a0900409403540b07440c2c590811100c5103131984c0380e0f00b005403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 342115080 1250 342113830 342113851
    0x9071d1009030803010f1403120d0c030605060d09140a030c15061208030f01060503070509013006050a0623030714030f0f160c08030a0e0312010f0b07030c0b 69
    0x9642d00c2d00e0b010807640c804e8006414201601030244003451400c0317481048804190b000340328088100900380740742e000e4640c0c00351034583c40782c458a070060700c2500002c0141c040105003658445401c10754400500c02287c04882c40d17081006034548110001ca043c445090b056150495100e84650360000001420700d07103204c14654070207000c03400800c0c901401400c80c2c41001c0503070b56030034004410030000905030b10800070040c082003002020b03a03200040e5440c0b0842030900400f0150b004d42c5405115480c51501071030202d0310074400300254202d8100c103044800c103480c846002512170303404940000086000071003c86d8a44110107001000500031a4403000d20315005d035000409083c111032640c826100c0d40c3c00e142c1000280701c2480b082c1c0f03a00300d030000c010006006000440c403002418031080343e0000740c9501c4000c40080c0c2c1c403a0319500701e4092119000d046c0d03561014000307130341641503000780683c11402046080105030303509410100c0380055050307202c2451601465446248105e0002e00da031158 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 342116330 1250 342115080 342115097
    0x50120070b0a050714010b0d081c02032e0e2403240a1a01031805060901050412080c0f0a020307020301050106051803010902100c02011b0302060609071d10 68
    0x722030300d040540380801030360b0b4a0541c1c507029414a0304462400c807007501c00342d0340b500c00300710303110b0b550f0203007882556502400564588920110500d0144411148066124000020405006203030621400c5215075094442c0c6134031300c01c0c01c040301c10040c0307401a4035020768140c02003002518400640c000c482c0124a081000018400101c0d003801c4241c2c1800c0b980d00308403041d020351041124400c40d4400018a07040040f5440fa0010003064005d43c03060a0616584070054001c5810140c94181d0454000089414900341200d005000344401c40c4d064411501a5040001081c0304580d50b42c0910100358010f41001c024200110703ca5100302106015031000704120b40068400307000d2b0030b00805854039195240d0346121000c0d4880480c0200c002c0c42640340c844003900580d40c2a00d000003001c030341c0c84c0c01d52901d1400e00c01030b035021031f90800c0102c0c1021a4511181010748c00114540304080950300c060140e1160ba40940301401595628000101c42d40c0310110541410703505007031440324624007003aa = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 342117580 1250 342116330 342116339
    0x50703050a0b041218140307031b06020c12031e0910030b030607030c020304140402160807050d0806091303021f0603061a10030504020a1d0601020601090605012007 72
    0x28003854050125820b103101e0080005100c2140c0a6020f540c01500340030110042c00c6030420361180050050301c03002d502c1d1401c8040c1940b802c1285002950b880440d086540c10040c5651900d1103003485008014412006044482c0c00c054001c0c400020b1914015400c00c80201040500e8820031b030007a1039840c0040c0b0000c0a2555540c20106841d0110b0b01c0002c2c0803410b41c402c1c503080c220003c001c41c09150426005000559000040b101214664a184151048214000f030003a1007502d604648841c0f5000018060140c004001c0854a00c030f00c04440c45100c103484281d516503000c030340c400d41c0300324441c0010300001101b0081191862007803060b20b19031850451195040d0706800d12150125a0342e900078000c01012340300b5800610b104450b000440d040003000103a14a49060fa0a03041507100c8020408541f224101100035101c80c49242c501c81c3c295001d40280003404440050040c400c64000050081c2544200c400b6954181d50324200c0c0c40f401803559003800c000398500c0311948034000c2d0008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 342118830 1250 342117580 342117583
    0x180209090a0b03160b1b0f071e0f0b0a0503040201033b010e0606100e060708030403030516050a11190b18150633030109180b06090405070305 62
    0x2072144a40240000c1d00e0040181030624000d07403e1010381240030111004d01c034006456081d622640c105400c0d0300b00d00c07860020351605040e6207000103e406c1c4514040030410809150313071000e10000d10403208061590f10a450300d9003540030701c60041c2581d0f041110341c01c611303c03034401158000d0040c140481c030449011035441e100d800c500300010f240314803440c40b80b905088a00909030000380e80e400078004a10b4114039a80c80d00d4000c0c10491050505d1075911140720301400450701840e01c0180010381340d2001782081c0140d035008030780c210001f915010000e41c12407400d042c00d00081c1e081d66a210b0515030030f0030084d1010358104042d04902d200750201490741e00181c6071205a958400c4a034900746042403403100081c40424411090039800000070343d07800c1c0900c41000340d4042421101c0c0002461035218095184c0b00748445031a10042030320864481c007503501d0040d4100e8149510400c0301181d42c51512044950f0220010310191025010544a14100201c180c005014400f5600141d65039501d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 342120080 1250 342118830 342118849
    0x809090901061814180f01020c0d080604150513090b010306060311060304170304030903050d0807020d09060c0f08090604030624123017010f03020a180209 68
    0x1156980d1903030070070703c450400a50110140500c01200380302505541070091300c0004000e00951000038081e6903446003150070806007600f040d9100c001c40d13582980702d0490380c5506429000f9004203d00034040383e00c41c14a4411043c1031702c0d810a407010300b282400c0400465102802400c440c060b12081400e000c1072000750428004d622800c1e001424603d14138110790076491150245100e9a828001c000c045141c00b4010b98164106c802002d90b03035a0f4516007950201075540003d0524454481d00c0e106040d00642c01c140583c0041c0c00304e0350700e55078209040b21034082d9030003010005180380004c030300042c80304020368441c28810b00074582004101400301d1a250020343c002d8540d59142e04603890035003489074402201202c10544035081e1400d1a807052050860400001c00e240440200030900481160711b50000150688560f18048000300700101b0040000c03180d240000c800c200005034100f002c0316030b1000c03241c0c003403c0f03699214038100c404075000d00010007401e1500c0d02004400c082d5030300e060f1079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 342121330 1250 342120080 342120091
    0x20a0203030609060f06070f060f0204090b09010b0f180a03060e1e0c0a050d0c1a040303020f07062109060903032301061d12100504170a1b080909 64
    0x40d9220b192800400801003005000c003401744801c198400c4c1d85072140421200c1582c1c0184c010007600c0410b1030701a0042c80e00954641e4030510102d0085400c0500ba042105030f5442120010b065980b142981038140c810301100300c0c1015410001182285603220301c3c2e107440c01000346a034100d56a02d899080aa41140000076035640145041d02c1031144000c0d285058409404020030701450400003080302c0e40c1243c000e541c8680d4001c6140001c002070651460090000a481c502502200400041454200340011409030107041c004151034100065000100c03225540c1d1509520311a06034038000d45043c1c010496419281c900b0600032880f43d015400881d40f00b5680040d490054605010102206402110640007920010000542d00c050002d5241c51008121040c2d085c050000419580d039518202c0d03598011144254940c41c000e41c8150f1240e0b0203a601c010100440050841103441600514404946815040d1a0701c074890a5a1520309100352405480e201c440340000d103000b40e08aa0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 342122580 1250 342121330 342121333
    0x903010212160e030d0309060209030f010b011416020d140607020a0c05040507020706030e01090b0412170717070306080102070c1a180906060f0f04061e0f031e020a02 73
    0x901a580190000542032400b281c5003c124820b00c1400190700d80c542c41c1c1d203100400d070300d5000d800700303205895045034101000103080319184010900054003030181f05001340d02082c0c0801e50900c02c100d050003228021041031b42d0104041003290f081003022a00c1480039035440000240300c401b40f000400c1080d003e8031140e0000c02d01d082c040c0c41e0243c0c22500d543c00482c042d509050522a06540004489090320114240400da02910150a40c010441013401070802c061900a02c400d000d0725040c0e90520b4070b01540c0711031840d41300d0804202c070000242c13000c0380001c1290949010300b13882c05203141e80041982c41e021880c1d56481031503130b0a98016030021386130147c500700c041000003502c081e0421148000003c46041881340c1c54061102414204042d000313800c0000010619642c0004856103540c000260584480d00003510308407540003030003a400490300743c810300900072840d60700c941c04619403a5212405d01544100c201c0240c05880a418000020186c090210064500150500c800039a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 342123830 1250 342122580 342122617
    0xf0a020906071b09020403030e40050a022a01140f07080106030e03071104090602070807050c0306010312121b210504031707090e0411040c02010506090105041109030102 74
    0x900c540443c08076902050b40b40381304010810000742c0211900301e07800d0044445000e10711460500c000e41c4000c0c179401c0492111403181c3d0b2000346441521210301c55124000c10065a9140c560810880c880c1205c114152240000c2241082402c0b040072420b9031003d00002c00c40c0c10410101d806000001e0300e050340c003c5640010041e80a034082c0300389005011601c0c050244042040306aa20b0f8031440c1c0001c0c0020302140103a0704551915004080b6042d270000b030031950f414081c104030400b9009034100301c64901030715401d22154074000a049058940205149200d050b5680040d610010544145100561074000001e001d00c034000100000107040c2c1c6818600002000385002d15580000b160408140381c00d0034440825400307076541c1c641c0c1c9200859156542c40e440307000d40c1c60f0320b01d0758810482280300e08108000c0040c0c0c28002800140251400d200e240c441000036401d0341c90131207210380c01c440311000400291500d038102d0130720b5183c5020746030300d054a10340100e170990f0301401c0c20a01800c88103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 342125080 1250 342123830 342123863
    0x31d161214160914060f06090d1b06020f031317010f0e0f0d030608030307050a120906020a08061e041505040f0204030201090501171506161a10030203060f0a02090607 73
    0xc4c0503441c081140c40100c1d00311842c00400040b010608141e090340620f1005c00d29001c2c58603a58140080780d40c000403040ca0000c558507001da00d4810a0207904018014504032308003a103000004e446850040c0d00e803044200b402d00e1420718814400301d00b545202c0d0740b04e07001c1802d00c003110b11580c041c0c6074101e40648201e400c0c0c0700c15280b802d49003d82441c20545411810485100c0c08420341e0780050192070070540d90800c1032411a80700420303411204c4454136100c038540801445500900c61080c20392583c440642d41c0c001002001c4100c05401c0c280d4200e01c03707000949181941c0315032462000281e02d03c090a071184045070843d100002e1400358281e000500b4000d541e044401900280003d02c1c02074803c100c01c0040d030956250140529609052140b140c1c00c056440c00c0036a810782c20079600100003080c0394103102c05c031a401c0d02405000a544100800c414182600820050381d40140040c1743c1a00c42040c0c81805c00c5004140d031011940c2409200c100d030742d80800501b10980111410106042d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 342126330 1250 342125080 342125099
    0x615030907060e030f03090d0302011b080405070b03010e060d080408030f03060406080f1c41090a0608131b06080a090f060506010e10031d16121416 65
    0x640b150148a544000d4400c034600800008642c7d01c03040603201d12200060f9481c00364050308541d001a0708040c03244d542811120b0388081424807072400781c1c00311590141e403694005018070080c094403003c80ca1000000c1c2c036038104445c80501c400d2040c11010f26281c2c4d14889142582c100210507808140000144040d920706402140c028050700d02c05814102c00c1004802e60340d40301c0e403e1203900200c150840c071410380e004400300560068100c50150302d00300740d041c510210340f5200c4114114042a010406090030f403007401c0e15010003001e011a01c6460421034291090754000344028030203102400d030140014240c00406480e103030251008103519040c000003801208004001e868540d1510103000701242d0305036000c55209420040014007902e810004860b2001514081c541088221001e159440c0e4541d02c2500701e24031a03500c15110240042d07056440d0901e2240c0620710614501050001c0f420310b1100c0d5441c14030581c01400d40031a0001864100301243e91541c01200903800f04000a404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 342127580 1250 342126330 342126347
    0x1f02041412030901110a08030c070213090302060a09080f0a02030909070201090f080304020f120f011503201306080706030b0105091f1206030c0303020c03030f03070305061503090706 80
    0xc0464401c0c03a030389080d00030716a5030b00070190614104400407031450032030030041c00081d21503900072103490f60301d01d00560203048541c40381c1400c80c0148100c8140e0100e20030b0922403250300d254035a000c2e0001d900d4100b810b00c040c2c500714074113541034a401c100583e0301780200780041502c80c031160060b68454022204004802c80b0081c0345070103590400c1141000903040d840207010b0185d02c0a1159202e84840c0081080342c04e0303500c0d00c56000320600c10729580320000060b001c60f030300184600a000850f120400c603149902544030050240a201003820601c00300000c010034914070240481d4510400d009a0109544084c4d2003039070a9082600244240307503050080070460343d001c1c01c0081c50f01c13142801180f10028038440c00c03200804003071500d01c03455104004c00c00c201d0a00701403e22a058407400d00411440042c8011000b511278818850801d0401000392610000060481d40c00d40c0daa000094000d0b190041195900c5000c0094000031000310b80003540c0510b60312402000d5650520002600c0c2c0031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 342128830 1250 342127580 342127619
    0x415050106050406121e020d0e0d090e130f0203070e040606050409020d02010c05031b0303060f011b030305042f011206050d061806022113030e060c1f0204 68
    0x801084140441600314a0107140e05504840c000307030341b1200d400d241c01220400040c0803416030000600c00484402c90300201c808000c2c05040c0c60510f041c02074151800c00161042d0030410580c0c0e40010302e040481c1601d1020702e400b030580b8038034182480d8002030401030650800d10040c0c4d440b605010030b100845c4505800b400b419a42040032a0a680000d00e000740103a400a04000003040e0040400c0703401c0c000d94104002c00102c144c0c54100510403140c4a4001307c4525000d603000c0b0303c0082503076105d59910344c02865040d0160b0b900c0003040c0c4040740500382c000c1041d100c000c400c60b60300340744032241c14011701c20880d40a801c442800d03162000400001e02f24524100c880e050140a002070b55542040341c01055000500140c2c940b2095084460703000d072840007900b00e510204020641580009140381800356010354446113030360358a038400c0b04030344400c400750000d540c0b15996541c0382042002080d0f0000010216250250701c1200b1490800a2140e0903040b181c02213400c11100300004441107542 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 342130080 1250 342128830 342128837
    0x50105180a0507021e070311030316120c02031609050708040209150d06110408061e040308040503070b07021e010204080d0509011404060f08280f0209090415050106 72
    0x280c01884520420140140000030b6940001c142e1a500810039811700c28075650701c4000041c1207207a020380300d00481c0f1050391542841440c02c6420302e4040101e4910396402204007440c00401d07150074a41031402c034000000c0c0040c1c0070640c400b603a820412a180308981c841908100c40c2046800f60503140050802c20612080c0e43c180401030f901c40c0092a842422443d800003540309403c0018159070354854080c10356403505912b50344004214005005680d04041150a230352540200c0740e881040000b038070200c2075a4000480e000078031441d0031503080341c01001128100582910f490070809000d586080140c0d20182d880119503040000a0001d2100100210304052401c885144c5462904401d00d08128001a02c50902d0780103181c52154200c0e0711600989442c0c0b9000040d18001c402444440800c0c0da02000403020b902c496007071245040b503100709054070071004110070043d0442904081003070340c09002da4005921078140a0b445503024060600154981d6240041180e0040e0000c2040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 342131330 1250 342130080 342130099
    0x15040b040b0904060f110c151b040302100302070812090c063c0408010618020408030712091503050411030703050613061e020901030c05091c0f02090f0901050105 71
    0x201e0792507610b51076115810540c081502401c0464140040c01e2480780000000d0000c251880040c1c0700060304100000074190845c8113448000751640c00c0590303c6012414000100000d20041c1000440c2c041012403d0501504019284c0d5955545820905c05084425044010405651400c10004403840810b4070210300d40a00440f11095201f0b42e040070141042c41c05c000a040d01d842c600542e81005c43c14440caa84564807038517514041c028510070050381101e0070a581500007804e10881e0b0850b86c0d010021894014640d40d140301d01406441010300384818600c001400c0e0325240e2036104d140c0c03840e5500103480d250a20b0034112850030b001c1d040c0c1c002e901c400c0c2d0901c00a070f4001021908403008200342c28a10304070380b070503001810550781d0007220019000400c4860107403d03009000362803026281800001c480c1d882c1100c050080c1d9101940c009041d0101403020601c040410030054000c440c50311000e40c03150042042d420040e907442c0020700d055010000105420301c00c0302c7c050001100c1c564071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 342132580 1250 342131330 342131351
    0x9150b010e0f0f091306050105031207061e0609092a0b0d0209030d030902120a0309140103020714070303090803031510020a05061006030c050405030318060d0515040b04 74
    0x1e400d450426042c000d07524240400c141e55203410509240d814001d01c03005503440c0504060f006400c010740d040315118144000802c15181c007140305c1c0c585851850015050007565125027028020a4cc4124042c09410344000c052042c43c5c0181406402c90b0600400c1110071803070480c8134a281001904004070810706100c92131005908007000b110014141c0a44480b01c4900000091042c10f40035941172190442c512401c603050f400518009000322108441c6207001ca0066441d81c540f018010002221800e00f030240c141c03032010101c4414018500181001107554a4003104116a8107400c200d0348042c804004040d4002d15020290515102070342c15800c00f058000c203490490711074580b03c2d8640b00d203900d400d28820404440348541000c100d42050803c21307402035911a883c02540e00090504000050003405003046808666002c0c008514081c4002c100407d03040181c8400c6500200802c00c504000e1a2405014094180300c41080728103921501004100c400d036411060042d4100700e030380e44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 342133830 1250 342132580 342132587
    0x32106030237080d080106050a0c0318050306041109010b070305190c0b131b06090515040e0a020c0d030902060d050a1104140301050106090f060f1404030609150b01 72
    0x148820441180c40c1261000742a00320356445004503560b680154030b8100040b04200010700303002428407501d81410598880e40c0841f01e901c0350320000408221500341c1a00000d00c9803250342e100400810181e56090f4542000034206002900d0a554444441400c84041d1410b150903078014000c2c1c9540c1c43c600100b950f4007030504d015125510a204100c142d0041e1102e01604980340c2071503006e045200c0500e098102084203280742c40041c0c0d402101d984400c4640402042c6142c152140c5803201c0c40741034980300401c03000c411036401d8107203c1c1c1403c2c4030019420000b11401800b942e080c0c2030240c0c4820890070390b145055549203d0030300701400c3c01e070310030050380780c0108596070300c200c8600104040d85e40c400060060140c10841c8007440c00300040c0003558406181a045484404034000d001599951a007110500c0c0d0f28001c00e02c100307410000c1000610b00843c1d100c07500c1c0025040119182890721201d400c00d41040d030055981d9a12039440c0c00030091200072280000c1421042000951080d90009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 342135080 1250 342133830 342133849
    0x3050105130f200d03020a0606090b131d01020a0c110114040603090f0210020127080f0c071508061009060f0e0109152111090607020d0f0321060302 65
    0x1e064010180e5001042c000201c0890100d010041d1280103546624500255207041f010713800c0d01c1c11454158041400c101c180602c424020004040380c1c4802e44000e20007009003030034401c945c2c80010500b00503e08800a0002c0c1c2201c4940381c841006544250524039500704441ca00507040110160b91a01c100424000b0f507015070310f0900e00007035240850b00e003000c13160205905c007030341c03250745a1010200240e054000283c8c4c038910f520320701d081050112001d5405072424000502c20341c020300101e5a4031600714050a681001501225401b56407444048040c01a440c0950300003001d9000300b10b4103080c6841c83da003441c2201c9c40e0501041c0d142c2200240182d100c0181c40d41004031210720004940e01c906010f4010303040940c50448000c0507180b02414280d00207043c00c4c0340e110400004010403d46100303020242c40440c840b40e192510b6071042040075400040d040f0b1b030104581d110280807400c07031900c2c034050502c2505d5824110208800080e80100b40540080b11181030900900040c0c8480ca82c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 342136330 1250 342135080 342135083
    0x161a010614030f040201020313090b120a05070905190501060905040b030a0201020d0f02240403090b030f0606070602071a0402131104030b0a0624030506040501060c020906031c0302030103050105130f 87
    0x243c124907103c0f440101d04504c1130b4410700e20250194840440c1c12032380382d884080001005c540d20704840d03420381c81e181d41b10000303c0c002503d175030003807942000022070303640040d50702c2100c226001090420920002041703410030381004c00091071030318081c0074034141b40c4103220114608400a0a40412590000b555100c0b4414060200002001c0700710420380208184207840e450740d24003402c03144807001c1984507004110380550005500c0440028805140001c0300c1c001c11001c0313000c0c0c599940e00703000c2c065164402c950460301c03181d00300300e00300c0030171000003405203000c50b00c200d65501400c0500402501da60b02203201070802e4505291002d1070484c0e0402c030f904a0b03900c207040c1812079981c10420402403096510406d4095620700b0a12001d221200400c1c0307074544030341c50030486900c8040512003110f00034007414001c10012022807001d413a100d00709940c8250020200c40d070070124000c01c61401c030042401c45001c070340c010005100b005000e0041c6540300003000100c859020303840e202c010108071a03420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 342137580 1250 342136330 342136351
    0x601030c0306050f220c08061309030519020c0d0503340312020405220f0b09040f060f5403020a0218040506060a030203030f0f161a01061403 62
    0x400082c090401002c917101c083d02e08000300a5046109809003984c0011101d0070b200704242020342d200c4a003141b007883d28040d050b60f00c0714100102c00c0c0780c9011200c00000041305500c00c2042090f15951080100152144544055516400004101d14440580e41d481e01580c40281d0140440014100500390b071198051912140181d02c140500009100e16080300e83c0203c07110425048801c21400c11081340d0340002c03001c0054040b1200160202c803020740703045501482490200c3c0c082140030340c800c48010701a200c00252070441408400840d5105452109025000d0004041040c9146201c03084241201032141031000c10389902400f6031200e01110600c1d01224030554107041c401c00c44445c501d9405040c0500303141e6009440d008040f81102c003110b803803103004001041d6040134009801203ea0250043d030400f2314051060350250410300700032500300c0007800740100e0700104120060215000301e1580d69024007041c180754500f407058100000f80300840010b900084100c00890358400724640 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 342138830 1250 342137580 342137599
    0x9060a06020c100e040c020703050d111228020f1b0907030e1509010504140d1e0e060d0f05010b040b0304080a120509100614061b0703020a06080601030c0306050f 71
    0x10070b54002c9800362425400ca03107008244480c86d0f070001051400d032030040d41107814071a040c00086844000040305151960059005100c500801c200986040f40651003116142e004620303805402c0040003402e900141c1c8217501c5900410b42c10320015203c041092070b032300507142002c0b0200d030301400090580d008060342c45d409220a03210034418030001c8941000c01e03007085d05014000c2070203003006440c19a801c4881030048401c0c4200020008460030b41502c5c3e1700140881280b031403d010030039900031400c1c0403a800041d085a66070000a010840c02400f000a0440b511002d140440700140c00c698401c400c1000207102020018055a03401541b0502c0207a071518000411120f140302d1124440701d00c2e0802c014000c0d80030000c00c1000f00d040d041c4000300b096030755914460b0f107010642d603590b5400c040200a400140c07122048028416030090f000c466415982e50b000c285484015800800061200c800f88001c541c2d06000c1c0c070401441916042c00064241320000341102c0c07031514244e101c1ca40e1903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 342140080 1250 342138830 342138859
    0x150c051209030c03030309150a0507020604031101021b1006080d021e0c06040314060a02030c0a0804020a0506040f1d192408010204030605090d05092209030e09060a06020c 75
    0x3c2042458250780039082ea5180c5c03d01e8504a9070310802d4022042c08403100c00000741000c415440340510401640d030060072252200d0310165804020740c0000503441d50208080c0c0c01d202c0c4040703224011094050010703e55948081540021504182c1141510340c000000c100e04040d8000b68442c12026103280310aa01c4851480040c0780c4640c900f0b0482c0c002d080400c0010a0012003141d048504ca10701d400d4440541d0307440b90000884c07204a50390001d4400c1440240302c04d911400c800d5038031610241100c440e0f00e448030006540c640042d4004488103003805010b10010a06d204800b06a40565003020b0941c1400300402c0c0410803c0f84010004640e10030b030620b00d03000d440041100d010500044001c4d00b6442e05c00860107036011340025589541003501040d07106000007011010030b4995555030b410320f4048010003040302440740c0c2d4040400407540e480310743d40b6075038821000b0042c0701c2d0303d1314024034801c0800d12032a240010400383c071036100400d00300400f84e000b241c0c4c095094822076041c2036242c2e80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 342141330 1250 342140080 342140083
    0x41505101b05060a0203041a010e1b0f0408010903120902010909021c0507091a040b030f060312120402010305070e0a060f0203070501140714070c030201120222150c05120903 76
    0x10801d0203855481240207100c10f8810550084d13001d140500882429180600d10309a2841000e110b4501d0000404000440c003d210409410074502d8100c501072400c0341480512110f80c00642102d240b03a556441d105041581110820542c2e4900f99401c0c002c1021030707000a0459040c42c8120100313150001044441c1a65a0482480c44005101b0800a0b0708103080002e048004500034940c08038030002602c05010903610944040340e001e9251645140e40f40500995a0f0401a180b590035104100740104030b64400c40150000c810400010141440d2138000107042d1200501110b091055000c040c68968a50201d01d1092701e809080c50044ca808501c0b040346988030b8401d001c0c00350351800c482c0307000e405c4955440c1c0b40100d415544000131005402d2a0410a1181120080c06980610030401c0154014180c0c01c100c14519140141040c03c40e0191214400300c41041c60084c04203510300340722880461100c03080c8040d9601d040c8804c1659595038030b54801440031040030a000c007241c00325950340c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 342142580 1250 342141330 342141377
    0x18031203022a0f01050c18040b06090307320907180b161b0501021b03101406010207060f1704020604031208091c140706090b1504150510 60
    0x208050340b4000a40c403410307114072020044034419401c000c0400ea85050700b8060703401c2d1111410b0743d410302902840402000301000744980c0c3c3c11100901140748607503001e100e200010700c880b0404104580f55402d801e9810b040c3e19450022050800743c1c60000380d01c80e05071841e8441d10900308610440d14000c0360602d14082580000d20000c030004e107800c0050500d03d52481d40754401d41f00d201d90f030301c000703180308014054901030701d80143d2110183d070803200c9403005149864040503040d0b5000b4020202c8590aa0300c0c1c0003500b00c0c030b143c541b0b002c3c040c0750b590400c0542d0080c00a4589101858032009d4010012440b200032022800d00e020081429503a9590403038000350303840100c07944000302a03e00500803e000f141c60303040c5401000d81142c0900403800c07003410709001c25a240b00341641e11100c0e00c00e054114420030b8a15940c1d440204000034012280340c1e01034160704180340600c8640790b04010a45007404102251003002c01810012501d0300030841500c03003480e080c100514065817076689141e41c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 342143830 1250 342142580 342142627
    0x3050702011233050d020907050310050603010b0405030c22020a050408031b061e07080c09180a060515040501050a020f03040e01030c0602061006050c0a08030103121803120302 77
    0x8044640041d0514200078011800f80380071100100507540d00d080010701741508170301940081d105400518603c1c4150000e60340000103984011070310f51990b0220b461030300240c000300032040000805101314502002041c0d03407140125402c3c00c560301d070f407480701e5000c540c004404007050b070b00410940c1000303003c2c805030341c06040c150003140d48030383c0301070031480085003200036404d214025400403030780c00410b80350044d007400c0c0c0b140c004120340d03100c0e00b90850301c81030010004030403003600307028034462070b550300b0300c04c203000d41179410b040000c4d080c0420030400701e45059000381e205800c14180c3e070b2050000e442c00c1d50304075030342421721075110b400f0004140e0403ca1203200341d083c603000000d4046500c10790300182c2070680f401000c80c0141c040c0c8668090b641c071401034581c02ea69440c0c502c4100300440c4034600130040c2c1c20900301038913040399950b556201c840d0002c3e041110340c189400e880e240c14641c0860078203142455005142c14480c5181c4131034800320100c0c0944001c05400140c64610214100f0080354400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 342145080 1250 342143830 342143861
    0x1302090d06021213111003090f030c050d020a0201090302060d1104030602040603110703080612070807080c12011413030903020a140f010f0e0f0d080f0c010e03030103030507020112 79
    0x4034941ca0240000e42c00390000141601c64400440d601c407611030000c4c0381c1140d005a80480b004c0406040140f0345108000400815494039202d03400900c1818644418900c00c5e00d41c1680042c080c50b0480c00d1000407a5001d08650020703200c5405030307902c0984202103d40595070240d5030030a07000b03800080d0000000b0050165000100001044803541c001c2048802079601045a440b00340c540398114402e40c0c4000e40000c60800102d81240f030040c00e0010248000811150083c1c0e031900041d04105240d032010125402a14018001d410701c035144407494406d40c0d00800402d2002d801254804401500e072043c0700c0e07000014401010b005195030409550001c200d142615621000e2070351004110300b016005620051042d011540506038000003401d80351200803581c80c0301c00c18490702c8078216200b42c0d4041e400710940d6000c5801c02000f003c1d80e4003070a08240d61501000340060070740340452142c03402a03004000402c04a039114054415840e030902c0d01c5044140c038640c042d0040e000417130f04034520 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 342146330 1250 342145080 342145099
    0xe0d08210c0a0e0a12020906121f110c0706050307050408150610030506090a021c090c0e10060801050108180105070f090509040b040b041e0b06040f0507090302130209 73
    0x40360a01c03030140c002070a0750b580341c0f000080100240034074900c19104407941902e034202e60b4801860290b41c0e0310740c400e0700a804c914980384184580d51034802d104000030545401c0c140418500c5601d401036048540d206240c40c1e180030010803406950b49440d03c620020004d01102180501d0310481c11a002460410200c0c1d50482032042c44100820055501910400b542c00b0001e00141c00fa005080c4102c0e8000d2018903e035450220f031101950103542c2500a0300c551902a074040400c9100c0c2d41d0071940900c944101c15410400350f190080f02c00307455035407082c903850301c1000718950107880c141c1900d6083ca0005081d4940302c001a14132a401c0e01d400d075140d402c12041090b00c5030300031110ba50b010701c640d07521001c8559403003d01c03042d09025100540807450f0500000c02103032510300313502d400511441c3c04078940c03203181c00406042841c1c0d0700102c07210034100382400b900d86014020841003a038803038810052410003c4001d02802014032009026100c1e40da40f135451207255505440d196000a04010070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 342147580 1250 342146330 342146341
    0x503030c0a030b03010510090c0c0206030a0b03070e2e033009080703080702060702030a05070e07032912030d1d0a0804060c0503040906061706010e0d0821 68
    0x10780c0060401400091900b00301400780d00c0c0501500303006000518545030924240700c205006400b0401809092111083c8900010f80b2600003e61168a09010000e40074012000b010f00301201e0b68051008100702100707100c64541040c0c084103a500301c030849421544070904001038ae250304c507032018011900c0c000e61b0b07800748908005130340000d44c880d08899221569a443c02c6c4c0346014140128805580f00c080c0070b0000a642d20b00070f298040c0010485418108140c4c0060b02c0d02d0b00c0103804a8a68000c0881001101e855049017500308006040074041c00261219600d08001030800035480f902c12004004107644803066410075200300d65080e60358980ca0088213902606024080072420054411104241c0401043c80040305a11000e21460145801811a0304880c40301c0283c0307540c001000001510403180c81910002e00058131003540e032001024500d100700000074415814083e441001082c1030b502d0100c036a841c0c540c08050746442e43e2007074900150108003000c0e00200108041c06110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 342148830 1250 342147580 342147601
    0x12190912050a0204050c03090a03051305040e030a020106090908030c0a0e0901090b010206011e050d080f0a0306051c0b0a02070f0f080403021509090a0c050d0f0516030209060306010c0f050303 84
    0x4068004d40d0180304075155800034034403d100c201d900c40170700d41207211800e000070b01c50801403010f041c43c590b00014154981001a04948104011801e19400012800303805502801108001d0519040030894808d880c1c8440d007403032200074000c801c048c0000a0b41c50281d4010002041c111f440a8805440c1e03685855140000740003e030111405442024000111031400007814540c100d03001000c0d081c400e26104c24000355111101c821144007106100c03c64100446101401440300150740c040b580c2072074081071000b00f9903108022800d80c1c41562800002c0341003800001e0300050040d200503564802ca0501c1c8101d5001800c009005490075590720040c030541134044c0003900e000f1140c40000c80700902da41440791040e0700216400c0004440012050701e9164030858050101d400c009217008400291002190381a42d154803086030b0b00c0c400e00070400c0380786100c4c2c43c0e080c0c0d0f1420110324002c40000010503074080100214104040300005004110712035030080c16507130380a41101d443c1c0c1410304691 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 342150080 1250 342148830 342148843
    0x31b011d07050109050904050a0b070c0609050303180109020f1003020702120102040504143705070f020f0a0f081315030504060b0f011e03150303031406031219091205 73
    0xc030f001035602100400d00d0318010300f0a0307020301d0f4004014000707035180e9918a40c15080c0105100148841e07840c170140410194002c004029100308041c2d6501d01e0704c125001210300311041c45141682c0f40074a0000144c482c500c101c40d248104944075507415a00b240b044010348581100203402681141d036006000ea0150040c00030b940342200d0906c1004040210102d0391070b003c40d4000110890668210040d500070315007076400180301d07400c4003084a105401901502d20070750f007500015a100181e1040154180b1698a02d00b00100141003004004d4075983c010310f202c000081c01401000648003c641105035075280240000300204200703140b10103010b070041c4001c9030b003035038650306021541050307143c28100030b0003550058540c08006410043ca0035605036082004505056980d480898082d9204403418000e5209590106108589a05110710113501a00460103130340210345e40527006028100b0b43c0c81408011140f4114001e480e03074103c60018842d0301011803881104042c0b01400703000b0540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 342151330 1250 342150080 342150089
    0x204090e0601050a1202090406020703020c0604080d120204060f11010617062a0d05090a05010e0a03020111030f16170103060624050306010c0f0c0909030210020c031b011d07 76
    0xd070b13901e903403030030324103819a03401000035400341601d40080d000036250f42c0540510b0340284102d81d010002c4401048155110b0340100c00b05038403203030b4808041c03507001810003413808650300203504251030001c018182c0c1c0162158241801410341d0040c0c4121003d40c044001040380d100c161000b8030244003016150307071040e1610b0034030070300b1100360044540510040c59900072040404529003000d410f404802041c0140800700c45001f80c00176200424000d00400c5034106c0703a1070180500c0101484c0103801c441d68078a420741c1102052040201280d41000c09540c80359030a94841d0084402c540102c4144040f8018842ca02040c503001009001240d0702030020b85914041400812907040c030b50111010f100b21242c40080d0080002580e40e511880c00000c0700c0b80308651866210104c0c2d6a0200c1060181e04023465080c0d44490030820305604100110403400401ca0071880c00300001540d40d1603200ba605038080100b00f030300b0b41c8602103600354811910040d02c100030701d102c090780d000840c0c0c40f05464801c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 342152580 1250 342151330 342151339
    0x1104060f020c0901092c100b1f11070902030901020324030601051905030f0a0201260a09110904210504050616050f1222180b03010204090e060105 64
    0x1540c0d006035000085241d41950028020440e6030710384400031005c1c0092100c40b0002c00c0e52400521000b0040c060b0318100d0050038000740c610241d20b07500746c40456044601252007160b40a070b00e1050040d291828001c00b4030f051a141d00070030740c40c12046283c040c4940c880d09202384008104a604034046d4040c0d4081d101031130300c1d0558490780e440507074520800c40240c25410740040c00100301600d03021849907542c0c0c0c003120003105030380e551b0000a410400b5524036031100350013096404003150303030100207410510420340280c40900c0b450718500380c04910003090408403958601c1c10505006040500000c844070061403484a460149820290f00012440598805212014001405005009860540708041c1805007000c092080c04a2072400d005416101070040d0750074a0001c2000307200c203980000d200507041d541c403d2540c1c0419050100d81040c105601180c10b020702890700f601c80d00100096401601140401c10200003074024403c0d41d10404810b40742c00500805504041001da040303410849 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 342153830 1250 342152580 342152597
    0x507050603070512180a030914031c052113020405010e070c060213080d0507110d03050d0209030c090108010c030b0f010e01050d0204030602130e070c0804090b13110406 74
    0x80600103180020385030180410800d01030004121956807070998407914103408042424159041207082030400c3c01c06074006907035501c00340442da01c3c40703900c1c807041c0d10b044e402810754003208001e000749200391000a00c2008030000b81c0d403031600207030b8051201011059151800030b09111742c10480428903010128003581c04c020000800c00400c030707070301c2d84078290546415109200654900b0300035801070a000c00124809440881e0290003085511241030058980750b41e41c403903a0420498074040108032501c10301d0303c1a013100000340d02c5400d5501c0941c6130a80541c0700c80c3c01d0000a4213110b802c00800350081c011381c000041c200310541018000782d0640c1c0b401c0184581c42000d20040007000708800d4081101c204221f111948030341e000780030b11410100018141922a914a82627910040e0716180d440c0161310140b1506617000c0300f0580040841c00c00598800302c965402059006611440c3c01c0c551380c5041c08052500c0d00c0920412000003154208540402a0a1040305800c94010640058a40ca = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 342155080 1250 342153830 342153839
    0x20d0306150507061104092003010312031a03100f0c020c030304062001090f03030b0d170c03070510020a030605060a080c031b0703090e150603010e130803070801030507 74
    0x2031081034241d540320700718a01c15280000c01603590307522482c001c88103555140b105000d50411100a0030261451481c00705414590105c0340c400540510707100c1c80502420001000010402480f451403140079041c08205082188006c000316500d040703000b90140170b50511a01000360039448110003c24004003008075030b000d840126900c4558640f0702c0c0d0103502c00c01003480810301400071100c03d42041c8155174282009501c0a50030341e40c1c02da0088861801d900408820550580100d0215400c00d444150000c00035440d00c0142080c412001644240c0004503d00e400c44140121901c40f5004000c403944800000200d600940c448a000000640f504a02240d9482e01c80111180000180e5891865448801140c4003e900250911036031b550400324200b03012100b8005170203c503002e515a08071041c40c082c1680d01c0b4503001460f015407248242c000407040c1e6100004e6038159103244804444941d44c05a0340030061014503000b41c01c2c45004410004000d502c1040da41c142c81c07281c400e844c9101c0c0c1e05c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 342156330 1250 342155080 342155087
    0xa150206060109120b040b091c052107051602040e0d11010b27060103151503060f08031b240a0e0a02060909040f0b090c0102010e0c01020c010c080403080a090501020d 73
    0x913042c008044003c041c0100300440da04003606600441010240d483c1c00401c58051084800c3c0c500f03843c404104040fa00c144208400b81000900d40358080329442c2c14542018010203a00c56490f5102081610407401d4007551595808038070b000c503001d01102c50300e60010501030164070304090110440c0d808d151051015007403002410088444404201c484001c0c1c0d0540074502500003090070303040503964044030036802903100d0080000d1140900c0c01e0b1346002c444600400f521019003051007440086402003202c0da10010450b11503a0826840c4000d010035141e06609002e800c422403c0b03500d48a0a094000c3c80134489001d000d01400d41d81042529060200181c84807001e00002c0d61004081c003040089040c00b100b040d138010310590030300500c184c40d652a0b852020040e501a20785070302c560008000d5507024401c200e076030000c4200a088428003070000035620340c9401540381c1081707048594501044001d0b4181c0d4080c55104c6021904d0321014800100030f4400352045500511810745100e807410301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 342157580 1250 342156330 342156359
    0x141612090803180f180402010c06020d061202040f05010612090804050324090a111005090d030503180a021f0c0507081629030c070506040f0b070f02070905060a150206060109 76
    0x802c17285042c0395aa90b001903441c0e509001d0145c1d07542b50200f10044e2110050f11429000d4809001c1c003565541540c010700c000c175101c0414003840030f80303000300500500d074100c0314030040f1000c81d180110316060b40c2d00c0c180c4801c1c001d03a031055030544600c2e00d10195408072184202020742c403171401402140e035100136040d0b40d0000e240d0042d2240d07019105042d801c0c103148031031444100302420070624111322400402d4280c400300b035003980002c0011040c480c01c401800042e488407080703c002440700c03800c141c0000f4107103100c94543d202c041408032400c000c8980030b241c41041c0640c00c10144d44071940d55801851f1075020380249042c510301c040e036021420782481c5411052501c01090800d4104402c0b41003111543d0019002e8885001d0602000001440401c2014440e51090121415008052030242485800a003400007071055851503005000da00141620454400d442c0105250701c40d0008a41c14031200e41110700720058003220504115000524140600004e0f0fa88000306503a40c40035510602 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 342158830 1250 342157580 342157609
    0x30a0e060c0415030e19060c0309030210020a0908030c0a06051003031b02150c07030c05040506010f0e010e0409050f06011403030d1e0603050d141612090803180f 71
    0x207105000c00e104103903014404281c1c40c280c90400051207208828094074017a4664500c04401a03070601c10f1003080118081c202000e11075050904c00b042c8203640c086d440301c00f00410400101d501282a416003440707070a46c0801082d110059030758584203c121315072030f42884030003500d440381000082580145405481d804403038040da02e8103c009601c001108550507400016a4403c0600c510b07031002102003401401c240050700000c0110a03e540341c10300c0c85041340e0f44801e101d54507000400c0903a98000c4030b00700c010b810034504415003131481c40059902d8160300403001d4203d80f8000c141410010300242001d1030070342241c103c0b403181e80e95035420003041c5215061580c0507001070006000f410550b07084072142102d140721076010034920800500460b0940d901c2030f51981e00c1481410440c6030042040000509141c01d080e02d800400b981440b1514420500100b005e0180341d4441cae00c181c880c9040c000035003083c10680ea0b42d4200d8190303480012000c140580d11032510402d138401c5514000c082c0c0704250 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 342160080 1250 342158830 342158851
    0x70608060409260408070b090139030905010e19091104080a0602040302100306050d02210d0f2c0f03070312120e0109030e0f061b03030a0e06 62
    0x2903840340c0610010300801e400440d184035100310004411105000050103504240c01d0840e02c1c0c5250414103407410166510075000c01d4030030070580150b40d81c448c03807904074013094165449445200101c00c0c804501c3c410790720141500051480c2041640c4600000c0413100700b660740203801d90785a010013140d2809e401140a810110001c10000c5013070980100c000c010040108a081a685101080c01c150720030300e0441d4a280d00140c240f045141103000700175101901d280400445007088049812842d413241302920078008503400798142c0600410400d0b200d100740e010366109214090010f81340d100d02030505408520030682503404000c1d005083c41003104100140d44102e0000710900141d101d52680750380e054001e13050080003081400303003c1010500c1030341e69202c07049a04c4100900710740c06d1042041f41c0342d040c2850300c00841c3c1d0140049086020803201000c0b11301001d4002540c5c0d01ca48800f559004118242e00c0c40d0300c04003c8040e6106422424003405205a582516030311000122000b1101c0b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 342161330 1250 342160080 342160097
    0x210080f07031d0303010909140a0c06051c0f0603030306060e0f090709050d030f021c0807030b01030b131406031c050c0307141c0206130308060f150307020f0706 71
    0x958403941107950f903d422243c09403030542001120a046a01c00d820008000391a143c500c01001a0400703c02c0c500280c61018080040640d580d9240b824400c1c406c9030100034000c210380c0c81d6101280d41000c4103008040040010200c88403004018006600c401d0300400d26120b030003d80030b03004085d12401d8900c020404580038003c1e504000c10660042c0403442001701d41d0300003041c0c0c1e403605204007030500d000c0e403601220302001c1c450084c540304202c41d02c030002803031030954400c0c000c3d002034074140c02c81480d050201c1c82e600c0d00c2004030005e03d0305000c0309a20440130300000d46000401d03444101030014410103010103a071044185079a0345418000303034860b040083c4440f280b152240001e094003940d02802d0301d103000201e07141e0051030035003058150102e402c900c111003445001c41d025001822010b00282c20b003403910a040011a41d00301c8005401e025000c00083c48550350002c0315000300e04024142003241c01400c0a003c034640003200c940003d4481c3d103102d801511000111102291001d0381d400c00c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 342162580 1250 342161330 342161341
    0x30303090b0c21040f02060a02030c070816060305151011071a0a050313060911010f18050105090a0e1608090106030c03120e030f2a0a0603020c1504030c0210080f 71
    0x34070f40103200303030744071120103162000503521b140003840301c4001a07000b0b41e00c0e40c01d003a684900301541075100040c0c90348520382040c2902ca80952140c1124040c0c01c0000d50f9a8a4120a408070700d001005998880ca494540c0d100c42d507007040c0001d811892000c1244d80403515924207424110300c00e0855842884140100c2410030b01c143e000390b07401500c0c59480c1000b1215940e5000603184008403c81d18142888a05111540e100045910183e05850040e25002e0420b0541441c41e43c603000f058100400014910a5501c44081d894000c00070f46c000d040d4503140c100c030620b44213000d101d04400000d88881c003141400b20705010b00c0c415207421200c41d410a901e1030741c1e11117220244c0712191081c0300000341d40180316075050140118110051028001a94008540c9008801c44a5950010001520706c101a07030312032040d44d500b035441d6401c005a4070140c8010740d624105c0d0100c0c0060040680c2c50401081550291010a5091098400d0101e030b4001400a03902160122201c02c0c890748148006507 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 342163830 1250 342162580 342162637
    0x60906020c031b091f030605010302120a0f020909120409020901090b04080319110313030b1e0c0c1204090e0c0103050420150705031207020706020d180b04030303090b0c 74
    0x2904555500c154260503045d03005900044115980281c415981e100c0042040d41442c1c01214841540407020703002c807800d2660b802500ca542410080d000b010002e0016400320003c00006c11844c00712001240c440b603452010784083d50001ea025400114007402c002940001c1900f91000e442e0000c02031410201e81c01c3d20b88050303c4411500804120605840d1425010284000c200104440101c020b0f02d0b0304504150740c40310f001034203102c0b007044144003445c0c0c4030728503100c2d55800c0200c0c03120455903089009049071401040c000718080520300010006141340555001e080706111100951746d0449003040150211102120003500103d5500b401d00c0c4444a4003010700d0800d54000c00c4d00e00d41200744502d03904030340c01c151003c4960b50300006044180380100f2403601c1d03000350b41e8801003c5c02c0d414010300070b45600507400c1100600c001603d01c1440013403a110038001402034801c21544441d52400d0082c080c00040c001528105600b0000c036849603164022601c40000e40045002280300003c0b250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 342165080 1250 342163830 342163849
    0x70206030a020a0306120f0b01050613030611090a06180902070c0905071103040f050f040911010f0201022808090706080606090301020c0d03061a0304110904050c0307060906020c031b 80
    0x500c00c05603a8035000c2040b80c00c0762a006e40d03141c00b0315682e46000702c10b89001e034690001038111501c100c006106030706c01015807682e0345064035404000810301c2005440c81125600988031166406000706401207110b5500030b5405802c51701c502521000d8a5a40d82d210049100390314024000407640070042c8510903850b04600d070005850f2030f00310b080520f01351807241590403507080f04060125001042005103450407406040c0d0904443c20840050983d50b01e401034070a14010340e05110580c2143c0042500030360654028940782c4103400b0003488200500104078040385225404140b40e040450218000010440c0580e40140c940240b1502da503001c05c5019080a0f00040c0d0564081110702815401840301240300c0001c0c2d203011032424240964038011100e000c503040b82c88501401004041b81c21012806802030003502e40d00140d80b1130f0b003085820000261481a003520402d10002195580266030348100c80302c03503094a00c040880000c242c0c4136003210410048042a03200340e03039014075014519 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 342166330 1250 342165080 342165097
    0x160e01021e0f060103080316020708070324050a0203010603110901090501050c01020f120405010e0a0f02040f09061a0405010611072c0705120f0705030f06060d0f05040512070206030a02 81
    0x100c0d06560100442e882c0b07000401d80044032403000100234051804815850008154484c1c0042e00c0001c1c18004041c0ea60360541c88050400d0828003020b065024420042d40c6032004010002e12041c50720017032000c0690700a126900000c0e20303110000c6030581c1882c040e900002016515403000344d142c1001110541c02c02103481506541c00c001c1e42d80c103007800c00001c000c0007040003a00c40f07103031815060907821034544950000703041e0030a031034a0000602c120544040305504507400507010303d0101c0c20100a01c2c075040011301c030b503140400505410ba003034115090501c100316010701c40daa8030746504407541d10380e1011002a5034003c0d0000e119103181000d00c00d5182c070500100081598014803200305c114000e8600310040f90001504c10040c503401c07222241d0102040e4105141030518407401441031000501a585044016000c0384481c0e80c0e1604440000082007811721106800442180c020b0105907011511841200342800c0c2d00c031085020f640f080c5800034417442c2540d6a07040e030710000e980074200c0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 342167580 1250 342166330 342166333
    0x4080706050414031201031115030a0c0c140c09061f0e03161503060b1206100306030b0c0405120a05030726031905101404020d0b041103160e01021e 65
    0x200030740b480e0f108202800810201054100a552450a0400390a00a1451513000b144960702e400101c18481080f02d400401200001619a44102d0110352514400d00000d040d0443e048050007259400960510462400c031030180007a241c1e0810004407400203c4402c0c0b1034400c0541030200d040c040c00d40000f41d83c07405000c1d070b50501e0b554149022030720190b03040300d018803d402c0050403407254035100c1c040251041e010828a0101003158141c60b80c480280307102c0c41070301292466070302d007803094200400441d804000c02c0044e060503090782045400a024041c02065801115001070700f00080304194035030008040c41c40c00295403030310441e0711305219460b5100c421090340204040d000d03c00662050b10043c8103030343d641104001c02000c4e280042d000c21440ca40314401440340301404020008030043c100d40041c3e031030b002094030201400106203003a52143c40c140440201d880180e009500c990381e98028801e40030700d4004140c81101c13009a2480c0164021109803024840055004001800020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 342168830 1250 342167580 342167603
    0x7060c0606030f03050c0d0206040b040b0601020f01110a030c03060b03010b030402030f371101031e1503021008100e04020a05040f0902031603020d1106130803091305040807060504 79
    0x119103258184007020304600150000944c030501c006c0500030044441c07040c0c4064441802e02c1d80301d10b03170030080180001e0407644208011401503070003002030b0210b00015030001d1040392041010550b0b5500448031080100741442900c08103d0300c28480c08066401a886490071a42410500c502c00e801c024401c0760140b01c0c0d96420071900c0001c11240d41d80e4601000121b400480480707014540c1460780d1007101c120701c0c4484007a00000c204440303c0b080e01e2402c1c43c1c001a082d01403098038030000088071189071833528001811600000203000f04013035a009a5040c0510020108225170180048428420083d001c40041c022507041ca40f09640140c00180040e1580351a000060102c1e01100803260082c2d51303032440d0100b141000e01c03140e5001000021901480c6e45142c0100d00b04600c6480000c0900035502008202580c5003400d541c03100728803d210b80f09442d140d91289941c1d83c84210094419600b05c06160170142c690f004007441503601c800068107080841d62400060b042c040d10403212000d444 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 342170080 1250 342168830 342168833
    0x30608240c0d0e0a1b0e0c0a0c0501061211031605011d27100801020306013501060f020105090706050d020307121506030614010509120c03070914060f0307060c060603 73
    0x10400076000d180660b4404417042c20103d141030b22284244d000100f1a5181d404000040f0025410748001c00b41d00e0a0036100301c91186409401003460381c005082c80c01c084464030f401c2c40000700060b080c1c400113904903036009009041e001408501031041074009030030a10220160044400000000c1d2070103800e20226140d18000480c24034504a98240b01107081020440300a14441102004169001c000c42c603600b02480020300b6140412a9103420720113000382485500b04694445054840f5100c00e050b255031a18801844042412403103001907081001007141c550002c102c1d2022900c858803607925007500c10b1410300194100a101e801071140c1850707085420f4805000300c8528078504001d012095060010203021035071b00b6007046084c00d00700da4900c54a6608802194084542240c0303100c0b6000d012411146070030101001e00e6054050440001481c2c01c182d0800038a00c20405041045c1c4c4d80c134181480319170017038001403562541c03140c0f20030405a80075030b00d41e41c8510300034000490703126100d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 342171330 1250 342170080 342170083
    0x42702012d030218040506060d090203211216050403021011010507030b040c030204180203090a0f0302060402010e060909041113020c070312080108030403030e01030219030608240c0d0e 81
    0x101d48441021940008000e00c4102d4160114500c1c1c8074116400c00c0942003507004508540101c803901d0040c903540340a4007041d036908101112990b020684421240d402003034501400740c0040640b070007034134410f0010400c01000c076803e14107008001c0c2c0c0e8144c2007620355020040150900c1401a0078002c04e80c2112041e05001e020341031080080340c0b404034290151509000c11141030120300410144180018800c902d821030810706c101440d000c0c00340c4c0341d44030180418142100280000d00c9401500781c031104064000c81c00074412030003600c0c0c03245070700c1150080c030841d4450103030010f07032085501c40000d00044480b03150030405000a00341002e4000e21b210070400720b90203421003401c81c3c0d21840d002c00c00c10858401110444444c0d240c42c0181d5450b006c01e00f41d40b40220b000050510103254200003580c1d1295040e101907030f000030741c580c0d10008840400f130f0040505006844c02030042c80100da10300d4094050080307580003140b07a0b443e655900e1306d1141c00c45800c12403c02150300d8449007100d020000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 342172580 1250 342171330 342171407
    0xf09040b0301180c06050c033403110d0503391b060109020c0a060b030c0901140909030c0705010e031006031b060f09291804270201 58
    0x140c2c500d0642e681841c604204c00d201e0311544c065020032070300b001214100d05010041c0c80c440440c40f002c01000003401c031151056950000100c908408540540809043e4009a42c800d9a05400d050b0380c1981d110781c904441c00c1c4811240c00b11190300808440141c44158a003190b40f061001d08031500143d81100040c01951000328803640e000d03500c203841001b042040c0203141c01031035180d4003107140142c0c2980b15a22070181541c058209552208100c015440a1000900d1144018208141507031191240d41700649a00b18036400381415038009540a400002100c0a94007610300030400c2e5031924004482c2c3d12100c004080d018011003008100004950007403030041c6100d122482400d040840b51501041100c7d0b00030010010744282201800ba0040c061070207640311001211035070692a0200310030310107070b21501c0e10583c90025001284580c40012286680f0040300c0a110105403010455510408600f8103001c0c019079605c010015800b8041080000c000c00080300c0d41f079404036104919204 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 342173830 1250 342172580 342172601
    0x3080a121a0a050d060f020706020a0315051509030c0d110102190c140f0a0305030307090509010f120312020a0f120903080601050307030f023103080f09040b0301 71
    0x1400c0105030080350116010310051030510701181240c0e03014120024021041078451540213a40444110301406140d40042103903103002001955200320710b10f8a040294410310020340008d1511910000b4281c080107800c0403202c0040001401c203c00500b489210741c0905030442d07161140c0038600c011900da1a1040c3c09950144110610030700e20345001904011102100940300c00f0300d50880c000050178400143c040c1c0d44650010084001c80342c1c045000505141c5400741c0c0012030a00000420000100840c803d084540da2600581d0f99101800700211080c0545954030888142c10300101c0c0080b100401040c2c080c0c90318500392451785c0340740c600b242d110442c540700141c1c0301401540f400742c01c180c2c54902414070150030003189039540c41c010451440509021304000c0700201240015100e5001044102c5841004668403e02c9121002904421002c0700000725401c49540700340b00c05000900040b40e40000d1071038903103000b94007441d02a900c074000255119940b09222012610244501038000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 342175080 1250 342173830 342173837
    0x51609062909010e09011805060913030509010c140a060608121801020718050717040305070b190c03021209122217011a040c0c110d0803072604121803080a 68
    0x203034801c68149062300d9004102500812a40c81880406030040c01444540c4c0d416241140c0c480c184d880040300da049442e0006404592000c000c1040004041040c60009109401c208185135641d4070481c0c650420100c003110701d21050201940c40b02d1000980c115018051040c0d400e607540b5205403030101410460700c05405039694040001c9960030582582108a40003e02556450259001000741c0300300b01c0b004240c15464404185829020030000c03010b00c03103c0105001d01060780030018002d4000c80d607050400c3d0320308004103a00c010f01003050310041981d804281c2c038200b01a6a07a580343e1070400c0f4829030a40ca007040000b00d44929400d150700e101d40340f80000c03a06105c40030750a04807000100c8500e110381d140920100d03040740c0014542002e2648039000da1825508403000800310010075801800c6070400208015640340d00040745d810308001c00d625a500f4040f28841d5081018080f1401003440c0c4042007180324440c092003080c0c3c1c25260b03411140480b01d07181d95030003039990440e50344603022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 342176330 1250 342175080 342175109
    0x6080309280b1207020102040b0304060902010908030a020a0506010e040201020a0b09190c0303020c040605091302010c0f050a0213150b030a0b0a030303050a06050405060f0616051609062909010e0901 87
    0x41c262520202c4d0708a0752030701c001c0d41800d080c01e208012910015100602a6a035003000300116400381d40090000c045071415a619000164406915644c45810460382d60040740008070b11440d00c3c504c01400b994040c0d0050070404801d075105601090040d20120491080501c2c1005c0343d0701d240d940c401081d201c1c0300c00c0c1107114510b00d4040d1a01410900c160312880c1803d00034821501c842540707a1b403008070048942d554100a000507102e1043c0c85001410f5403c82e42c0011003845800a000c02145100352180c0c2101903e42107010b08613070b4030300503107059900c0c0d07a08100628102c54001e0341d0840f040160001d8416510800030300c1d210410f500485c0030a03220b900300f0246813164410303c0010407080c1c6e4144014039018001078820b110000b04244500804a402c0701458900d4640c0c0115981c80030442d0b03040310f01a81c01c081e03555198404c0ea00d902d410040041200c0c0708100001e28900c500503a684010180010400310f503030070490039141001107944508041c2d1344c520012600130000c0301142c5070f1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 342177580 1250 342176330 342176347
    0x922060e011401170a060e0c030121081602011e03050a050a020f04030f0606050303181e031c0320041a090303120c090904080a0e010306080309280b 65
    0x640450581c028202c000c000d003102107107a60040c45024004d80c100d42e8809113550341c154501d00414040d0003030091a4414010410f480f400b020003035060b510f000302c40c9401c10066242c1c0041e00d4880f401c0c01040c0035020710070707502c0002c0c0f80001d600c0510300c14100509409004a014001102840b8803180002d8441d0288200b1101ca40f04e41a0080324601043d882c1243c0500003c095224600c0f0040038002400310680a01c07509500c4580500001015640e40344400c1d1440b02e480c1801d881420b119004044103040c092400f4144100a610081d001e030544c42c1c3c01c042c20214641c0e81c1c010900526468400124044581c40c1100f145400004031142d02c40e810b00c40d21090103003d045188000d190f08100008141d43c000040d00c0010041d50151800c0340c1d1380303521055560003184542d40d00402d14000f80710401c81408007601e0780c003049658600241e072400d4011400d076032042c4910159034004002c03010ba2800e12410b00d542e01c440d8248804010010452079110b1744900b60f0051401400220300003c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 342178830 1250 342177580 342177599
    0x206070b04061b170606090d0f060506090f0a18060c0c03020606030601060504050909010e010906091a16030911030a0305040303021614010c050a0c0303090f050307030f0602092206 79
    0x60b00f4000c00301d002c00201e401c10340540650129552031400c5815840021080d40d28581150704191001e0007903521400703580f6090607042809401164110f040000144032800c0000d0602c3c0b0807110300320200c1c00358480060610080100c080d511407410010f1000380d02151060007540d60305111130b07072440001c0c096030400904100002d8081d62003034015200400c40c0c950f12409030b0b01510012030b403421140d2282100c0740d0041075005500c9009500b462402402d01035203901c008802401030b60794000c0c80d00150403285031102c01701c0d0440302810038140c00c50b00041c401c4d030181422520543c10920483c0007000064030b03005103100c0c114001a00040d0034003c1680c18840d04540090980c2c0c442c0540b41010440c030554040104900d0400850f035042e04107212041240008154000c0c14440703149490382002000e044a0740540c2200b5000302000007841d0400281c1c0c0d1048a0304008940110b404036510030020354810380201d0340c081050000e042110800003401190000d210300300243c824a0b040401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 342180080 1250 342178830 342178841
    0x92a050f0402031e10030b090313080312070f211b0c0b0103291302041a0d0206031005100c05070e0c033d0302090c0f07080906070206070b0406 63
    0x540c01240144244041008014400c0558041007a24002c4d255218240e440000b6441c0e400036249440e01001d1004604012000304ac0013402440541e40341919828019035910906407035600c03030b10b051700010300f05511452000c3c0c86111039251581c0d01da1400605034645400824a64000c01d66501002008000c0701140071080009400c080207460304540b00c40030400c0051001800600e0040d00401006003551f0340a20103480f203203050f01d440d0400212680d844410a0750490041d45040300c4c0c210f2460380ba54032034040d020010705015020f0409d03402c1c065130b0b4001030510720f4802d2850201044030b42d03401c009001c0000440da01c90034500342c13604145203040a180d100d210000320311410310050381108400c50780c0c0060b1483c190307940c0000c80c00620a2090515802c580803070a650315550790041d860480e40b085a000300c800079029114440781131642c1c440c000d16560404401c03c4510009070111001d0b000e075880c0244082d00b0502c040d0046803a82d40020740440e0586030034000c102c00c200c024440e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 342181330 1250 342180080 342180109
    0x70308060913020d120c080a020c010e0a080d140409050903030406050c030f130f06060f050306010e010806060d031205040f14070501020c040207320d0e0f0103092a05 73
    0x82e211100095008658075516500020b846240c8680b0743c260214002d00e42c0203103095000341e002c0d51320f5943d40002510344079070200c50340c009500200c0c0c103045490f04d40c0050050b10041000780c0020a4100d10640e4a506a0700c2d009840000038000080e0010007031103800d10900038100034650b00c0c5020700c0c10004450004000c41c2c0b12071001d000340200031071a011060740c402801902c03401c00010300d040031110f403810b0307000050029003003207130210340070b024102084219130090741110034a90300e80c005905030b140e0034001e100341c1d030340003000141c41480c0c4421144603c0b8000d0a1030541c0d410003003483d1054a204032410f644100e8010004800c00c01d141c1a071300819410000038000070743c10304000075141d034461100e40c5d21454003c0b43e40380521040002d0481070000e0718002d45904555201c1d0070203d0b0a0f82075242489001d450300208859000f10541034503110003c046003000e01c0c020005400410704c6000c283c4007202d40c2144144251320001181c100d40c9890000f51560074940320401c59845150848d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 342182580 1250 342181330 342181351
    0x206190c0e090c0903010504030504080f07080c09041a07020604021509090a0f0b03010f05070207051c0201050d0f02070c0503011104180b12100f1b08041103010b04020703080609 78
    0x40162125501c80040c00241c40c0445100c022070b00c03580c019490500070060a00c1e4503520309010300c0b04154200009004076806c6805a510382c112800c0c41640b664440d100e00d0b040398000d074080c4105032505c0e1581039405803103880c0c4d2140300031042569114100c0700300c0d0007038090703031109081c0070039842c081406000f01c0610102c25490300c20b11902240b003032070001d4291955141c40f01e44500710f002081d0807454108070040d000b0002c0c801146140000341000399001e03c0903008681c00480d850a04400540021214003984800307030156034011115a4040040840165a501c0440400c4051400204001401410061001810302d42014219162072804408206081104109003100c1005203100c0742c111036000110381000300702240c0f80483c0440300b031109004192a0a080c164598090b06450780c54071030400260b90705403041d00c084036003000c800000c10001c20029001541c20b0300408076444001d000410300c281501c000c14141d1704005412408903c8000800c804c0d420030300e600716403000341c0ca00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 342183830 1250 342182580 342182591
    0x319111315080d1b050c040c051603020601090b0a0e0f04230d080c1903020d021e070b090a0f020f031509150a1503030c0303060302060f2106060406030c0c08040303020619 75
    0x3517616548401221001c0c0c001d80d1146e8404007014080d40541c0c0980003041520b0821a0407840d0082d2150000d0080404840c0703400000319841c1440c00130201035840455a40c0e030681c07210b411242491100801c1251210404440c589100c001001c1550342c0e000101e0041c180ca004100e03024141150040481d040101c0901403401c0c0303030110081f484610040b0b8240140c0d0756483d510203402074400c010310051004013078010401100e0300c1000070201075018034a0042a0380311055169150051000c0240600c100c99810502520704624440800c15006080300d0042035100380c514440c8a007210145026003041d00b648010860711780a003948400051000c0211311a41e0810b000c87c07007140c0c0030107800c0020b210290410140a40c2c1320300003a41d002040991602280c140c2c69006501c81d02100c1c1148121805450030a00c00042c4240140001007000f820581032500440c0100940c003550410030940305810404a2020802440514000c0d40540594609800140c0034030103801c441400039407510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 342185080 1250 342183830 342183833
    0x40914040203070b070203070b03011707090c08012c0c0316020a0c0902070318030c03061a2202070b09030a0801060203040f060e0d0602180319111315080d1b 69
    0x803c181c026640c00c1514252507801c1070000c246440f900b50440013803007c00100124a13484140381d105074980070502110390054407032400c4001d942c0c4500282010a403800700521400926070b0341056685c01c0350055010380c90f244001d109141d00262a0000300190000034400c583c4520030b02e01c024240719000401c0b442e1282d40d2119180c120134840c0382c0c4000c3e03000c11840304040c400c42c1d00c43d20300d40f41075940d00c500984a05186403000400c7c0b100f02c0c0c0702807a050444400517205c0a82c5008080014052002250120262031426154001200d00280c0c20846800010040200c0714000c01a0000864071780b40100806000359a040e0459800c3d58814041085280140c1d00c2410558400e8508a1044400980444d0400b040034000801a60001c50074400c44000022040c0c1403c0c401c9084482c0103542043c082000c40d5409006000d04200e0540c9058034149590303205a2849096030009102102e004402400300c0b117604100c1091b0061040140c03815486243c103004130000460044940c0c07410b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 342186330 1250 342185080 342185083
    0x72103061412070b0310030f0506060310110315150d0e010501060809030714120f0a18060e1203070f1202060c0a17060118140306090f07061d04060308040914040203 72
    0x7441002d000010002c005581080710b1700011b0011039012110490405092400c69101c1c502100c56a0181c0b080211810802105015511070300d400c10f800d080c6940c56815038a000b4440c1d42c241d854112150300310b0800310303004100050031411803810000881580d40d84106080d180181d110108000e845c1d0140700d180c0c1da0100c03c4403181680040003152100400c0b40e150300304980c8000304500310070f020604070300e4050f12000400500c00e207276866409620305007040034040c05007401040001001d030070980b600e60030001c0218100c05031803011a402c0c00101c0d030f80c81c0c01040c3d523090100c1d0003084012140d070f001070f010031001e90800809c038001030401265003030007804240d1580c824100e074407800000c00c0755a40900e900c0101142c4c5009110100c640346d421149004642c0030030b1900074400ca00c001100220085024100b0030f6114003e48a42c0d843c0c02c4080340c3c12170601121008a212500031b010203940d492051030015442101440d854a14004c10300c012180c580302c61400758405a0100305c0180e40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 342187580 1250 342186330 342186343
    0xc070320060c0310050307060804050f150a1d0d09080d080415020f12040602041401110319021c021605041a010305070e0405040c0819050304060302072103061412 71
    0x202c001d242601c0307940c1c407180307840840703210f078040c0e501409800d10205400f503101c0d45603445070f4003d40461301c211207002061940d4a0107403088010541c0300d03402280081c89590421900030707001001400501d45a043c00c182070540c119155001704006040c200440401401181c005481c40c1c00c00b09182e2074140c544404000c0391003030704c001a03980029529042d190780c100b910001c1c106c8240c640000d14080c9860b900a502500940500300520300c2940010741c82400500c0084481c50003541c10000c0f41082a8181c2903c05088001d5005003881107880950b1101088100d407819070080410b104180381c00f00064041e40c00180c0641d0800000c04036802034140c10242c400f03428600041d403560348240803501455201e102951042c202024801031000501150701903034500703400d0b59041695000d000d02d10f030a9050005280d5007042c0810010540254050044113000b065018030102c2c0c4030f1031000e8100101104040170a1740d901052001d41c070000820b07070302240d06403080240250402e420a545a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 342188830 1250 342187580 342187591
    0x30d11030a050702120604240218090a09021306060806040e03120901150b03090705010e0a030605040c1214060709060507060207150617060708010609030b0601030e03030c07032006 79
    0x200003c102c400c6407102c14000c0b034000d100341e041ea1140e00b49450144000080040b070025050f001110b0000440a24805c0316101c140d0501d1800e030132031120040c0002e4000007480162201d580314440001340c0c6442d0071032442c80c8030011000078071a0520b9000340103408007400341b034011f0380ba0400c2003d4000c0008116809103010361a116407a03910044881e000d00b000c07104020095006c0d80c0d001800d0360010300070b50302070040301e401d84070010388460044446484c00a400e507030254144038100301040007588659009401501203d90072511001c001d142c22000703c00c22101220a80c80740111408203000b05a0800001d1621242003072410340001c000380500c80001d00742d283c0c002405401c1000d0012104182c05100005000300c0384c1d10035030082c81229906c062402800703060000b0341d850f0312403074000d8180da0b201d4031540221811600d400c61320000c0141124141a0380c0c0c400000c0d940b200300043c510485038100c9159686c2d0325840c3c003e04540509400d0003000320600c41364410200b0105100d54000c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 342190080 1250 342188830 342188837
    0x30f0306050f190504020a020703021f0801030b040303060b0a0c060c230f04030f06020c1506311a010e0d0b01140325030c0e1005010e01031d0606030d11030a 69
    0xd01507007a08840b403c0c0e180e008940c1309100040580040390081126030031a4002c81c2c250700c2c0c0f1036184d400c030000b4448400d00c0400080b40c50340140005466506025009400391800260580d194002500700e84c0c0841080000305504840c00307010443d103406072542080c0c1c14a89100c0f1817060b5043c03000c6407003a103890116120000714000d00c0c540c0400c4261001580c010013200d0101704141814402944520050402409000024038103603000540e0980100300c058005031142d4090741c028514a4050310242c4040c40c0516044001301c801406500d8080c1c03d507030703003203240802c107400050443c000c2e80086501600c0700340ad4600101d005807040c5c604441041d102545889207200002c1d041c40107400e21842c0b44088040345c01010726400191030181e82c407448043c5407403900c43e01100c0c0344040c02c40720340b000701045000a0005500c01c91051f42c2942040c12b000c200406500381105c2071541c0c0e4014179110b40d00c054200006032408005010405040b42000c8566200719a580c0c2e4503889451004000d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 342191330 1250 342190080 342190099
    0x1c0b33031305031c060e011a0d0914060a06061412040c03120801082a040c260613050609010312021203010801020d3605100203070c030f0306050f 64
    0x340700540071080400c1d0b40481030320f036200302e80e44c003019820781c200007107650061814030045003d051191703110b41600c2c84d507a1003020150004115540941c040040180b400341c8a902d0800060000c4407090120b010741c101030030742e910301540400d04903407469010f00100030042046080c45824982100c5a0702048540c820040e521824001080d1090381e0008210b20b11411b4046d80e016800080213050b5601c071800c2c0e400305000403580c81718140f000f846c0c142040400d8003110303481d031400350320122480d1141c0c04c00420140d03040c9100c46840003082000781c14108070703d04100503850811030307181030b102c40e82d03104010b1750a19502040e80040140401403c038507000c811442d849000700110721543c003000c901c05a03a50303120841d8602135040006414901c0742415682200707159004000600c0220300e2904500d00042d40c1412118001407170070036030b82130241c0941d0f145204060700045206a856469520b0701c88101c0c6002428001001e801001b058640701044c0515035858000407c200b00488078440b2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 342192580 1250 342191330 342191341
    0x904020f090d0b010603050c1e13091803020c06070803070507080d0c090501081006020c061b100c091d04020409020f0409030915080c07171c0b3303 65
    0x985125074240282e100d060500510704120350000040c1c140d401a039800d0015480e4401055040e000b0038908000e603070492084400400280f0340942030354581c13103961300007140c0d03a040d2460488400310030300303002c10704021100c209041e01006641e400083c1500d2880ca801010340311802d4a01001c0d240c02c0401c400003e40038140b15110713051751499082403200300a21240c107a00a0034450b100e02c6aa4046039a4800248444c2000302103001214800d402404174580c41c54100130142d4000d5210004070701c4c00e040c3e0000c003c00704019440010b0b02403400010742c070200c80d00191180459501c045080c44072540312444520082c61025049581960007107410100342c40041c04441901401a800502d4110342105050707100c00c00c101143c20103400e02c1c0e501d2030100700407101c0711000c4604201100b0704100b000001050003611078035007154894810f05103d40481c1c500740d1580c403182900c80c40c546030082090180703004146144250b030381858a1301d91030603051014a41840ca0710389500c4c180008000a40b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 342193830 1250 342192580 342192607
    0x606090d05071a04140405090714060c0a05101b020a030c020a0806040309031415040b0702030f1201080c0d050c040906020d021b070e04151a0a090c0210050c090402 72
    0x340034049500110f844115000808922070300075104011440c11203942500e1241450b208040c06507081c07901030322426080000300580c8082400d2003c1c0c200070104114560b641041c4122140a03208401401f581c88100e021003055800307808850228400051540700d145c2e80009039031003001d501d410075a800c20f10600000f8800105a0f001d241140501720402003010391082c041001c0e203200c1c1300e810303001008040c81c803541c5421608009078400000d40100d00415100003042d917005240d44110303454a00d00e280300700c1d00d42c1c0281003410310050012005101c085010300103414004030944104030311b10b420f07880b83d0740d54000b03078400d26010300d0391180d07004103004e0b4580450324415485a002d5580c1d521100021010300d102d0302041480f8012002c0118078210f400c980d0f1030183c0e41004004102c0990f4541d8207001700460a000c008640c680174018031075885400c41c020080c140074000084c2c0d54244200a4100440c520103004403519240402102419040c252450514159801600e071000d001c0004c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 342195080 1250 342193830 342193843
    0x3051540020403030807020105010e09150a230405060106020604030e0402131e03060f050108061605040e190510050108150d0b010b0304021003051603090303090221070605030606090d05 81
    0xd00c503a0300002e004818141c008500718002c030f00c2076000700a160703610b401000003e142a40c403c480358128a22151f030604041180300d070001956940055516600c0380d11600e4021801508400c0307046510800c4144201400701600600b00d40c0060100e070b1500740c0d001090000c0f00060b4500c544d5020401c1a81403200c4096100a0712041c4c9041d42000040e00300da0642c0d001e2440100c0e850390501050180241741e238010b49040350a03403001010652150120800e00e0243c0c1d498400803c44284400114800914440b500907228042d1403829000c143c440769040c0c8038014105c5550903d10300d8104060399000400c15886000391f2001c884007007020000800503000040054100c22201001041d618403080c0154020382c0b007262201c0907203d4900c0103400351542210004d1045011094840b0064001c3d00b04a0701503200b46400590b000466000038038a405001c45041124158110b40c0101c16007084880042d0171141806410751412600041407403040081c002d000340e00311101042000405c0050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 342196330 1250 342195080 342195199
    0x2070e090a170c0f0a081206060c0d090509090a0308011a07050f030a030b0a1404180218060901090902030c1908030409090201021908030412020c03010c030515 70
    0x21114840041d140801d80d0f0b4201c0083c10803903014818440311140000a041d00b0352540c00841c2d1801c11000343c50821401d04024102c0390000390820860300401c0b002d2001d80d41c0244d040d121508403034101018411007202c0208107120f10b5012014480109030405051030458015041e2400b0032182c005600c29107020707041006281703200e10340d03c08000070300200c0900b02064250b80c040042450850401c60100f10500c21041c41c4201520b0034800d03402c06811042c0581a103417008000c00320f081d4081060100c046c0000240f6000800030300209160141410340144044407091000c00410340029444514030481d031031040751603028150a814a010300080185a12010303030b925170ba65540700c100a08078018081f401801507000b4400c540308003900398800b0302c5d0000394241c190380da50ba0700d000107010300300250303c15449100700003403e541e070900880310014101c1d5000b1645041078428641000c0c404c280e03032842803461680341c0c0c01c1da00740359142c1221405951410b400d42600e80c80103d2160081205 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 342197580 1250 342196330 342196343
    0x2030c1e1914090f0f070201020906030408092107060815040501080a0302070f0b030403110c03030310180908160c0803030705030f0702010519020901090e040f0308011502070e090a 79
    0x2400c0d10704401400c0e10446681120b91074004401408104280c0404c803140e4000d18201404074510720228009194000380e107000040c6081480c00c0007541a4008580456003c48002201c0b9100c1c107005044010b015000c500f0060303c50011600107880361900c0c012401080460400644403d03002074001d030001101801c1001256110b2032110384503805000190b001d03200300400041c5600c0d0a2000c2002c032546804c1c03803070550b21650b9003162006040b0030513521078815104000f043c0e6030140011030042c0d101d17a90046182d031401c81d00d400803440064540c01e9417483c18a15a01140c1014100c1d001007501c800403045500e40351520140030b2090740c00002075884080104980c8071381000056000c3c850180101c060303541e1307500b4200e0a0f00e078121141c0d20404003071040b807c8002030540140c0f2901605040400c1a1034480b000503002c841c040ba4181e8021308001c0c2d00500781600a1480c8ac00343c0106003144c00100884c0001039507a95030340c8240000540315500240c80480f003402402c40c1258004d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 342198830 1250 342197580 342197599
    0xc15041406130602010b15040312050c15070e19140904021201020313061a22020912010c0906080c301503010c0504030203060f0702070f030c030b0c0702030c1e 70
    0x40080c000c4c0114002d0038007e5240e048081c554590ba2170075282100e900c00f0205902154004c0301329100d401c98445468a407250301ca14403801304502e2642c6219012a03900c41280810710000c218044a24110741903440100c1542400703034000752460402801e0060f1561000340c1c4551000c1600a80c1d40009983c0300d500c044140f00780c0f1200c00034508041801100b05114a00c081c1806006550703510f030800d07620104c1c02c0021015145c000d094501403124100d401803d0031480008650620390b501500140c0c1d95603009004601600f018050014005c2403500084a1510100101c002e01c22240c6003001c41e400b01c02e0041c4e0165a48000094012500042c40600c4c01c1190781030700d05080c1015a20321075400c000840c0680d901c03800a4030102c80d001002484261184001c00d410050090042c00c1103002d20701001c2100100c000154008500c9602d03404102c030b1540c104a460030401038401840c8880800003400541c0d0006850352180100704c0c1d00c0304400006418992108a000503c2c540001c4d005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 342200080 1250 342198830 342198839
    0x1121e03054005220f06031407090b0a031e080d020315040507050d0203040c030b040c061b080d0216021c050606040c0519230c0c1504140613 62
    0x1c207a0000c101c0e40c82400d003200700a002c825090b907a00103000d4544c0111034402c07030348055501d031003400d60415841c44002a0b00380ca101901400e44640ba00155518843c45050014024007001040004c1441640801031070b5000f0b000076150ba00e0750720000d0401c5184250b00504240c9038854046c036a548840026a2507041c030454078065041107685007000400d480c004e2805080c28001c0501c00c51550341c81615102c40804604000d42010340280c85c500d01107240440084c5003801450b009a004a080d07413403480c079048009011481311180101d0755000c85074458005103111701a0b460340c545107200503860b41c03492421400665420100698040703e01d4800d0b02c040c07000214001030003400b8100380c0d8911b42d648070512054480036100140018820070404c0400c414040000c3c503500c6c10340c503040c010544002104405044020894004010005603c00c1e059204101c8001d6488040d515020617003c0440e819105005611800200d024103d51081c46a503450044440610741c400e079195200c1d0b02e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 342201330 1250 342200080 342200137
    0x17040e040201030b01020703030212180406080a2d2d1b0602060f28021c14060d03081503070305010906060501051312110904030305090601121e0305 65
    0x40d68164003003850118404401d51010418030281c0f50590000e0000c403104418042d01e981c0b20f8141c00381046240365443d01c460f0341d00d00900d0001c2c26000c008285c02d82e000c0c200000503480d45005121000c3c021201481100c40103903440311102e030401b00c40c1c0102402000c0e180301d2800e01035079a15a04201c884000100b1003032071a40d000810840e071032035600980741c400036070b40e40b60240e641000e0b014a8034001603245a0752030011403041424202e02e462000300d41d05d01410380e00141c50060ba2242d1a04000540004500c911441c0100011a00080e418000046a161413210b403000c0c00708084000000c0117103080039100030000001600700c0309255502d00b0014001d000c0e80d1400c80700c90303050040c005015071090080d20a03416001d282680301a2515000e2141c2024007401150529100102007a80d41c0d01c030802d00348507078081d440100710761600b040702d5400c1c0041604001d040902c1e080b11030700070500e07468841d503642d211242420340058250800350341a001d01c6108031781e8180c49a4035240020b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 342202580 1250 342201330 342201359
    0xf0e0c0c0105040b24060d1a0607080d110702060d0b030c130609060807050315100e130c0b211003060504081c0b060906030414030a02150606070b0c071704 68
    0x49080f102d100401c11861484075400701800c061b0b200702c05114450011002d5840210a10006041c840794617140801040450b00321075016682d020000c01d0410b460880e0340540144000c01181c020310b4551240e000a02d24051104a50000e80d44e65680c008643c804100e100c0000e140108807052451841e48464040c090901070300da24541070010000398090b000a8500c00c0d10001000f400182c060418140b081100c02091640e075007810000014a813005500600c0c01004be015103603110501a003002b1168102c80c0c2d2001c0240e0004012401c20f2458401941c030001c2c0400102d50b40a07201c05c2ea8900802d2000d400180c0290325200a0004100460009081c600d010303e12140186070a4a101401c65800003180c40e000300b030030007484005181c220021030b4020320a0704802540861823004a01d503411801201015030310203c42d041d4401024101a035000000703d5026290004a584500a030200540100a20b0724089003240410110792003000c1c080f0049045640c540303586219040e034101b03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 342203830 1250 342202580 342202591
    0x6050402041503060f21080f0d0b1002070e06130207020907020a0b010f0f030b2815090912080c0706050906070f02011406010e060d181b0f0e0c0c0105040b 68
    0xe1515000007440b400c003104a50407201091541c2e0441d0090440d58406006c2d202012182e6a03810002180c2d0924040c0192020b02845080002c1d040801c1c403d0040590140c1e56400c01e560062030100001d007c0c0000c469803040d0241c81c080c0b0800480000880030380256040254421109010400c03641e0340001c54420301d502500380000b0360b980c3c40f074440c60000964000c1c0c540b0303500c4012007440440c0c41c0680307590700442e0882c40b540d2581c0710b4414980201c40701364804803040741c0b00c000100e0550040745900018040400c0d0800c5a65150350380d0740b001418a007808c000740040a00040c080845013030940342260740050061280b880d10300511034035500b0440e00000440c3d402003481802074414400c0500c0b040141440691071b03101c61005544220303070301e8661030b8000010081c0000c90401030103a84c0044400c10f4500340001000c0c0f50803c03905907164004002d100305c0c50800c002070a0901418400c0383c20340585410f050301c9001d00f50f00385118810b00a1025030801c41071108002800c0300152045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 342205080 1250 342203830 342203837
    0x1b02180f0c040312200a050d080703020a0c0f020402070b09010903030609020a0522051203090f12060c03070c060603030e09062d0a15080403020d0201150315060504020415 75
    0x41e5140d1040c104a03010324000903103c028250b0414542c1030003400c050000f41c1c0c484c41009440e060311007489240c0000003100b2a4180c109046a004154103c0c101070303001070312414150b00f402400c1e8002070400c2e20200c0041c0c41aa8a41034100a43d1210740c1220314154100c00410364600d000383e086400f8100d51f03081100000c0c80c00034005503802c05032003610391b8090981c3c1c83c1460000d41070048400c1040060f050304030680c1c0184002510765441c10511284603450001e5515503203081c0400c040707903550060070ba028021820391014000c1d2301041ca030341d201e02c510300303c1502d07502d17120b800f101c1c5031002281c010b10b40391910902100340f40c0c020280520909089032001d0180d52a603080c0116050300ea60300855081114141c3c00380342c109030703d0402e0801c6020f000315123025035591004040c000c2c88114080480c0100301403000b4154140a4110400c195000074400e10030f0b020041d03140c5107114070015014003010190105c0c00340c120341050f0300806000b0001d54075940c80d950002c6d107610030051001c011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 342206330 1250 342205080 342205111
    0x50a0f06020c031b06031021050f0d08010605031504020d0203150406081b01260709080a2102010906091101110c1e120d1206241b0218 59
    0x303280004102546070303900308a40362130180d00310070301225400243ca0190b40845a44010840440f0710403001c04540060110501c0e00b91141005414000316001c00459030704184c0222044c00c0d004141241111001e107480d80d1b481d5654000c003024214040702d4030b0307881400021980711050b402d8010314011280480d180c0311035658042007100b1a1528400c01c1c9242e04104145905004107400c00c1e0841903040c10080011242e225516000c50b003296940e0300c4107032181040c4503102c0d130300200c840003034602d540c000d01150525849400814001c400e0300c858070b03240b2580008186200f90401c2e562107a0207242405030071004d14146c84c40c8005200a5800244d002d160182d1a29001508400190003d0f100c1542d00e100b40e070006044d9803c07100900d1300514441001c5021400800c4003040070420b176500d2021056410300070b48243c80166001101a140004294110050b07503500c03000c46442a092150050b01c0c0084843d003101340451000e94410068030301200301d10460488103100c1c204a00c0305564 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 342207580 1250 342206330 342206353
    0x20a0f0501060f170c040f060315020a09231509061b06061804121407030801082a21011107021801060c0303020f040e04030f030b0f0102030d050a06050a0f0602 70
    0x140c039440c4c1010079034903500840002c0b4440c1090790241c2c60068400300c0104051343c882c0c07504a900c3d00040400c0e03001950015046140075801900c141c00781c00c550003060f10a0710540710804034000e40d484041d11070350450404070518500c0004541d24510040d03e070359101c4414901980c4131803c9440d10001900410000030720614180c680300161503034141280d4950b44494461502c24041c0582483c140401e0231b0000b182105144040d060b014032076920707120b080d03040c82940c0d070400c540c0d100d0182a1030640030148c01044a41015009421415aa144c0b0302c0343c6e200a2005440c1c3e042001032210307504c2e080c2c080c80044840c20007080d489009844c2401072081c0d001e100e000000092140c880010f20114544000130f1180d002041d4020362905103900303054403001c030342d8400b0006903002c801103030034003030795180312174050181c040d100a0803103d104002c1c102100103516481182e000c20344a84d51280000d403100b116a2241024040c0038100366100c61b03c5001d0001c514285000310005486007248180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 342208830 1250 342207580 342207599
    0x18041b110d021002031803040e070f0509130903030b1306050f0303071101120e06010e071d061e160506040311030f0403030309020301020d1a040c05091f020a0f0501060f 74
    0x4055590030350003444002036a80c3d00900030b400182003044d215203650040045404d04201900180151401c002202c0c180b941c1c02610903a0420f1035201030003401e1000ba00980d0721010080f041d03000314200414030018074642100281014104680d1128401c20520b1907003100d540140182c07501587c200c1003107000002003540d6401884070080041c038050280241070f5110340301e550440f1100c070b800070071383e03818030507089051000076000800c48404007000c03c03800c654024007040d46102201c60001038000c143c00070038014441d601c0d20980029848601c00e10000043d4210b440ea0303804800c4031844402140390658503040181c80580000d401844020300700c0c01d0110840b2000310002002502c0c00d4030b941d800750040c0c03c0c00c030b405030f90556003031000c690000c0c494010030580403842130780c03000c000c1d0034041040704503804514403108100e018042c2582c00d0b2104040209582600141d84a401c0d0160108900d0b00000b910020144000300000d001080f02c1508018107a82c1c100c50000e0b14151500c4401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 342210080 1250 342208830 342208843
    0x210905011e0216030e1f0f030c0e0306040206090105040b03010e01030b060909150c04090213081207050615150409141501020a1202070f0315050108070b03040818041b11 74
    0x300f01120003a180500024001c1c1d81d40c1580c0980074208980011611050f0407015066010000120700b010502c60748542e814442d4144202d254180720a1404040c0042a903582c0300420090054400141d000c1e44d584c02102601e00410008001680d603613103038410ba20100d2000e1100311540424680425021714295130010f10644200b8028000c000e9001c0100700070728000750059180480c20000815006038600052014400c035a80c0b40103028500040c07245444117010f481e6546030418042640080c401040c41070300500802d9540c02c01c0200140007581c0b600c1180c1c103850701a82c00207000505080c4540158060050150b001ea105583d03c0c51034641c146004c1440500580207003e466000501d100132520303038080d51384111740742d060f00c0f101c20007070030f03074072504217580520b4881c0100d040c3c0700c50381c0645805400c000d0003034151149080c017940301a0002400041c0164000304460f43c000d07251544040241d180103000f0301081698045203600d0403555149840026800c1b5102210780c4400a040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 342211330 1250 342210080 342210097
    0x60703060e0403080411090a1d0f0c040203060613060f0e030a030c0b040510051008070807080d21140430030b010c0203030406050c071212210905011e02 67
    0x1c01a4940d01c980e4201c800c0c0000920448010701d03400003035001c6032505c24560384201c1d065440051030084414119510080c03041c402d824981c04251050343c0400081240122160250340140c0c4a495085c0021618090300d00c0700c210788940c01c5000108a40d110060078861581074581e0701128295005040d00c8007560500500841d40406e4404002101c1c00306995003d8014010b4415030f080e81707010002520000d80389090b4818124600348074035001070083c20000c00601000300016882c0020007601c0d546461190800d03c0034020900071403582e180201c400e11040345408200e44081990f80810f900d005450a0300c00d5003017008214480591303000b0080b07000c40340300340041e0a20b90710002103014201b040010303810400d40d0007000d00142c07000c1000e44054140c60704c0d01605c0d44075000304240780517101d82c4803ca42c0211149901c1c0456050402031554480f03500c0c1240e10504000c0002d59015a40224202e44501d4081c10105002040d88408110070003495610303207200c0650304c2c8000368000d0501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 342212580 1250 342211330 342211349
    0xf05010c081b120a1508011a011d19031e15090201080c0c0316050d170c0301030f0809030f0a060f020711040504020f060f03040c0501050f1c020f0a030e06070306 71
    0x448100310308581070f280d0f01081481c0d02050300d101c501c0c0000d815588070352100025039100c01182000035000110480803410a2a1081c0d4114103411a40310400e8000d80c000c0c0541c684003140150310780349600390005960003140c0d40654086903c50714102040250094a001030038075408107411143d80181c81d0550f40507135440300b054460001440c1e66520503650300d00284000c00034582c00000d00b1110140441c0642d01500e13601c29644000703810355149454008007102c0c5003041021091108007501d06403608400003102012480ca480c55082c400d4035034996062250110580c0c2c0040300044001d076651050005014030ba0039001d011059025560700145804072841c4a2209410710382c0c05554070a0000f010702200140e11004504998041c00c80384034134401c0001008244401031001d04010102844c10a00c0c103201d24a4045240c060095414109511000c52448131500c54042d90301848110004c541e40d400790076806402044c91002645207402341d20300244902e400b0341702c1e25044944541 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 342213830 1250 342212580 342212587
    0xf0d090605040e16090807140f0301020306010518030307060e030d0c020d0e040e03041508010815160309030c05030a110709050108030a1215031118070e0f0d0f05010c081b 75
    0x804100d03801c80304d240001041101d400006480408000650082c09902d0107000768616240030f0000385070120701403d000368010001e00c500750360f0040c01c0b20007070b0264507441d0540d40c05a80002c0e055101e49030001e4600c0b07040007010700c1001c40200080003100c400040820158500801c1681c480d0301d010090b4000c101c00d10350f000454240754021100031511182030b00c0c901a1078003200904d1200e40403c1c0c00004801c08014040c94400308030034985a0f1100c50004818038101080081641d158040c03102003540301c0a030802014041c41d2101d10650b484000c4d2503c804107000b0083c0b0080008040800c07d120308500064401c0c10f900c04c890680398450040c0d49030200d0060161441da03c40c000c20305d24642d440c0303001c0140d8261804520084c45c410104410031544110030048000c0141105051a0004800b440506d070b8100e0303280d240314070003a140c000160041d0000180030203140440a041c209904a9800800c403065200303051080381a22150401c0d20b1300455125040300c51905194402402c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 342215080 1250 342213830 342213841
    0x102070510110703080d0603020a290d18030819051611100f061406130905060102191a090706021518100603061a0a0302040504060e0f0d090605040e 65
    0x10042e07503140e51211070440e048a5626500c2c0d00d00c9500440b229940d45580c0c850234811441d01031b41090041c0b903100c48240c40401b802c8400340003152020381480030080001100030307000c0c034146c1003d820b41500514020b5500c119080c050030b03a1070308461404004501c144605402203281c40b81c14050310f0b043c10840070603c24240c041e10a10044944c4c500248180c0610242071001405900c82c2d4102c80d16010404501c3e22a000480310703044551980300d040300780070310b41c034080419000754200c401c12040071030349840f43d07070041c1c1c1003043d00215540d500d0141e05410040c80707500c1c0000082e10719401c1104030b0381d50301c2f0085a91a500a8011140181c11400caa034000c11001450190401c81585d46040c005103610721040c074000840210150130760715100e0420501000d882443d403c070204100c4004051283c0340014507010850000070f00c0395a81d04042400d000b101d500070401e080401040782e25581c8041d1020341e48094544500c0c0020310070500100c0c015105100b9102100c040000030300310380c2c540303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 342216330 1250 342215080 342215087
    0xb010e0a020a0e0607050c090403020d090e060d0f111801150903030819060b071a0702010501080309040e10090b0f011e050d050a020310150803121906150509040b0102070510 76
    0x1164040d80d40c0c1c418240c100c045648c85421045c0100d1003a0020038010b01c1c00709000c0c04100c0306501c03a110f40c00e203d400b04415501d4003034480c01840e60219210814969500e400002e6464088106401000b21103c0d450a02c1d440c006490586d03082040380b50307400d01c2c0c80d1801c503802111408014000b0701071001041005881c5070b1a882d00409406000c200d490329207100a60310b8019900644003510407a28021070081c4504140da0400d07100d100030b00456041c80011503407403203182400c80c043e13907503900c091000310002e114044c0e003040c3c007640a02101d1801e0900003884002552448800701c01103000094680d200700e00d544010702e5606013032610603c0c150070080ca000d0f003440107a1b5071740904851040180d038144004001d503040c05800203170120201c5a4410340da81c05400078070740d9a00803c2005124050150708980c828068010f440c0880c40c0440404084d24495102e0390300f0031041c00c540c0d1050b581040107007c1c072140903a810092816030100490382d0341c403240300305901702100c00d81e1540e1181c032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 342217580 1250 342216330 342216337
    0x905060d020c030f09090604060608010510020f060a02040810060524160503040906120b04060e0304090e03040e1302130216140f060c07030f030b0f0301090b010e0a020a0e06 76
    0x4080e0801420080401c2505003190f0140181002c24440010420307114900090711580022040c0ca040240c9030802401600710300e8180a114821b229032442900000d10820643c0350002c1d401c001d94dc414140181280045d42060084690a01514021900648040c4105022181d0040800c118454106904440c0f03a00600c0c0c01e0510036401c0120a081401881d5a245003d209600840c0c1e158078060064080320002d4000f01c1d240d0444054001c080303044801810341154100e080000c5084076044000c0c5184281c0d804a005182850070765007200b030340070000d4021502d095a61200781c0c0ea030404210001499580d000394008524410071031440c0e13180d4041c0c55000303401c0341c0403000c054158071400c0c01c404800c15480c056a01c0803150605104040c0180791300420b000c0e441d5424906a40d401800d0345422460760300030940d840400400654074000442c90314000a002081164a41c0c1003030200004240515505d50190001044205215208582655040c2ea44001200c1814070810009a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 342218830 1250 342217580 342217597
    0x3090a0f060e0a030c0c08030c0c0f03011803030606021006060c0f05031c05041e2a0506030106030507090506090109060c021201020a05040303141602090603010e06090d03061401090506 81
    0x5959a260651203002008941d030044d00039254800300c030500d07140052203100140c105c0200c9800c14064a00f4254001800e4140d050040720100445018000800d00420500220442175614842c90106050f0541d0180c405e07600303d54250341c1170901d2011482c040c0c51403845040001540d120300324011540d540c16011141c0d10640507640380011465101a420301c9044021000030b640c0c005110070040d0f0100d90000701c01c0f40c2c0d02c18184110103030b2960041a451440403046020803403c0442800c110b0601160107013000404258480d40c42d120020300501e800c48003140030403c6018081440d1422000340d81010380165606594541041d4080350b002148a1049070440086541c1451048082c0050111002c07a03a8409032110314600340100a841a011000d100c440100000450900162100040d0940540701c2c00f80c07a032100c4001c6801420020041e000138052841400160301c4045603004050b150341e43c0a0018076142d0488101c0d10000188250104104510802190070240080c00300307003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 342220080 1250 342218830 342218843
    0x60f0c0106050307080c01020f0106030803240607080703030b0102120d0c0c08120412170c03040f050f1b0405090c0f060c010f1508010e06042a0b03011a03090a0f 71
    0x10750b912404a450072105401050143d00314000280c0296070400420394000b070088020b114691031074a13154a18403014203500aa4101d1415200c2c10b00d55001c900d40d0100c402070089503540d05182001807498000420440c0020705003481956250710001d52840100310801d0014070701020318a040d001403102c03d0001d414850716406034004a1807041c05040551050f200d940d807a841c2a2408294200c14035581d2000c2c003c0b803600c130b02e00c0120040701030365000703c01404440d039a490b43e00380f260400020380402012446011001c01c81a400400d0aa20103544010400241d4400700300b04004d50714111543c0000e40c1c0320480c20016440c3c1014003041c0e10b2000751005140c0403010985900352070124086400f2b081c1c50724002d00c04044d9520084004003000d4008004596006d140c2d00c2d00c03441c0c003800244c00c42c0e62102014203841d100f0070010080d40b0018000d0061156070b00050111904240b040c1980b420013540055031107000c1c541140c0c451040000070b0440039585658910011240e0382040c0ea0700d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 342221330 1250 342220080 342220091
    0xa0b0316030f0309080a150218060d0606030e01111e0c07090204050306070f020a0312180609140705030d0f0c0b0901020318070f09020304050a0c3002060f0c01 70
    0x20001420303400203035001c1c1603000c603180e8003410040c0200009900c040900d80c00202c449000c9240c90403c000540301c0201c0140e5034460001548140c50341001000360b01c4480014a2030742007403543d000b08111142070f1011701038940b050001d94220f6002c0d00880d8462030301001101000100c0038100740a904c00e05640c40c2c01c01c2c00c4100110b180c44110b40110207080c0c0d000406000a203810001541d0200e600e00d03040620f1118054000c3d1141c501040040c1800030351200d03900340d000d041d00f003c041d8102140d103102481165007061005089030aa0a0f9640d59041c401d10300318005c081080425100c000d402080002d41c3c201c1c0496072303a0b004824810130003080c64800e80024a90016282c050181d0000160726070618884840048a48000b2034545501a0504200501c031a00082040310056000161643e0703450824905200013100014002820101c022580710f500300080c100d041c040303241007070403444411807400310401030700e41c041e40c0004140a0300c90380051206c01409100c9a08002180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 342222580 1250 342221330 342221353
    0xa030813031406010e09120a0f030b100f1407020f06030a0212070e01020d0809330406090c140604030803071707050d14012108040f1e120203060a0b03 66
    0x2003580d00b442d42c044464118000410090f1100e41146800000210181800d4580d110342c030703103062003981c4010003408401e25109499602982c05110011000b03081298107510b1910000c19101d4604050404600310035441d03800d180e8000140c50711994050196070082e5503d0041007200d130002010700541c541c080240c0303040710700c0018070f05002d01107646402d190075440200190a0215105030001004500f07010465004800940014091000c1c0c5441001c50509059240607000ca42e041040034405082400300300859071348400c545a0150604064a0351244a4260003d04101d06140e0000c8144014008070300f0703200c001e540101c1541070050385a00b42d41d20754842c43c80e0440b100000700b0404103410509032201c2c01454140c41141408890359070500f40ca50414490714070144c000589450242005c0004440484014201c00c80d1003c1240d42e42e070b220303c00503000303104030320109506007000081c070000c00900644425038020054699642c40002c540c009100420b84140d0501c104d880041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 342223830 1250 342222580 342222593
    0x60a0905040f17070c0608101a09030a0c0e01120305030103120e1809011104081518030c0709180302030d15090614030607110307080a0302120c21060a03081303 70
    0x2290f201c2c1e4003902d540b107580a09089a1600d101c2e41b0450520010030108544c0c181c000e11350806984004041c5002840a1503d0b445103010380e025039034040c81108044418058411300d45001c85022504900b816030b02d070a0250101480664003d001c82d0050005000141a04000700d00c00d904034503204114078256000580c42800849038800f1880c448414800d500300280200e01d6521444d416a40c1b4191505e14803d544940c20311074005120000e002203411002174030302c10308824103840c0c222619060a101c3d495200d04040c868801038914080720500c0311014554002005500368000d0360405c0b29040c0b02102a117250300703c0203045840241c001c5800a500d104901c06090040b480c2052a1010400c0c10f03d0000f018244c0e00a00c1910b81e0044101040041106c01881d031004901c1e0b224841c054056001c1c2c05000c030a220310b01c0e4403c0410000c40201c1001d44400100350b100302c44219182a1386c080b0b040816140103402954402e400d03c08a0310034802400011910300d002c4000300d0f500d80f2040b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 342225080 1250 342223830 342223853
    0x50a091e02180316080a111f08010e060405070e091302030f01020405090a11090d0510140a0c110309010509130f0b03060c19030e1615110105060a0905040f 68
    0x7280c0c0348080e520a441541001c000446141d03030300702c02c1285134a0400d02100da8030700f18100c0003040282c030624808174644550040101c85040030150700f03031941d600300300544261400d0003000181c0c41c982001460a20741800340c18041d04460b00d80204040c1d0710000d00c180c81d10700409120282503003560800060310100b028460100f8008001610f0b40d04060400ca0740d160b01803c0e190700b87d42040410500114480220342c0000e42c12903404502c0202c0d40740c0241096031802c1c903a518035162042e00c80540044021691140d002c0007400c000100c4c0041040c0c4a104407600080c2c0030354414000084c4e15402007005000560006219178039900d101902102915440d40c0da03078580c95104c2150b20320070300f02008925002000065441e04005082c8100311440e00e4074124001015110310002c0700c0e620701806103c00028114507112502c0d529525920744008001062400290750340c180401d0080c1c0c113100e528000e020061090b0741051511090030302400002d071040d070303c074803404992030000703181c09010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 342226330 1250 342225080 342225097
    0x70801020d0c020f03030126030a0914121b0d05031305240711040f0c1706030f0703141e0f06010509150904170a0507050f07050a091e02 60
    0x36070350310000c1d80c0d050261024030003020305541c00342c0e401c040c800c5404002c0d40c2c1510000202c583c0341034502003400e1910340b01d80308001880e0000165034005254040150402da41c0301100281800d00b0900a0003010003407041000c14540200076010707402d110000801d0101c9c0001081080c1d02c00b940e80741e550170b56008603503a0f14074030344032501080142802c44c0446507454482406101c00703001011220382c5807190407002041c044090901a4041c0e81741d91004a10354a58081007251400179a00980000414078201c48810032a0000502c07074a40007c440c8108034088002e0300b030081c41c40c0d550b04003c229038118585a0b014450340f0022401c205500d5036540d007800e400030400c030880d8a02282c00c040f810b0300032a006e141c80c3c208010244030341c10041108801c060355403040d80c1d502c6041c031042d142441001e16010781400a840030b60998480040c2c107900b405041910108012411850364402161141c82e41144101c2c6040241051943c0002c04801d2060f504c00ca5410403180340104130f9100000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 342227580 1250 342226330 342226333
    0x2040e040b01061119050312010902070b0f01050d0b1003021f0f0212220b04140307080105280608070b031e040203071e0b1306110607050304020d03020309030708 71
    0x10441844100c412003401000213081807900d43d40300080c044c3c0c030703989520f011101291074140c01c0402c100040003207a20b0760340080d0103000c2a507150800b04020394000c480c1070316106591b01c0400c2196242c410800d040f2796000b000000d8801503951a042240c100411000d11140804400409070b141c00300e0307044240000030b00c83c6100c8040900080d2140e800308003805d04551088040c02c0308031645c88205c480c0d03a0401100180d080e05000c0c108140480503401002c070411000c6400a41059441d04140c5e2a88088080d20300103600c540c0c0c420700300c6900f119001014aa0701c90b80c40901011502d9003004015106008500b480e259400640340c40328580c031001007600004100604904040910030400710109441c0d03200d400c060300020f9480c4014042c4250001b8a040189a0090341e04190b4004020921215440b034012070302c070301c2c4061000e203d07880110308a014055440301020440a11030350a80c1c88072400d585031078003800300c14940d0b120118154841045034000d15601045a50010b000440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 342228830 1250 342227580 342227609
    0x3210b010824030a0b0402031c0c030818070605040602010e0606090103031112031302040f140a05070e0d1505061801030b04030507150504020f060405060d110f07050114100e150102100204 82
    0x10505181900da442c0d10814089c100342c00d43c0102c1d5100c081d484180d605407400741400e440301d0400d41c0448420071903500e01807041d40c1002951a0700b01014104a51a1b500204214a00f41038600d454038000c48015031700180c0c540c01480024014030034114074010b920700b110751460303a109244800c0d034800e5800504034030718080400d00710702d442c0c01400410413480d10240850f0b00024145a0951000f03000d41ca00750b6182c5000a60491103018030180c803220042c081c0c60f40d208d1a0178145080395010a00203100c03030400c1c00003801e504011100e80c401c4084030506072050780c42d50301c510304500740140c01103041100802c05c2a01040d40e0b8850160700040c5260f00068904041c03041141c180405844240221006d02c4204140d5858100740c4540c4a41c003400400d01c0b4180200f00741007440740d600241803624000c6041030502a0551003507150081114070364241c1d0b00d581d0003031048441d02d031003205000b02203800010580382e010482c0700565507060040b900010342552210050360070a0300440004000760 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 342230080 1250 342228830 342228833
    0xb040b03060411040501052a1203270d0e130203010618080f0c1201061508070201060b03100311030114190b040216030f05120403210b010824030a0b04 66
    0x80c40340320501c2900700101d42c5403c1c5403500107010b41c0140c0b503d042380a0107002c1c1d140407180810b1180e410f000810b40035505440303154001a0041d4006641c0316150741d00c0c3c1d2042c1903038460a154a03101c00218a001800000401c100841d5400b515181c3c0f0390304606561340e1300840b00345c02c1c005540600f1260315071158001e5808100d088680312a44058840d50100500d1210b0600100d5180a01d070002d86034050320f2280690641c0c0940b4581d4001d00031103000c000c40036403141c0c1c442083ca0140000b40d000b8469647d0b40c0030030020034041079951400010032603500308001040d00e501440352000107400444d01001042201c030450b01e080301c044000c5e010030003101104c04058402e90382000d004070303070450804440b050f800880107100c44004080c000c0450030000103d01800c02e48980580c2d0000700c2c1024986480e0081c401c00140449201c400014000c5041406241c0941c1c08109010395030708005a540c200080c541c0940d0346c012900c00c56690951240039201030094500c0c40340580f929101c03d0416 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 342231330 1250 342230080 342230089
    0x606030b0301090b0606160506090606090a06050306062e0306090609090f2405071e0e010f0e010e0406080109021908060109020702012f0f030c0601090903090b040b0306 74
    0x4400c031030720907407403d40c211002600114001c2d030880340a035001d43e15000014145a0240c101d404003174164411030080240c20400046c00520840068509031426113814038260f0a46030300b4040c00354190088000035060781000c21800000f0444840152060a0a1448490100e10b0f03404c882c0c0c0002d40ba4001402451094014607004290104003041003502689407200701344901c150042ca603c5451603c03a9205d6004144881441541d4100f0001414000f1000d00100500404191301060302c01010580c00c0c003413201d0001108043c1c40c4c1128400d00103502701d8a0308100c060941c14806649104134098460303114110240c003481d400001c2200c80390040001603c501c0e001600402e10281c024000c152000c030f0340c907045423000d50000d6215000d0740300680e81314140c40354031080340d80000b40f5040a40c0516400c179116130002c2c02502d2440c08800c0d29251a44212100844a503002000401c1000600d61008400e58021302c1d00c10003603501c0d030414541a50160b404100c0660002c001c1c4181483c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 342232580 1250 342231330 342231341
    0x70305010c0e0d020607051f02070b3d080a0302060f06060715020a0516050307020a050319020f0a050409050f0606061206010e0d0210050a12090209010317120a060603 73
    0x5a0700b041d1506078602e82c0000c090300f0746260000e02500c03002c1104002c10202300a000c1840040c56100041042840340e440c000350007801c02a00d00840c040c01280c1e041420707500700f0014490b0405002504080041640c04904c0c40404a06102680110001ba442c40500036402c1e03842c0f099000c1d00581c03c000c034824a1340d89000d4040c0307204040c2003055a0000e201d48501d120001441c03d07000d0385551280e9810781c2d45000f540710780c80310000d1400b80481000004030051050501c03c540a0a40c541c885090541d50b01280600b05091800901ca0341c001d4649a0034044545400a2406000341d07221400f00e41600c52146080b91654003640c0f4461002806011150b884801034884504000c0222800411040d0181040d4103120140712200d1003611032203250b0950329000342840206418180300242594407080407840011255051685a080d060080740300d02d640080201443e0303425a1241c107070648903403100281402040000702041a14020310501c204002100041c540c0d15200c030240c00d070f69 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 342233830 1250 342232580 342232601
    0x219090f0803030f0a0f0c050703021c050315040209030a05010b011103120109020c0309041103070f03060b0301090e10050f10051801060f021504061a101b03170907030501 75
    0x5146a20902003644008103599010310304c9018101e05403960401c1000910603034019030300b29403c01d00e0b44601140c2041c028480c8911a078215204583c2d000e43c0000e00c041c01c000c0b5640000c40800c0461210290790318500c4201a00400061514100c000064a402000c60040700c2d80c0e51240030035400c030341e04001610074008494001d0340c540880e04051540b030440c14002d5000300c0c1d502041c031030443d030782c20800c1e40d5a031803001d001003040e08104040c01d07047d5002222000005584603c13030001c01882402141c007106c007038032560307800c690920b0100700c05040c1d450741da454a403080c0c140545025429000d0300d4055104401c101080f820005c2140c8212074168001d140a4102100348207502e2122202e0181164414a040d4040050f001c80803030820283c51108000020000c0070f00081c40411b50088114007045941c1d8100e140e001000c4c4010049020203a401044005481002403882d40c40c040d81c03094800c1c5800075022444c0c1000e1406d4a1080d02c450030745034024002841001130034865a1940d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 342235080 1250 342233830 342233849
    0x2240a050906010317130b070b04060e0a1a0a09081809180a0303051801020d0b030c0109060203040e04060908070b091e071710051906050609060403060519021909 71
    0x3903040da12001715080d06071121840c1c0580014110895501c242c2580c4041c3c010324038003a07614002c6041090f201c0c082903a080d984c1c0c80c6881c17650320071214002420024140d1018100c41c1d0b0005400721011008002072035842495241c0b01000001002c0100410841c0c103036520710154201c880c81841071200c4003c0c6407500302c03020194110313008080015400b01041d4145400716039652810b00602e909050700c070000340e480d800450508001d84942d00720401205050301250030b4070155074011200000a44070f4800580c001b000244610140f0300c0500780e006004100c041104540317070f035580c40703280d014440643c1d140f5613503070a100c0520001e025840860311010035003512210f14110450f03c1c0c0e4202d00c01c5000030000d0320f841003214134090000384203100300d6a00821092900007a00365207030381500c030b00b08011303442c12001060030300e000c2003602d1082034098565800c1504541d01d8800402c0080c00c6a960040c0559070040080c0a500041400000c0c0e4041c4802c044504840945101c0c1d06801c001c0a1b03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 342236330 1250 342235080 342235093
    0x1005030618060108010c090b2a0c1e10081506040306020705151b07050c06070501090b090d09090b01020102070203010e0d12140a020f0705070b090907051303110102240a0509 76
    0x52544911f02106031100e48401c260354000d0f0b07010080502600c9008038000d00305288504079840720220f4a480d030118296410400c811025020708244000002540d07404104901e50054451044896907032140703242942100340705625000072541c0d0440e6108a8400b600011b00c9020410706001080e01138000704801c002030b0a0500d0030f44d1000d9542c02d0440d215070004140c140501408000101c1d003400c0182813140e9030202030602134080c00e14141c040d0f0701418000c010581d401e00000e00303072105c4000c40c1d44130f17110103090a480c50042d000024001c1e046640900050025940a10458a00b42c80100c0145810000d403103025050404000c014143c00e4030340404c524404503011021580314140300380040e40d80d985044a1074050007405000341c02441841008140d1100030401820504000c4518081591b82c554040300c032485182e05101041001c2403041000031000c440340402d0403014010340b6050032001d20003000c80049040c005600700360000503c0118140e82c4503041c2c22207285c90140c1f03078 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 342237580 1250 342236330 342236351
    0x9020307140a0306090609050108240604052e061d0102100b0d0b0c030105040b06090f1210020c06041e1a040204060909080d06090e15100503061806010801 68
    0x154007070449003150102070010351640764600c00d900200140100d003204000041e01e542c070b404000d0000b40100d58051251104d4421749910707290f0001d120003e03800307221149944200600026050281156243c405160b140d94100901c01c2d4410201e5a8458000c09076180b50800c02003805040019814461200d1008028580d0b408201c010852980c0b03040400c4400034000804c00c400081c120103801262100180907072000900c00071812218111000c2c8078003038142007000417910410032a960301501c0328620340e68904100324141c04080201c425144500001444c0405991001b07015000d5a049801000300b0019030406403400c1c0654a64100310724944c03a5241186400020030f014004540f0740c001404650321a0406070240c40c0f41c1c5c2060054800e03500c0e10503000e8002110803c0901d04044000c00d0b421001d209034040303000744da00249070805c059032600c10b007410702800c001c0400b8940480464151000c000050190030103080e0031802070881c41070380e03040038010703001818564100040c1d03d6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 342238830 1250 342237580 342237587
    0x201110406090614090307030807060f15060e03160603060512010c020607050c0111040605040e15060a0c030203190503010302100806030a020120010c030506030106121703040c1205031309020307 85
    0x1640c42c6400c2c002640303100c1000486450041a1005e5454460300c4008010481c1040189c8540d07486510103001c42869185c1450941d40c05801000d000005000200b007080c2c0f00f00707004103203440040c0a440a6102d01c00b101c51302003441760403101c046500c40388204454144142c8441c0d4450215000b000382d600b490134000d468200107021401005408241c8486181c401c0d48400210014290101c3c2d445594860143c8142c01500c00c81f60a10380000001c0c6410605d109071b6140e19000500440c40d21038103200680365070440c1c036403d5007184000e1002404040c400040d408401c1c046407902510ba42c55841048081d1624900d1a0104240c01c020b000154500007034a07014140e09007004070190514161074a104080382d0341e103000d59820000320b607951039010303400350b80541c070250300912510392188180091100050002408918160580c0e00c4003420840559001440340d24002c1510741d40c1c51103503e122101b904191810740000810f4100c00076000c0000f0014001144250b055152000015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 342240080 1250 342238830 342238847
    0x30103060e0709020403050d09060f090306110c03031302030c0d0b04032001050a1508120f0309031303030e0a05180604051b0a0309140c0d0f0623070201110406 70
    0x303140545480004a020105012000240c01040e6045440c0d41c2e6905040d07980350246812607011030340b44240070074030521500150316590302903103c01030b480e85540d803014001e0095410040c00c0b210180904510044148000c41c0180c0c5840455141c3c440580105401c000450380c05505c0342c0403040e420000214501e40b615440b582609201180b030142520a82000707810780031003001c0d54a0101000100f8003aa4003420184e20524094061b542d00d40b220b9a540303020400b2640359841d02482000454045040203540c00301c1e541c1c090341d08146003500840050030060f001100820304003408180e05003818800d00b4010041200d038015131040c9081155041480a4491800381d0703145d0707000444502d110440f200802d042c1210b4036a0340c1d014004014024003c0c3c0000703c1c1d100c40140c1d5000c01100c00095004a90100284462034141072503580c1c03e00651480390031075040c0d8441c6003a2408544104501011800340602001e00346442c1900900315100c40640001000c802e0009121966000a14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 342241330 1250 342240080 342240083
    0x607050306100804111f09090213141503040803041b06050f072f091501020c130b04050a050a0f060b0f07060e03030a0603050714030309010e0607140607091a030103 72
    0x5001139200c1d030070560783e118580c4454607006104080191007091460090741a14829981c03922181c0d03807103002c0300c0c00f07901c40c0c40d248207550300c2c11402c02d0020140945a071010094000d05541c8490a400c0710419540c0040301d058502c0e18022080100b441004000806003103007c0d1581c1c5286410094082c2450140c0308284100c80300c082844410028a2040490000000488844003c200c0804c200b0758000f903040c494095104200808c92040b4888802400010141c0141c000100c406e01030182940d0b1003500c80c0c510701c1d1514032000b40e60301e95101d0300340221503031600401c45141c480300c840301392050032910002c1c281c54007608214401075501030f2140001c004403441e68400c41c80c285480584441c2284000030b000000510060071400da0001c0100c034031440030342e401d26a032200c280c00e07010030f42c4c2a450303015001000241c28075841001d6401c510440200f2042c107058680d04c40303207002c040303103106455641d000c00240030301e060f04140391340b001302021031404d00d0746030b502c481d05410360006110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 342242580 1250 342241330 342241337
    0x5010f030209190905060102010c02010204030b0117070914011a09010e040e120313060e070605040302010f09230f0a240306080f03180904034d060705030610 69
    0x2000c078000c0d03544111007000088003c030f480210b19110030f0060001c180945035140075610b0310b0555040350b4010300942d02140d0700f10030010000da20b444031003030115140ca84500385601422001060481542c0704400c202e02d03003444902815814a14070220340880c85c0e460600d00b940500c1050300c1aa0b00c404a5562030900341c8000c0b51a1007460125440d10901e0400398906a9010040011000150052000c01e500500742030221072410040aa00d42d4024050000040d204101c28400355002d40a0140305034000d00d800f00b2210f6542030501155007225501504208005040d04020720307007030300f201d804040708682c0050841e103001100900750301b45980c0c04074168943c00c0741c0700c403150080e409070b030003440c4820545c7d40824135140a56100c0d845000184241421b2420808071410488041e6118641c1074031052480d98100071030358a1a01d40c00d4100d040c8030441040400c0c041510300c08034032260303021030145a81c4880541410704045009104100300003007441046155942d08603d1040a01d0703606 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 342243830 1250 342242580 342242587
    0x1b03120833030f0a060f0203040f0f03051b0a03090e0105220e0d17010e0609070305101a040e06030105070c14071a03011716061b0506010305030c0f0705010f0302 71
    0x641203074401d05041125505000342c1a03101116800807910982c0300d0702c155420003440c584e84888000b21300003941c014164488107186c113070005046003101d8005a0003410850b00b492a041020114001c0140c1ca503a250381040d814042010b4004034903102405143e003112180b076050001040000d2440c5200500501d1410344904c00008540c0c850350002071081c0941d441c030070000c58007030015680158503280400d201c4d8000102ca181d2642c0b4503002d0400206005180e48600c00304401420010f03098407880c081e4034100043c083e80c80800d00a80380010b4641a40755031a20303024030100000100a28020707410b003020403c0241e40a03902c41100c99200044038038602805400c60314059803a009072842d81c40d10309480b10303442405005503040703c20f100701420300e601100e5242512113196600c1d0300c10001c500f1405008440c040c038427098103244039420b01c200c0c0d41d609840b980d1a0823000c1c1d1040d141c5030000a10200c03260001e00c00c2268900110000b0809035151134002449014a20410b204051307012 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 342245080 1250 342243830 342243901
    0x80c070813151e0203040302010c0203010e010606030506010e0f06070f0c08030313060609020a0e060d0b0904080c01060b04032d050a0506060901120b011a071b031208 73
    0x224195045925a450651030242e01c80d40360801070024910280b000c82e40306014030f200181d1a2400e14441c002640c080c6040c00d1466005481c0c0d41d00368401241d042d500e60084154400b0248506802009556004901401c280c00090035203070b166140d06005805010301101c4c951a440101c0d084551300200b210902d1481d405c01a41c41200b0f0b800129643c000041400b40c03030154a015034284d54043e02c42040303841d543d40c0343c0400300e01c6511461408190042001200703031600700054004000101000304080100c00c0c0010f06170340c802c031403c6885135404200c0310306a031424851040a041030031081c601d003a040d601d60b40c0c250504241024101740b213013060860042808005000d0081e408011910300b25881c0c0741c01c83c1c41d00000c41d03000340608411000045c541e0404129080015044200c5d6130490f4207140034880081d414481c0201068030410281000a101003685042c0c00d42c2a00c031300c02001c0c2145000c102c610305000c0a01d007040304010611603400c040980c283c00c0d80c00b10030300c0035444140c0d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 342246330 1250 342245080 342245093
    0x60402060c0c0a06020609070e190e01021606020403050c010203040b0f03090705121f1506080408070807050d030e2a01450f030f030908010501090b1906080c07 70
    0x1840e640c00d40001d10303c0700c00078810b038002880501aa0401017520510341c2c50310110100c54402b1110400001da1042c41003900100707562040d542c04003c000090724055005020403035100c4803900448109600040030424403406103d80d074400303102440035618081c03804410103201c0c0a460800001d2101c00000300341000410040c0c4001007602410713000724175002d28035940c0c85807042c1030100c50142c00100c40f003451404500c40c03803810700389800309440100c0c01c1200480d41010000c0044036038003410080240450003030700150003a58840d0006103d02e12480600038165807442014000e03507408180700740085900a00c005078101100c0e6403895000c40300c070b00100c03030410000c071826001075180e004078020200c80101d43d840c001d10440640c01500000400782109091900c0790307d807512074500d014000929003000172150a80245008000e2580325400542101c40aa0100c100070796103809804d2a030604092030043c1d21080d548038038510340b0340758000d031280a0040141c14080d400081f1001001613 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 342247580 1250 342246330 342246343
    0x1e031e05011107060509011401090908090d05030703170606030a2c0102043308131a060109061d15071a010f0b040303022a04020307030f0b060c060402060c 68
    0x40000c0244445044072840082c00c0c0e02c03194042e20384034180400600d81c00c2c0c05024600301846886105225680b070701210200401c40d510b0221845c01040080700029501c0b4528541042c3c002c1c0042c6696440914014090b4102c513040061000c894104022080e83d6000a80781e1000a0584c0450b4082680e0b0345010040080000c00c0d00000800c9041c045002c030550240040d00da00c541e0006d4500d070131020001522044aa071220500d103100307801c4038001d10440003c4d410400d244003520a8007001e40d0b40785100d60301a9a49030068590b0b070104a0300b036030300103100300007060389040480884102401c504007020398801094000c813901031144000ca140101100c2a00d13411001d5803040c40140f220598800b08280706401d1660070144c00490005d424004403002c40e58141c00a1606d888101100507a451a1541c129103286a84885103115181c0740002c62040c045a0f500081040b01c051410b8200c44903141d84070301404091158120841c80020002c3c1c0054040302d100e520390500329040d81c84e2070b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342248830 1250 342247580 342247583
    0x10b040909060b132705030f09010e030604050f01050c040308160c0f03050616020c030624100f0306060f05121f0b07050606100807050705210a03061e031e 68
    0x850a07590304000039502d070b008000308520070100f5545124101c440341d85c0b0290002014155401c200120a100340b403140080421260604080c0601000340c0700103030901c102181c0070b030350700c2d004040911203000b07003032003100d1340700b4100c001c4541041d0554903403580324021030344081e503002a4500c0800901c108128441c004109103e680c0f00d203140c50340341c8070ba1102d00c140d0380c8a00d6002441002c030300203400807445800f0300401500902076a80d071841551089000b201500f404146c900a5030003182c1c840303040da5051a081c6441d0911800d0418a000b000c0360079a0340641c080111003482401440d50110840308003400b551505045038840d4a10240d5071800c85105207001c50049000040000c200b0000d09903c901503000e840040c0c0ea030809005030102c007840c08400181d031201c00103642a020384040c040090081003103610700f0315880e0802290160a0140d42c50021020480c26022941406124050050030b4000c850000e0f034446848000365080c0402404404015019800300f00d101c2484038845 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 342250080 1250 342248830 342248839
    0x6070f050a2d0504050f0a300611031515180a090c1110020301030c0905090309030a230a1101080c0f03010905040303060b09030703031103070b0c0405010215010b040909060b 76
    0xc0c0e000143c4607500034811540540b4410102860501d071a20280c011100300e0300d281d100c6480025103034800038010000c8100960410310041c808501244190203104266014055480c108100c0015801a00090741d922680c94080c3e80011500d00c00252030030aa00b0720301522000c0344010000c1c88840c556000851034a01d800007a0544640c041c04500540d503081007500e280584a02d2101e01340e22007400050503490703980004003c0c0002c00d0f0b1010740e102c00b0400c15070303040c20740400000307003008124401601c0104403108007800082502e410700c040060401d0091101024990705c44000e03a89050702c59041c030501900041c1640c0118084540c032a4140c00c1172030340d960b11074074035000800040e901034001907c1c0c02404510311502c0ea044030b0596000a00402c0190b00e0350f6021a0b54a0381c2d101048070700d00041c08450b000035650140309000d481400700d456110382c1014002031401c00f134440d072040c103112104010006841c6260458060310741c02100070130301c65000d05184001e1301c403140702c00e50003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 342251330 1250 342250080 342250157
    0x40f0317031b16170d0501061803120909050901050103030f0c021f0e0d030807030606090e0f06040b1009140109050a0612021207020a050c010e03070e0402041401061106070f050a 78
    0x5054135500502c0c1e5030380301410401c080d07600e13a102101c40c880f80c03c3c1000c507448403a41050021070001601040158283e240c80f00810351684903110a481d0181d8840d60ba5a4481c0c00601c20190025900124030760185041c00d00c200e12170f00007412035603030608070044042a010001c16036522403280150304520242440840030401d00e40101502021181240000d2030403801103840d6209082c0c0d0801c0321041c520f00f03119a100d400684100f54009080303d03a0155440b58041040c3e01c0746000f01003046040d44402c409076140107800741840d0080103901d4100002e011060245548031254582030741c669292462040e40145240d8000b8807a00781e043c40301ca000d40c800c20801c19800540b18402c00c4c4160141e40d203100c52900155070520307002d103031940e154222a0342030000c034008070101944203000400119041c0f44004002410840a070003602c0011203c2c40c1c1017098040c208041904003041b4a061000200780380c0700203106001d001c42c2c8c0d500300011aa0914414000c032034015558404080321b2a64 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 342252580 1250 342251330 342251363
    0x150c030218220b150703080403170609070e0307030606080a0219080304170a05010f0c0f17070507030e12010b011e050d021c0c0f02070b030c09150d02040f0317031b16 73
    0x3201048400b1000201984556241c4088162b0034602039407014002e902d064440c1c0b0030942d02c0000382c840180d09481795950001c003003012030040c1c0d8020701c60340c8080c00303440b00309006001c0c1104503d800465950b0980d5020000d0b404008200c2e42150a82c0d042141280c80750b1030031034101402c01102030b09940c00d0a03c2a043c090081e4440302d10030481c0d031500714450103021019189040c503d1a810700d0703801c4642c001001d8078003e40040510701c0c405c1c5014541071405000203190501400d041c61040d0f0342d00c540425055070406015019030745410840c1c0d03840c00f02450300400300d1207100c0c001001543c02240e0346051200040684210741150001400980301c4a5001040018001218001071140000c000352800e2514116401011046101c41c40e01805006000340c400c211404000003030000c00c00004122514405000a043c0036400e2043c864a542082204000c010b6003000041000f041400344010384049840c44484041c50f6982d00e1318443c4460360204000480e000c4c004070b0780d451100c40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 342253830 1250 342252580 342252587
    0x1e1505010608010509090717031318050603030c060109021c0c0806010e06070308040f02060c1c03060e0f04030e030304091a0910080d0507150c030218220b150703 71
    0x241641d500741c0c0e4401190303030b80300200012200243c1e00318060380c0110005001804c6400d1042c0e00c0014080d0480e4509240310201c03a11132409075100d880003181450581c0001911401500e40000007100114100000b08400300d49510f4180700d10350046a00161201c0c5099090940ca103036104450f804004111120802a2503203c00701c070410300041594403020107600e0141d0039104019016036401e091582c030355481303070b030515056035040c1d030b00170340900110b204244100581d01130701c040b145d00c0604141c0c000101030282c0303140b40c11084040c001c3c58100540c20102e000440d41c45074040c58185d0070640c241d804a410340c031880d0020f000740ea08001c000820f070358101038560307541c100c140c07400c1c1400c0e640e405070300316004030034019032020340c10540b0724084148c441c00141602c00d00039000904d0048400c140c4100303ca504451400200b5004100c0504682ca911100415030f601030718a60f10400f203408808a904102d2813803014929a0740c00c10020365160707c0c9460450401442d102580ca50f09400e01a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 342255080 1250 342253830 342253841
    0x1d040204120309050406140909030708070f0b0702010507050f090112020310140a0302010917010e1c080702010e060a0906090b040c081606020d0e010e131a03030c0304031e15 76
    0x56003c6120003000081a00706803107118100d445508080000d80e102c142000400c0d9000b805100ca5480103100640104140c0002171130000e02c40c40c500d00e0210154540544050750080c4100156454002041400e0760083c00301c5100290700710703103590f84120b242d005a41c1d8058640301140715130300c007004009030035105110001c15240741194003017502c480e8100300264503200d0702009000a280d410204411503040c4603003285a080c039400824440031000107a40750800c9017420900250290741c469036a240c0004006070415050301c028071015405901d42950366101400c02d800043c1e660103580107101c0f640d40001207080d80910100031604050506151103c0680503222060060000d4a030200030142e039060103c407030315000b80541d50b041103021340d040c010740740306c44d03041c4a20b01c107442c13000d5603c0c03203140c018034203440000190729044c0303c1409080c01c00000c60b10340203600070440400400000015101100c0d4800220054403491800e500300301da01500000300104c01050700010107007540e0300030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 342256330 1250 342255080 342255083
    0x303060f1c051b150901030b0a0e070c030f020d0c020f010306170604050c12190f0203060403020f100b0a0e09010e1209040507030501240905030313090b01050403121d04020412 77
    0x4540e00b68441c03020001a06101d4108580d200000c01901845d54080e8100d00200f200c028140e0100d0fa582d1981d001d01010f00b2640c6a00040030200038104150300100c82b00030000e903500c0107101d44800600003802c1c0140810b006441010488541015a071007600981c0c00b40103040c0940b50221040f4203601d80e154000d440440791800b07191950364440c00c01c040078003001c041c1c80000380680ba510b40090702e0401c03420798084d260758840f04c1c55000580c80401c0b005014078401d500a0078460342c200280307804c05008084a1074454100300288855130f40e46002c2d00300b9611408803c007a9130b1142b480441c01041d042c038034170b00e483c0185030746800a0340b0054050031035248259424031181d9079260041701158001d010700441d200319819082e4a801003002802d020b00740c28205440d207243c94000080c5540c00c064004400c01c01d5a24080c0810344403030280c4a51401c003030030001d0800d8110794071803100003408011a010003400c0002c558605100c800e034196681c0c8040c00465444d0344840640540c032011600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 342257580 1250 342256330 342256363
    0xb03042d0b090c12060c1c2d0507020a06020c01020c06040804150f14180a120203101b0c060b1c0b090619020906070b010b2a0303060f1c05 61
    0x4055141460b411900c0c4c84a5500054585682c0340c861648031a00454800204d03641840344566080e10b2901ca0028101801040c00b94102d4444801110b5083ca0b05c000c81d084a00386014000c442d5000103954010541c403a0000d030711003070030080d5140240200702680466120305402c6c441489515402802600c824032100ea504540d441c0d010384001c4801c04407100011405034000303810000340e00103000c0341e1080342d030344203103107081d000c0007030b94150300c82e0021103802c1403c0748a0002c52508101c11000d94a41c020203010202d95015113400e010710a01030301c4144942c01600808001a60380306004141000b014022089040f500c0342200c0f40100000315070a0000c14046955030b400061004e100351803600d80301050304a4007269030043d40100140e0b54002c54140908400184111010340c0a401c0400c00d880e110010031600c00c1020b05008484500c5650030303c40040724660101c1140d0f4004020b0300c401c07480403502e501290343d0044410344c2e5041c0480480e40b24040080200e0454800071803d80c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 342258830 1250 342257580 342257593
    0x50706020d05010302100f020706080711150105040e061621050901050703050601020c0a0501030e0309091603110406050306041e0f05040201020c01110714010e130b0301060902040b03042d0b09 84
    0x31081d81c140141c00c40328405270b808610201724191051604580c840316600c0d01070101908290061f1070f000030051114426044840180540e0800c1e120304106c0c2d0b080c00c002030101b4204a410790f042508000019000c0140140303000c0c3c0401f280752807418015541031000c000b00e107061804140244001e0f507401e8000303401c5c2800304401d03603c0015010b40900000b031080324614a800300540c003c0440080c0c1d81c13107500051090144940d15804000e00c145440380007001c0d54044000300504a41c80002001903200091005000c060b40c850300ba00c0e4004001d50740040d0900c401210340c0e20500038910b40c2d0050303600b8a5030041c4140c10702d400840c01103200303808580e4440840c034015640e182800158101c107502c803400400c040c50040000401c2000103040a020300b13000d0001203031f210340c0c0328114000810703291900c214150609101d100001d100e40c0b0001c6007014100040000503110140000e4620f44400c0456901e490008680c803da00b0026058020022800c0c642108280021900c0181500954 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 342260080 1250 342258830 342258859
    0x2030411090f0a2f0903070602070f0303050f12040807050606031c030f2315010309030504050d11060310080f0c060403030f0e0618030c010f05160201050706020d05010302 75
    0x11041079000308980122074074555242920b0710010310f04400d150a103070a20003c10000166224640c0ca143e40040c8266a41c9010400516180200390b82c002c50031540b0003c01044a000c1c84004030094a0385440d0490390b80c0751000b180384145c0118000a20040240010b120400074400700814060f0b200c1e80c15585650f803040201921240546e00f0f03011041d202d49103c0191510980c0106106c0558080c00105040c0ca5030101030450f03071100c29600e540722a44c05000150034078140c0d44103148400d19091002804664004055000d14840c090003450851103100c100008030324a00c00c070a8024000644170b182c500d40c8007050107498400d00b44070b401211a80504840d000c502d03503641e080d01408591034589155802c0300d10f400440b180108000c1c0c07020103040503503034401c020421b50021a5403040d840600104050420840e84c0410341840800300c60080510b03046019209002002c0390301010040705800169024454818001d01ca203100046d02000c0003460341c46a03050741c2c02640d80340c504c0d0207030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 342261330 1250 342260080 342260089
    0x2e0b090105030d0c0503040320030601080d0903030804030e031605011202070206090d0819020c010311130b0904020f120109061e030b0a0e010905060115020334050d020102030411 78
    0x3802202e030190400c560b86000540540342454081d849402241d00e0290b403034803082d40300c0d10807030001803002e941109194018a01008100c0c09010309070060800810540400b80800140303100013428081ca0200080174940100051100b0400140680d41010110750711a240d20105014840c042103803200c035004249220710076500603a0b4043c040d185400200010400c0c01020380c00300300c8009004104080c050181320b50302d20444211a0010420700d9060341c00503040d24040209458204001d0280e107681444a0898030100c55040d020a581c44407a134000c10068810854590001d62001174856484200551090304035940701008108540d00c0d01e200000001040034411010000000700f48085540701406c00c0d00044290000a08226044142420344080d43c0d0b0a03121500008010000c03424010fa020b40c0d070b00082d01c050340c074100102d242490380528071210b0188601c3c580796040510701c641160441030741c0d0050220346600c0c3c0c01840090203944200da0440d01c081036015030700b0181c1003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 342262580 1250 342261330 342261349
    0x705040b0d0b12030a08061f0509010f110a0803100b0405010c080a03090f121409282d060f090501030f06150c02011409030606060c2e0b 60
    0x3000d400a00c0d0018101504019288082105034482849001c26203001d1003000141004d0900340c40b6445186042001c110381d06022004c641c4803880c1d07403101a100e5542c4031044030f4100609003004441005402c900b140c80704407001005449100340c9030740c0000d00c0207640242d841801900038a04c3c42e16202d011110136400f4070300c2203e02003451012030b00000b6aa0307030003501c28120f2503d0001410007440c1c4032882e0540c0b000000743c0300d15105d02c00040480c0d0740f0981c1107039061102d0b05618500001180030983d4241c1207102030300e1101c40c03000945c0501d940001d406006000a484113218030003244e02c41e2007802842801ca8101c2c848030b080002d003035030060030401030401e010348801d0340c4145820010f6010304022a035121a40380e482c90007040416110619020100f4a130392022000c204910003d82092000d83c58601d9850080c00b0114260b40d00041d90342c1e20845c00d449507a105c014840d40186046c144020300c038801e0012180300c194140341201284004180c0b60310501c010f5114000784204586c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 342263830 1250 342262580 342262589
    0xa0510090305040e04050c10030204060e010c0c18021204030201050106081605040b03130f05030a02150408070f05030d020a030902090a05041203052701060515030f010e0604060510020f0105070504 86
    0xc800303000030010300240485940d802409902500c45950070003001585000348c118402011982c0441d05110556101c040c40d025040c0a007050582c0420f15140d54850b90814491a201c0403112212500556900d03010303207010358071101840b10035007828034008e4080c2809006500000322500009004071107501d0310102c0c101c01f0340d112a45060300341585402c1c1944028041c5594a00c1a840c820001e9000124401c4183c06440555115070704031100a0802d28002c0150082d0f118031420b000c0803820820031914510361080c07010710000311a1501904500540701101071407840841d44404582c0c058000c030660b14030883d03190351130b41d0303e495a89084603800d4501910200d00c0101e1803003080e010f9400983c000081003e0601e01d21907914003400280301200034021565100d201c00c10282c140506a5203d05102000c01419480d14448a100d2032005225040002c02e2020105070f042e1a2035100c0400313800701800c0303034114100402c4080d546001c140c005131650340ca800300150480f44201c00f03807010b0301d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 342265080 1250 342263830 342263837
    0x106030b040c290316200d09050a0501090b07020109050d0b0105030105061c200406060e09010807120b0406060b04080a031e1b05100c1211040506030f0a0605060a020a05100903 77
    0x544400714010088017014031820180140344004071815002c16910000c5281200c004102140200100a0012001c0e40c0305a01603508400c05001c0380c1c0e0804d040e8002d82c1c024016a58840b0032500048860410560180b50448440d0700e5030300c1488019036101c7d040e90020380c000e2015407144c105214110340d03c1880c0f09a006514072502d000201e200310000702c44201c0301c0840222184800002d41126072951064021402c9100803200318180350784d6441c014100c107809004c03114030707000380c11003140705861000307080c071502c48009002c0002560040f00680309203149240c44544568040da030352070080c0c0080e400305a28503004080021548030510710002e596803104c4d403e115440102c484114030000c221050700480d015400c07901c0d03062280b010181c549075104540c2d800020003103022142c9200c24034200039820001070003aa1110b0741200e401004047c8050080d55900184800403c90713500a20f50007040001c65540c0141e0008221400c28007a81c1a100202004284074049880051004011 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 342266187 1107 342265080 342265087
    0x905060a020d0b0901030305030c0d02040305011d0c1f0309030e0603070c0c0605030106052b0905070518130602070201202d06180106030b040c29 64
    0x10580c0f0545070840c081d415610002e166200080044502c088001020150074810fa4122001950004020080c001c00900805411011076a000d003041c803424400a415107040a95542101d0249482001c0203d5550303040d0080c2c04406801e4041c449200c64007882501d0f910001c0d841170710256603000ac00e182d0b51618100d410a250026410001c4c00d1005004250700101204c0e03a04000c0f07000780207083e10810744410058800e940600800e070421800c03204105000a050381520b0f81100c2107038540c8140c0d14400c2003040110f44030300c48000b1462240340415001d41c01810001c1c010b241c0300500c1c040c0002212000c4108460a403c1584a1f0403048501c010101038603068101c039281d5400c9842c01d11007000d9581c00301a02c40048000d0820305841120002d41c0300074020b41d0301c142c07000002c2c6401c0c14550b00e8015a071044020720040405d241d4021010040490320398005210035034107 = true := by decide +kernel

theorem cover : BRFrame.Cov 342086330 342266187 := by
  have h0 := BRFrame.cov_init 342086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 342086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 342086330 ≤ n) (h2 : n < 342266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
