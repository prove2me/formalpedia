-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0579
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:33:26.391076+00:00
-- url     : https://prove2.me/submissions/ec5935ed-c90e-4b8a-ab65-1cfcad493b85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 103956834 ≤ n < 104136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 103958084 1250 103956834 103956863
    0x609060d031b03110601060c0b0f0703060e09030d0c0f05040501080a0603020d0c0602010b030109030516020a0906141306031e0f02150703020c03010504050d12060e0a0603120801030807 81
    0x1040e03a000c4000c5030820440e1840903054580100780480f180c4c02504a80a28000443c03194840c0c828120f0319034115400e603209483e03880d140280c04c18082e040106041d603500c000201c8680e20031400344070301d202d100a5502c0d0303032a0510104c155030020180d481084041884004070315000700a44d0203079102072800aa156031400b031035500800342608040c0d0701440601d1500c040010a1a01c60242c94243d4000e1000440034001c0c10300f0f8400e950002804100c0c14014060601500740c4002c00c0b42d800104412440741d600c0b15a08126038950304501c40c03642100b203181c10103062100700754074417806041e001c03c002441c0d41c0780e440b8692444203000c100c800c2c182240300e040c4082c054400c1c1f00b981c0c00401d44408075496049150269004080450242c0604a10070321185418450584140c0e01b14010380341100440200715240150101800b04266403078078085000207800802a210300300b4080c00144250641c1054140050441d150808010b4460014400940c8410598845641c8000218820740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 103959334 1250 103958084 103958087
    0xa030207111e13020a05040302060c0c19080c01090f0905100b0406080403030f1401030b0603010f0905010e0601121106031902030403170604060806041415011512050609060d03 77
    0x451188002e6001030300560107103100c41121101e10066000319502c0101c81c070032040c070760241d02800e50032a0201d001440b0420250605074020703d1885926410b85403280c007032100007008078034aaa08419070080380441031020034400c000e02a444003003402c180540c145029042045003010780101b801e2035442d0030100c0c5821140d44020006414100c0c105621982c07190b0f401006040b0032039003034000904042411480c3c8005100c1c40565201840840c501d5070f0a644070b44070360a1018004d1501590303a01e80c00d03120002907200304203803144030300004036010501c100d5491070440e060300203d1050a400e40a00001165210700c00e64146094a00e613440350354903041882c3d01700c40c1c0c000100800b40000100010140d0080f94010383c0b0f001140004034a03181c00d01480112020b0b030040d00d950758003100120b4007080740d442201045040540c00c441c3e00d107160320815800c001c000ea20095461001ca00c0842900b80c010840d0008100054402c020a140c22000540408400317000b05000e007a50179045028103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 103960584 1250 103959334 103959353
    0x12d060305030304030c05010605010813110102030d15050a0509090a06150e07020f010c031802090606040305031611101d030f03041205120306010206010e0a0f1b08060a03080a030207 80
    0x25074111003520703200e252600300900003001e0101e0803103455213410750200761036010341c0d4064015074002022a4501d1004e036642d0585d174101d54903090552000b480383c8000703042c950142a800000405218038030310302d440140950b07004a0f40100f84070b4400c07901000038982d80022040c1080303402c040c0c08244800e100045c1031440e960b5810280c85800c032103041040717894000036009100b04010000f00403001d00a03070201d04440d0084558040c00342d41810311005468031030589600030000418840c41c06070780303036034030362a5520080e11801c032048200028414480e001418940f00c80d0b0a81c4c60309480c840304c0b08014044500e00c1c1c80340e9002d40414900000644040000f00072100c1d034801200d65840d1526100342000342c00c14403c076850b1050408a60701010411305903802046e040c2c00801c5140d0030019101e50f001c0d00104440c8025135145440501c40320b65014a10f0501840300c04d4142c51441207400400c0500005e001501031a0107001c1040050b4a2104481d00652075240045e101c500c0d5141072a4803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 103961834 1250 103960584 103960589
    0x307090902011403101503020a0807020c0a1502070b0d1e0630061a0a0609140405130c0f0e010503031c0203060d020306040515100b0d1d01020319050108012d06 70
    0x383c0c03040410b2544031031f01a8000c1040040c02e403038000096998103c100d03515001c0c0c3c40b4a07608240c10240411144240907040607041d00c40d40141ca042c55298000c0e0045a00315204640d00070351259521007442001004a1070700c0d4951039001c5c840c0600300740e4080c40c455900a010400b4404c1b10342d00c071702400e1440c4160034103c2c0d40010280441d02408a21145180400d041c40e845108040340026151b401203120500306c40200d030012001003103c008010090030000c0c07400307006c1220a0400f200180101d03c0c45400350144251840d503043c00d0800f03043c90844140c03c0f680c0030783d00c10083c080c4a0360b40001704440d0302c103040e440540d503542c1c1c107030200c2d6001c100707964000e40610841003840104000424800101e00080410048980d202e80000c0c50395a4940f041c0c0506000c00c000c603595107111a0810382c0d03000384642a5002110103602c407282243d0080300d040f4941003201160108104035401014014001c031002070005503401d0219601a402c3d0346600f4120700400d050903c07000301c80350480c1c0700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 103963084 1250 103961834 103961849
    0x3110d0e0609131805011b09030b040c030c06050a080a0e0604020d0809040903020105060f03030301060c0312020f0f0a032d0506030a050a1208010f030308060d03110106060905030709090201140310 86
    0x1c1e04e0400b1850040608914045516508021495414848003c7c282d10800b046548140b242031031500c580d02d50400141c800d0310240e1101c0c0c00440400d1002038240b00405043d0340f010741d0b03804140e90040002c10045c24081d1118241300580d000e5510000780c1c1d540142d011160f91143c001d051604007914892414001e8000f82881003000034075030107502c600d201c1c0600703440011310200c9440c205500ea2009004004c040741c440007502c808248651401081455010b20051514031000c0455140d81c000d542d44000540740040c004031040d42c07600410782c12444000a001d0a02c04401c0f1040290311305814002805035948009100369400300014007055401900b62840320b19541000350040044095100200703004000004040c2c0700c3c050300b103007203a8043c2e86000094542000b0401186480403040d170809c0454420003205c44400e1088100800142e00d40e170704c66524203030905040000ca84d01c5030800501d840175803409030341c101700401c2070400340341c1d1030396070b04c1e03840c3e80c0950741c8000709030003044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 103964334 1250 103963084 103963091
    0x3091203020c010501050405040807200d12020f0601030507060c0f0f030215090d02030f21090c030f03030609041407030803010e1e0403120203100512030703110d0e060913 75
    0x1a160907600408108040310024042681c070703841403000387c50341940c008241c00c400308800c42c01b203030910702c0a21100304000c1c01e054180d0030490005904490a034001d88549045414000e10b04c1e804006190713803500302501800840d032443c3c07600ca0b12003d1520940c0240070800001c1420011940d10343c40701641e024801320114201e908000356500300d40c8400f030000c2448040480c2c100c040001303034041c4d0242c031540110702e0b00b5001d00c01107186400c807061601000e41c0b0b5040e40f0f0701f60910200c50038800d01c1a04000e1a442da006020540740c04210020914540c00820921180c0c0e210040c249501c560000800140b130180d010143c1d203810700c030b42e01c0541024008000800d180c0010000c10b8094400c1d0f40902240300b9050000340c441503001c0e00d0040c0401e624140090310601c0741d4010b540e10450b120f444214030703541d960105100e10041000707859150000604a010190040b4115014210f0b000043c241390458000c003030a51510f18903038511410021a810040361b490240813000340c40020700030b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 103965584 1250 103964334 103964363
    0xe01020309060d051b040b03190b030105160f0f0c0f0c0f0b070c05010807020c0904020a0503071e0e010806010e04170403050a0b0108030319020c0102070506090604120207150f0309 79
    0x10051006171340344544140354040344c090304040081070314251015070411030300d540c807080307050401c02c1c240c0c020f1022040d45860104140e56800c1c070800b4400c0c41c1c41034600500084001d401851510700920704c009014910800d41d08040d4015404220301d40e12204104805c8258240741d90921815440342c218032200640102d440c100240242040398070800d0108034140d194030040d40d01034011114140180c1c019094004589416102c560b001030005d0b101052060715540480c0c00c00040d40c00195440111404030009407008501507001051082c1c8640c5095052080d610345801c410b00c622552803040030081014090805008040305160110540ea920b41d03030b2a1450301c5200742a800e80300200000300000f506030020040740e20598080a01c26864121000c0c0c44000350007540000d491507600744a40c200007441040080d00a041c820020482490507140007010881880140011500220810810341c1c1303c2d581d186440048905200c03810141d181d008400500945101600000020060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 103966834 1250 103965584 103965607
    0x302070303090503060f06040207020f041a0a1d0601080703020d09030918060e0711280b090f0c060d0b0d0602180105090f0402090a09060e010e07030e0606010e0102030906 75
    0x8800c592080d180e14000e03564420070035445800889800440b2003e030000074480c5d25059004000041c0b0080480c2c60b0243c10f04041001c4884002c05900500b203010380e29074162070241c21201c02400040d20300e03040c0f50101403a05500a9000e811907060000c014003054000d40a070301518011010301c1c17020010107a55090090188490740319010700300c2c1c80c003621024103030094000da01c2503c1c19172900c0603440e22520012110140781c444c02e000d00b030044001c421552100051800303004041c90b10700040310807590910808850024004146690000b16102e404800c04149c04216810880313405854040031540d80c00508015400315522003190320b03514042100540c050000da0b11041d03490039184c81c4030401510a84514a09103070301210310080400365150039001010060005800301041c01c0c1d846080e1002e51b881d036041014074000070001440054015560182d00c06018582030007a5464841c51503212040500394a0402981c1089480944d000300b04940c16002c025040ba903507000034070308 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 103968084 1250 103966834 103966843
    0x30909020d0c0e01050c0618070306060b0304050c010207080c041112130302010e011a04020d020f040308071109071b02010306081005180c09070815100c0203060606030c0d050903160302 81
    0x1482c0b4007203080080c000c2e405510034020344035444144401040503844000c0540210b0284803403186280c842c500000c400038413075024000040201420240e200e0902e403030218204046801c4003411540215001c100483c000500004280404c0d00e00250308861103050968502c514284034001000300020300205905040d040c03602e0f24080d2f8000c00ca80032000c0400e07401d803145422001c52001092091f074140c1e1505034001e1411515110f0010718026821240c90b11503089640103641d40d000c007040d014244a8140968822008200d803264040e01e0700300ba000c0c0550039000300c108288043c141501045902940c4280d014141400882d2080a00c807403940000d80001c5070740340f010010f4008410a416070010f01d00700c031031100801d802d900313542d100c6040710300c5000200f102c8a00300016003980301607220700401c1049108140d964010701c138854014545007501c00391400740a580304008100c03620f080c00d41654403040d0620004200780d141c8003446440d500880c10000d406410898030714081540025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 103969334 1250 103968084 103968101
    0x130e0c010e0306010605070201030209060c071e0f050904140a080d02130b09060702091e0a020318071404020a090b0f0306030717030307030c1106070503010f05030c031009030909020d 80
    0xd85182040400100703060f00c0d10030a120300c1380480c0080c081440150f0080d0058000d40030054051400c11b0514080c85140420a0b44440030707c07030b645c207814152214a055018042c02d030060340c031200c0c1c61410b4003040d4040300050020300043c1140c0d00480300604140022100c06c0c2d0407007901c507111242410300c00000c2d44144070418136000315080c0020751310032031410b89240b008020001414501c280d024014200d070000d1945010070f0442c04519031850065001501403051070701c0040e00ca00d014000ca40c40c00101c1200d02000e90700402c0d040200e0000c4081d0320a02c4501600c016071a0300c10310074103989150f8290030060360480c02181803010320031410040d600c03c4400301e0449800e241d40744888030310380aa9190707240d4282c208000180510b4042e4024074644260341c90701d0104c12880100703031402d10405680740000610700000400208a8861140c8054801100503040107180d1800082c1d40d5a50040c2c102030f40c1da1120003401c00d050161055200500003510155541c4210302c05103001000503c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 103970584 1250 103969334 103969337
    0xd1104050301061e1403030408030d0b0405071e26090313120b04021e030115090c050a020312060609031204030318180504051009050c0a0b0a1d130e0c01 67
    0x283c000f46074003c044c28203400c0030800303d281c40c52a040110b10350120007540d810f42c2e01484104800111040204000d0800501d02c0c080010111109001c21041e83c6003d03081d034040010412541004900d032801200100999081442196102000702e43d560001c0c8c01004d01c10207005010441c200001100801441c0303641d264960405456590218107040b21076006850303000c01100050040c02c00303146c2d09920b0401003003501c504025200019003542c0e2213100800c180b840e4030130300300070765403660068000211003414001d09000707465400a54a011345280040f00761000c20100b04180c465404851104002a068600d40c043c0402c4902980d0310520045000402c1c03001c290403140b491109140075180801c1d0b8110403c007000c0703108400f42c81c003e441520b0130f010b0201c590184109901c1403901062184014100910140301006a10350955001c055107100401105800e41d42c090029400c0c3c0031110030b444800034008001c1408542d4040840102920307160382581084400034945c140170009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 103971834 1250 103970584 103970591
    0x1401060f15050301121401060302040603061407050a0c02010c02240a020d081005190b030901060302011d100c0f231608060c1e160b16020705090703020d1104050301 72
    0x2070102154544024800c44090b00c01c0d115101000400c420f264464081c661400850919101d400080c1112400e50088502da076440c61400241402d480d001c80d441129401c1107410113009141c045c2c0541c000d004024100031480f81c144c01103646a0180101009490781d00319603030741c1c00d4440080258400d0312020058491900781d020900e100d20007507840f84030740c8140031742080e14003001c4c4602d0320b80040c0d1862a038030081501140341940040958492111000081103003403443c0000750200a022107801940c51484140c0c4070680c0361030f1b0081c0070201f01e52508030804100303400c22a40d03001d002c5000800c905207522054024809000011070500b08140c00d032a294180701d0301007070080d885441084107982044000554800d1f820026006030484508105041c01109074044190350110804e0100c0c820a032042c4000e1040050103e40d001e42000210800e1401059011b5602d0301301c1c3c860180308035a000f000039941c80c440e4040c3c440252030403a0a001d0b07075141c140040d6613a0842e0152a00a40c42c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 103973084 1250 103971834 103971869
    0xe01090522020102030a050d0e010c1805010201050c0301030f0302031c0902091509070f050906131e0e190905030a02010515010309150b06070b0903070c0509010e070c1401060f 77
    0x12124181e81210350305030011484c102c84600705461582001c918980c0b516514040c40c1c98601081c0202c0c1141d0700503523240c103400d01d100750720a604480f41c1d0300401c2c1160700d484204040348081c40100e9040d00d800c041c011050b440c06280480c90361150032030040f6201070845003808004203503040f445205100300e0f0480103603540d42541441406140000c01c0d4007441c054082662907000e101104204240303841c000703182900e18004640310b54040c020000b50007642450070801c8615054a00a0401090307054898003890040f10261148020f00b00c54040c0f41c00890280b214101503001561080d0301106581d19134003c468064024802202c0e80301d540b212641143c40c0a62003031080300175241d4044081d00c010345c80286003a004090682d54140c10400405c058004030b08100c170110310440e8103400455030f402140c0b03405a16080194010b50060b0000e600500402d10380100d0b1a6028040307281212316210b003800e0100002500001400da65403a0840106041f001e0642e1542542d10408000c40c1104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 103974334 1250 103973084 103973131
    0x714010c08041e03020f0706050408120304050703080d060e01030614061207030303180203030310090e0c060f0304020a090204080a03020c10080c03041a01060f2d110102040e010905 79
    0x78040358010f04000c1d1203004a07100410020305110558007920440300ca41e0740d11590350f850000150400d401044001c1030070889e0031400c010100da0350945c0d102003419400c0c40c0d91410365942e0540001084000c2c0854070184090a5901050003040040c90045855a40b4102100209000921034500400480c0044d4641c10700000007558800e2842c0140001891500c048004040c3e40350500001000c0080303d8000d030742c003080690f02840100c84000b85041c82e2030300c02d0017229203203e007284164000b102101c44958840040c3c0340b1130035100c01034903502da955100082c120803c9400c1040060310119020810300740016080e14004c0c072940803074410013608800c000503640342c12841c0000035100c10006c0c004502d14030280d60094400e20112911094501e0500e46400c401d821100004e074042c1d170a0343c0e00d103611800607900e04503191051406540444110743c81e03502000200340c00d100f80c414210421100950440f0000c2c100420500101d503101c4807544040e09060340d0f5500c120700c220039000c0206 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 103975584 1250 103974334 103974347
    0xf060f030921050405090f090d020a050d080a09020307180c03020c1209130c0206191e050702191208011e0509060a050d1203051012110303040b0714010c 67
    0x10390441420002e44501010070b1054000ca20105010080103000c0043d141c0c80d082000783c0240c039501e0a0052514100d56460714003601c400041c0c0c21940681042c401043c1c011038070320302c40c10f050701d040d00c00c0b540d4659001c005005c1b80040250503100d0a000090442e00314a002280c4e0f5158402c00c1c1f040801102e000c4040e40200c810310301c41604000d0840c01c84085107401070205000191040a192040c0c906020440b000e17000001d02507008582001141604d0003540f6800c2100301108101c2900c036150341a0312a40394a10a80c401340c2d0300c40105e00714074001c200503145410f15408071040e034075032480c03c419010f4000d000c0001160111002080f0021001e8140c1941c0c031a43c219907a000c0c1c641000c0080f0084040c0c480c0d1b400c55500b00000c620360320703000d0500301024024801e41d24080c0410030010111803000301880003d11521000780844595a05008100c42c7c00102122040b10b520000a0962040790322814003032000094280410080461210000000000070000c501150505840c2c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 103976834 1250 103975584 103975601
    0x12030b0102030c03091c0c0810050a021c050c0f040b040503060112020d0f030302070204050901090b060a060f0c08040905010806010609080a080301060c0f140307060e010c090e0705090303040f060f03 87
    0x850300b0034400707040c03d414400d03c1e5400858486d12280c24407443c40e1209800701e13040b50000d0806401076a815170002c9490b0103204c0e000200020118034003c400c0c0a05481d20144001052400b6180c20204096022010913103074082c1e0070441031030340d07590b48410300c140c00d510621883c0e0080c00303100000501d0f008465940f15105801401000c0341d030b8040d66031000c000c8032500080302803540c2402094056115445402d105901e08000000ca6200344d04007040d45200080c82d440c42018030303030380078042c842e40101d0080f0f4046140c200805900018500700039540542d8005c06a598500800003640e48000205641221a1030312280250b44d1079a847e951102c41c003e00141540c1000c10042010600c01c0080701d0f00302d070142d0f428030710391102070751400c4404465554401181c1d2021900c2c40511081e07204681070f400c0c00b00000c101d0b40c0100703a0701404103a124400c2d8404132104000203030486002d1021a0340c0554010183ca45e0340b40c032640c594029007418010800060811200c1c01481e60191041068 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 103978084 1250 103976834 103976857
    0xe0a1a090c030714041805060102010f05040c060c02060c0303040c05011101091a2703040611030702030712020102100e210a1409010c020312040806070206130618020d12030b010203 79
    0x386035254102503d0081504041c0614244200300028480501d51601c9410381c2c6d05241c040341c00e0070071100081c00d40700c0d0780310507405c018907000034400025a941c84e072004640182c01c1015043c0c489000290203030042c0040792009010001c00c10082281e100e01000c2566402d807a403051600517121980c0c200c54404d03100601001c10f4104401440209105044c3d100700580310646002803c59182d5203141202401c5920b50b500200d000d110003908100d40401e415064030046003441126000079a855509201c0d207a114051a010a029640300780281000001d10b50024015198840c84807a503444d090148101800c8120044c0001c1412202c100e0b8000030b050340e43c4a14900c10304113680f4496200000007414000d01119000060320700744104507417514208070b1582c859207001089400c200d0020312420840d004041000034844a141c8800041900142c00144140b101c0021110142070884080e41c03182c0d907261a5020003034090010085002c5c5170f40c09000140c400b50040e81da03406000e10404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 103979334 1250 103978084 103978087
    0xe0607020712150e01060603061703040504020706110708090f120c011124150108040f0f02060409110d06090507020c01030908120408040906050d0804031b0e0a1a090c 73
    0x25542942c140e24507903500490400103400f40340c8020900300c560882182200340d4640304100552601841003100404042d00d9002e4840c0310311052544900c994041d403485142d01140402c14044558440441c0400f0301030180e5881d2002e023070250054002180d400c2c4274943c0346010801030309041d40c40c81102d4450000800803d0380311001035a03180e0b12030000c00e519110790b0005280300c0c20b408500100d011454007074203d507403c04801d2408032403000000302c2d040c8503000c0180400110fa100c00b5142a581200100480f080c480c80040d00ca442260711010186003841012608100d00b8402084402c41c0101c041010780e0b6148030400a485003164140096040400c250415501a8120b1118244281a010b2412001d000c50348031010f0161000c0e15a41c40104007840000c41a20510001d04001c43e41c16200301c0c0070342d4803848544101d01000b4400c0d00b00341c405440c00311003003079000b020301301398101141a8503290102c4401000b4407411020009410108100a4102012a0790189000c2928036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 103980584 1250 103979334 103979339
    0x1415061306030513021c031101060f061d04060b030105010e040b150a03020403140604020a0f0e0403050f0702030607030509010f0501080c040c090b04030b01090c020625020a0807080d0e06070207 85
    0x950042000902c440c441403542584e07800140d07900000c054003039100c110030004101482c140140b500d0500d01e80013849078507080081c4018101011200d0813248680b4081d20381e00341c0e0744502401085c000d115190042c0c2030800204151820700d010303505a40003a0b8070388000030f0f8035800300400e40721205090740e0040d5011006409104075803000380f1660015080241c40e050707496071200c181d12903254000e1090780159040c0400c603d0511030000080c44210038103d00039080c00902c0c03800c00d0024000402307008002a01c44074a20021064036180c5400600307032012850880340103400b8000455024226510b01400304c0000c0c9114400c01d07050b0b0f0502c00082003100c03625011700c001810011101c0e0180311031038100140e9400f1f4a001000a144a1990300c2c03202c0d40342100c1c40c0e054469540c2d0500030764200c201000310200d60f000e00074950360340d0075503000244100320505900f0443c4100010300817040009400050060840c020322101c4c0940303600300840342040e6901a1160815070700840142c10280d001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 103981834 1250 103980584 103980587
    0x603031207142802300703090b0309070602010b030d051c09020307090b011e1b0c0b040b1207051201181b0c030315050a180e011415061306 61
    0x40009050101c280d038540f01c3c100d0303a1001d00241c0b8a031403c05440740407403c0d511440d814411180281e0881c905010340da2102c4000c208540e00c040c0b50420308003000303d1000305240c031846200c80100340c8050704a941c0c1c14100f00b2203440d40c02c0c078043c240141d0700b003203400010f6060010300c5031506a49980c0c0c2c1d90070000310107403583c42d1000c08a04180c041c1d40f60040303940943d800384000310040c0000400011b00001941c00902026412040d0000c4181c2c00045800d10782e4110300c205040030844460341c402c4071600c0c0b03810b400d2004e10390840140c0d0403001c08c02041da4007104004154042042c00d9030030340c40c5d5840204a506210b44c00d00b00d5644240c2c81e00421486070001014020b07941c40fa42d012400c0743d41c0038080303100400440da8100018426028030014940c040c810350030650600340400243d681440c01044100c5010710580500241d00f00010341880c40c03503408000c902d0700f620002d0040f65080f8a00002c144401d40d201c40c122050188140d000d2314009084030305c1e465003400c184070b80ca4a0482c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 103983084 1250 103981834 103981847
    0x8030301080d12090602030708040c0b0a050304020609130c0909060e150d0609051605090702010e0c0607050f0712120207030302120c0c041d011a090406090c09021309050603031207 79
    0xf400b80b50541ca4000030f200040c0c6070f001640c840c0c1c141c0d6450703c0861030181401c1040c048158025120820108204080c103130344602102d5010b034042d00c206585403091404501e1a04040c580307200e00a14001d44110740c5503002070010219444000d0920100d03844400e426041d140940707418040185c0d084c1024400d042803007131449214001c040003d08144c190310b5031414510383e003c030a14180b038106424021031900b8400c00d80c001a0b18070080028505a0b0660796680303051701e4076103100c1d11000c14108100882004006084210441a10b030041e550b001c21043d04010094200c2c0c201c0c0d000f10340181d00c141b00140302c900316034065005101c4042c1c00d1200d5585c50340310700754929050040c2c1c0400f0817141c0f100d0007208012640500c0307079680081004841d0b42107a940c0f501a40d4a84483c6c030b05003072a90340e071450301500f05404ca079001684845030718051444d100190b0181c440c06001064840380c41c030b4151122070455000003818001d9070345101c201901c910824403041d041402d10400300d0b0f4118410103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 103984334 1250 103983084 103983107
    0xf0213050111120d02040f061e1b020d12080601020a08340309080706090b1e07140604020915090a0b010e0a03050a0606060801030c1202060d020d0b0a08030301080d 72
    0x80a40e60f10280182c08091030768081500240030903000181080f0b8000009040001004185006801d0780d200d805034021840d041070000081000c0b01500e015415074003000d4030071007a401003418505c000c80b8580100c83d08110202440030600a00026149500104003240718030703070108840349417081001421030320703d03a800a952105141107140c01c150709031070248100600d0080e1a8034021070325284005152030110380010041000360441005552407030400e6516001a903812445400e201070780c01e00042c090001d001c1e045c0102e0f21854030070a840818810b0059000351000d1520b5510300003200d29154a902010750031066000010704400d40701c1c1d0000d4915001450449501500880000c03d109950340040d6120f41180240c00100645845030788000c10041c14106595071640d11211001001440b980c200d1301d42003000c03203045641b9141102c0440c12211000c640b5920010031210060825521003130080d004488080381c0c04130000b05aa04940009000b045410801103080301c0c0c0d00d0014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 103985584 1250 103984334 103984367
    0x9040c031508070b030711150405030316021225050604030c05070501020705090a0b01030902130c2a080d0b090a0c0e0d0507170f0307050c010f050a23090d06020a030f02130501 77
    0x6030602019402301e451003901603400b440c015512420049041d0300c01c0802100448290b5010010100010248a0a850304c54505900028110002060b0700c00c1d01320008000802c14010f560800c020903800803102102c0c1801907040b2040a9281c10040e640c504080c001c565010340b400c800501c0d1020650000c0d0911401032401058ad101c29602094518002c10f029403021500c1302c0301e2501c0c03240e0080c00b0451016491240d40e07119440314200744007404100d4006002103c0014110074403080581000700c00d003030081c00c00c200c6031404644000040c20380b02203e0001501e642c000782345500d0001c4080c0c41564200e00a40505032602005800d480e071040300c03c4001d405044c10500b4102000c0c0050908030f40200d0203024603061800004140500c40c1610a06000e024049808866070020450740d9803a1051460411b8510001c4642030764000c0111640d0311404034102c0c1010451242c010b0540e01709181c030207000104500e8001400c1e17005100e5014a00b8042c00f200708503d40c8250400e100c81800c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 103986834 1250 103985584 103985593
    0xc0b030c070b0106020c1003090803040b2203030c26240301020f03041e030210020318010207030908100605030c130209060c0c0f010518040c0509040c031508070b030711 74
    0x1079680740c0006003400d0713001d107000d0b8100654036003030342c14001b00604c03207943c86180400a010481d50389c440c02d40030240c4003420420401c030015005004019005000200d0b0710f01810740c8030715038500100034241101c0082c002070000203001d200000d1020b034010f10990307120782c0e5002c1551030000300f050f0a11440d200b03a1880b00708510921494030f003803009052805158207007550340c1c6080c2c00c0411068800c0506004c5841112103031202103035000c0b480d82c1c0380760307030701c0801680e207494022000c4003400384005041c0855200185807010950019480d6040700d40d004103481168080707455000440d81c40d8414250541c2005841101c98074101d0402800715481d005c0040c1001c000303130041401504070a144100945c0843c490241a00d48500c0c180300d03000092814500d8101c0e03a403e42c01e6141301d501d40c0726004607251070900643d240a10182c0700c40540c0680b00304840c6c40b40c0c620060107800101c03400d044020a08a001c1269040424460281c1d80f000d2461840c41c2c0306e8030030440d80f20304400e012010354081e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 103988084 1250 103986834 103986847
    0xf02010e06070b0105090105060a050f090102010b100503090d0801061706030703060e0703060b041a12070b130906050a03020108041509060c030b01020c01020f0c120a050105280501030c0b030c 84
    0x1211406860b9250144084006a40c10001070196144045e00001d11556003444000c40090b407100440d04840545006c00b62164544c40c01030303014001400702141e00c0320101400e03038000d95101c006144030741010822218200760805058600b500c0c02c1c000d00000418030f40c800140c980b000350745550810400b80072a4031050303490310703104212800219001c0c1580c01c41c0e0420000c0c000c4078001d02d07500c0d04003140c0130008066000500905407500b00c11203400381c8401c0110a2072200d05001c9003000b00481c070100e0382c0e501ca00780c680d03462500c01c5004e9a10014600701c0081014102461080f064079030603141e46800343c8441c1c0303d28441030041c140c10f01946480d0300c03008001400034090b003802c207006514040307114104000061b00f805590300f4000d046511540780c45001d09400034590546150607035106c51050720f610819030900b401400007070155800e281c2403204650792440111810054811703040c054812001040c4c003a0380c801e12028044c8000b915003803040000c003900440c0c0011404001514025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 103989334 1250 103988084 103988089
    0x151d1905031902010c0906020309060d09020111010509060709060804050604080306031c05040306050601030513030f03090b090d09051f03050c072001090b0c07090b010203270126040f02010e 83
    0x42e07030081c2400c0107035113a1640111103504501a2005015940061414030400401151003400f540092040c225240c48000c410759000722500380c1446200f00091205291610040750780341c82c15181d0000040d40104000f8140c0d1003100c00e02e00465002016109030f89030f80d01d40300c0c00d50b00041c000c994140113110b440440480101c0501081d11410740301d8548a0b455800c042c001c80e40000c001905060030030b07080001903030759180c56444803541400c26000145a5450490041c00e41400050074006c0c9442488010280040ca00c181c801e5039135101c02c441900d81061110381e000d040d04400d205207103e060006c400740250410740d801490ae0104074204048c80e10382c200d042c0422021010042249240d002095910852860141505400d564944006075043c5e6580302203900c41c3c032000c0c561301c9204a0641c0e00c03d02c200e941081c20144510781e000002d5100982c0c1c80d40010416000c9103409901d101003262194100204141a40c0b03908210b54172900d0b9035441c907130302040c100d040264040b1200b0076079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 103990584 1250 103989334 103989367
    0x30402040608150a050606030411011107120602030105030f010902010c030f1b0305090301060503030901121d0303010f080f0d0f1b060e0f0f0303060609060d0209030703151d190503 79
    0x101c0c403d042010b0700d003042e150707040403100c001d801d00e401604100208000f10720420910248501e00b0300e0101400442d96035594148406a040034205050544521040c40100d80145058407011000c0d03520010603019510308850407800000d010801210714072011a0240d8254282c0440c04d051102d01070440184248002120b00000c030041640400c040c4000e0809200d100c000d440164015441c2002d101c00183c1303a010403500180c52181c5450801007415840f540517801000c550342140d403256100c8481d020550301c00d0160151034030980d846640f1a5000080301c00300c0c0f40450722034030b2401c0070208088070903000405000120003004489013000418a11400b00501c3c141405845014144518035007441c0300140c5142003035209105001c0555240811510070050896501d40c1e81c0b01010b0100000e40900320460354035005940d030000c1071004c3d04281d40c0c94100300590030000c030142d01d00f14203604280d10301010700303e03440040305550101600030244074050140c0c0403282802c42842d40e19001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 103991834 1250 103990584 103990603
    0x60403030203090f060603100218100206040314030f0601080402030102090a150207050d0506010603090212060106020a0201140a0e011b0f0f030f05041503020d0609091407050d020d0602030402040608 87
    0x41d500104000303002d041803001c00c0080104501130542030030b200001a0b80c4146440c1d00c11140ca500240240c02251a52010305094101918541c41c090843d0300c060f4030b4001c103c8054002c69010955480004580000c17a480307449040480d4881d51180001101c0a100040040346c144d0b40c00c0002c0a113a035140c070402c00003403011035420114001c22040003814101942e1046009091151100300000c0011621078190341c4549400036846101c1d000080c3c02d0482c48038401c03940c1c050b07000049203095010078101c904a0003030705c038180c4075240291a0452071082803461400600031480d1a4995072084102d140c0d18154131480c4113141016444400307002150241c202c0301d401d0091419020150042246e994401050404508051514050324070480c15501050105a40000d603280400d24980c4800701409125000300840b42d90f515040e0b1081c0d4001503804851b216200e00012186440100c500009502510071142403409a40d4100030303400103003080340d00c0358a8803800b04000c1c4c0104084440b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 103993084 1250 103991834 103991837
    0xc0b0406060302010e010302120a0b0604030803010924030206161103030d06091505090c03070507080301060f09090501120b0621100e060c0703050d0b040c21020406140307020f060403 80
    0x884502d14800900408003038910380f03042c180180890100601040e440943c40b8007000c101042110720000003030382d140309641000300851400300020440f69216405072114845c046044886c0d81c610f00a0303498100411312009501600c100f01003440d8101b0303000604696481050381d000344181d0400080e0031a045000c500924540e81c0c0001c2156984600600454900c0c4641115015040ca0045548501c004041030003101c0000082104240f1035000c81d5980c0e0740113180507840b96111240106215025034650001480040000c207082003580b00d841c1c100d8071101000c116560151380c5482400f4401444c081d400703075481c111400e001e070b90702140000e800710800c003034060810b4000088041781c0d18020b0a6185600c110200413030000003004880c2003d405041c000e49a48a0007140006050781c40380c56500f160800311070045c0160001100e40550380c40390021854018010044012030240d80b0464000502c0080b0341ca0072820048015a0010028410b913104401e0300309000b45001001c0d1000c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 103994334 1250 103993084 103993091
    0x1509090203060f040c150c020406090905150c030106031a03060c0a08010e040b0f0402040b18090106060e03030706090f050601030b061e030607050c150f07030e0303190c0c0b0406 78
    0x41107103414070405521401090740808541001e4440003a01d50440c0200b210002c55482d02031407207801911a4901664024418050f06031141030801c0604090300007240d0621584034070020702d4403410038a40c840c2848284040c110380c40c1402c114080d100890702c1407002000e008007100c403a10705000b11489082c82102e65559034081680080816905030301c40c586442c2c070342c010f1000144c150b08500d90012420078120010f910750340001401060101e0000e03900c00e0700b0281002d0901c4000381c0b80c030301c110b0f0301c80020400140c0c0e61b0015105115001000f81d4507410402c0544001345682d440f60324800d00440c004180000d407545e6003031a202080e0070a851107000e21041289030f11304031001c0310b00c40302e03c448840101d2540318080ba40e2148054844028000e000c5500b81010104004002400c400c15107503c0860900c251240c00c1e081007a20503800180c1801c25100d001d00001048074000d101c440d2101c1c1c07000e408140c0702001006c0300d1403004200400740307604c04040350f0382c01d2080d8003c0c2d000b2107000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 103995584 1250 103994334 103994351
    0xf11100c18030807020d0204060803070302010501081b030703080c010905030f1e090609090a0b0310091101080c030406230106020c0f01030510030b06060d020a050a0e010c0c1401031509 81
    0x74110750020208a0079046100d2000e00000e5451402e9888859041d145081762128034400a0302074107843d0400c00c4540300c04107071082032641c15000310f8121081c00060f00c1c1100c40322400307010384100308490250594441442000042d04141c01001c504205200005015485590301c034150f0f03121a4040521003004520b024502105031881f00130074080b520351600d031082000105015000f414070940c8038070010380000d07048004940220026140003800e541c0400d001882d0744005080d4000c041e41d601340342d61a9810103500036510580140c00f4917a100c0e046513207070f50311003000d00a0003440c03500300c8591901001d040b01034040320034080c1040382c02501a0101450521074000500c00307a690400d8105411b02860b1405e032516202035980205580c2c0040c1d44460204415110306a21924a1480020749a4015074094060072641032190303036070300c07048030213400464035104200e4019100744031030302c01048201e103203910101e0310705418103000c544003188001d00840311419610040b02d50740c49201b01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 103996834 1250 103995584 103995587
    0x3030207080c06040312080601180f060905041a100c05060c1902010605060a031107021315080105040809040b010e130e15132604030c0f060806030d0f11100c 69
    0x1d0b6000da010303501c081c04c007490343d101c1c0d04d0740c3d00c0000d544405124980c00440c2c0280d1150f00c20040b02401c8506a00480c4e560f21081007035078060b44a140c001920301d41c40480d1524040c0500000700d0a01c002c001284407540041142822100c0151414410400048000103109202c041c0c810740056000d0703500c401c105120803402040d01600d240440e40361071410310880d6904802e5800001d41480c0001d40701402614040c00c0f44140c560203584005030300001c440f088020781041d010305200e416804032041c1d0f20682d417401d03900283c1c3c00038150441804a85690b0400d640041c1c024001403600111240d4580003082c1c03502c201501001c80e0b1521483c4025001104102030940c517850344404135150319060140301e09a207460b49000b446204001c6a48c80381050543c4445072a0558004280e56155070786004030f20650681f00341c080200704130000003a214055801d20b807044002801a200d00d50000c0803c807865090645480140100041d203184a00c0040040c403171a80e209050003d200a8080300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 103998084 1250 103996834 103996843
    0x70204050a0c0207031101110715090e04050a0602030c0f0a0810150203040b030c040f080d0906031112061c050307061802011d06040506070308100e1005150c070303020708 75
    0x72001d0072508001d05104115800100001102d80000103665103a80c0c00c80100c2c4c11070203000c0303003c81600c50182c0101c0d451145a03128210140310f920303160784159403410b004007071981c22180503045800c0715240e000440c84a80055a1001c0c0307465566260035100c101040ca55003005075000000b414140800c64002000c20201020b00403a000ca18451050035a0084d0f84c0c0c45140204c00c400f05001c400b00d071240c800e442c1030310007030480340030030940c440e4480c15240c4c0d45d03120004841c40040d941000c001501402407140b05001000907071010700e0001000c21002c20840c0191050b600250b1444600245c600742d21200c80d0750b1881031010303594500d00350504906035401007480100401d101111400143c2e0001614103091012035001d0000c3c880c2c50300051180c0c0a29840b054025400040c25010103521080e400d10400120f080c98490300c1d00c0b80d00341800c2d040c00710744001c1d07860003025003400f0324941044510141010a0708182c41d1000a0710300500b4500c07141d100b28050b901c44141071151150600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 103999334 1250 103998084 103998091
    0x16090302180703050105091302010309050a020a06080406060605030601120b0a0806070c0c0b0412260412140105071409060d0204090506120115030209040201021c0816020102041a09061204060207020405 88
    0x140c0703200040c00c082c8d40ba01c0b402860444000d050640e40c21540782005818000000e10f15002050a800140e44020250201e80c08480032107440345484c1000c141c1a006e68180c030700030302c01a516120040e1a00d034101005001d0098150750111980c807000400750b41c01c00c03550348600c03020f40c0d402c0c441e04182e10340b2542d02096038000606844c0240300500c8a11090103042880a8126027642c06590f0001c1e100186a80100911301c4030700800180450b4221001d00401110341c804c44100c0544a010003c0502300c0d2000d4070a240001d5843c041d40503020800809003d6541c8003c01540c5030019501b40714080740c0c0150321082c107685e210002c2081502d010b0111001800b41c2100030301100c0240c000711440c210803400020320034108900490305591003001075103000c1c4041c1140310741c50a44c0d454003920001c01110350354041d136415101542010300c10700950b0100c501e090a01c1c001801c00c4844140329800c50000607402c980e081c004c81007408008207125019038005c041c01a90b500517401800107464000303 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 104000584 1250 103999334 103999339
    0xf03050417070c0f0e0f0609090a063606050105150304120918050a05070203072301020702060a0504050406050f030d08070e0301060611060601030c050316090302180703050105 77
    0x10041002180003085000c003411035080c0340c540e80340d0b82490401c000301c0568100e40122001c0680c04075908070385010041c000d5800040f218a507a54003010800d03040422664030303000f03411101d03005000600d250490301602d00c0b02d00310801034440d02c0100345010a1003294032000c0e02d0304081100240b1003584146809810140c0d410024403920307140340061880081c0c402040c580c11440340c07c50007849801c0a5010305260190f10308906d5014071802d01030407094604008551420012401c02400007007240c9440754000c070303604080d4249500306400070000340e112480a540030809d038001645c504000703099005c42621100d403070b82e05100038003040383d030070f41c03c958010070940c0515070f01039070002250320b43c401d01ca01d802191582c0340e01c011601c0c540f40544142c0c2660a1030f001042c3d6a400280180e1420000404c9908540d550001102034844854060b00410b40030004a154100100803002d50000682031001045a8070ba02060304081c002200e032005964000500280a515010701e03401000d08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 104001834 1250 104000584 104000591
    0x60103140d020604030507060f02030a0b030708010c1403130f05060103050609070b040e0601021e01020903190f030c030905030607050415142b0612050d1701150309150c0f03 76
    0x5400c000382d81c2d03d00c05003000d814050302054100800515402035068032001e032409648a0030104078501c05024a0012644203000780d01c00883c407140140315a921000059940d94032400420203910925800904501810b090011004000c0746406020301c13106480361300100740540c03540c2007031410301e00003a0440e041034000c240100691003142d029581070b80c104401ca0942e9458074401070b4503007040c490002007c2a003038217071030400c3d16040d80509004071080d0706440342c010342c480030281901d1550fa030082c4400c1e103600003070011030f20404c445640d145c805c0c00c6c130405190301d0750002442c11004847d8030340081d50006041c08110b2423692114080c82143c08c1010055206500c0c0c03480074040c10080d10310f001c0a1401c0c1f1032025203000d043d240c0c0c00442e01000c1080a03111100c0441d2105224420b440e1840f916107041865403291070101541c080f0340718150307081e90a05d48861016050707103482408054940c041040860310500e204015070205040004408040f6413002d0061003100c811031042c50b14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 104003084 1250 104001834 104001853
    0x50702011805030601262505060702061b0a08070c0f050f0a03122003031f180c030902131505030a03080f060109150306050108060a06050d0b0f1206010314 68
    0x10000390341810b456034001d001b8084180c0003a0040120389164040e5880d104442602d0680100074000b80200c80100c401003000c140c407a0140038003131242d004001e4020f0320422044600b6039485408000310400041520140706031a1100002c0707820070442a1070584d01e41a04000d0940c1e04100100280001e5803400909110300c0001410b420f01031202a10000441c0382c1c10040c01d1051942076180c003030000d185400c01800d0458166a50011034003030110480704a55411007641d030110b404200c0303148051140f04001645000d50113000a9003001c0180368a510031580140d61b07045844095228040e0000340d0030b01014440354015074517620050003a0003412916021a0b030169030950300c2070141703014090320340707031032004881c1307103450394441410704203c1b092424210758103400c014202c4078242d032441150b482d403600700213100546204c0c440c041041004050180d00e0301e5002620700b9100203114991850112021511104066001340c80c607401100040c0b080002d40f41c0c4601410030520000d007d20032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 104004334 1250 104003084 104003089
    0x90e0705040e0c0d110a060938071a04110a05040e031803030f03091e160302041a130e011802010206071101110a031a0f0303090d020a0e07050702011805 67
    0x494808440c000c400c030031503d5050044800001e00311100192a02c0105595018010140e000274042c9042340000c0b500114401c40800007001500c4150600c4d00c0d1107411018447c0d04c00c2d034040c501c00c80d20460030702c0328941e401800d0200d00b84124007500400e0a10328100007000107000250700000e206620741104500c4001001003600c42c01a241211215004a400002440c50041d0000c084001000004004860501103240810200c030482d024200c044081a1952240c1c000e0144081c3c40542010030409450b083d0480349500d4200420200302a4078480403903041d8042c8102d40121a880f01080e40a1000134440c14a841020340260210207410b940000d444040c058031450400c04002080804190290701c0441c0014103103a5842e524800514040e0240c0401c00d184c030030058240c894070909041a00b1502110f00004002d10318250040c02001a48010b20605036041000b0f160003003440d0300907100340742c0190300544550391100e043d03200041a025850b28031202d010421802004640c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 104005584 1250 104004334 104004343
    0x100801060e100504032003061b0a1d0a03110a090605090403050a0215071e0f02070501030f060503010203100504050115050306010c080d09030801050108070f0234090e0705040e 77
    0x42201c0302042208a168100d8680c011600041d0810046c110f50303202034030054415002508099080d500341d95035940c076550301001c1c81604c4d8400b080b030400102c0c0c3c07041e02c251070720070429101d0b202100582c000c0d5030118441d13101581040b1445400060b03003090328648010040020b06410a00388565401c0601103404d20b08040d10050600c1004240b0f030324054024010601c4e410003202603680a494940c4005150b0303070500340410440d4203512845c220642c805d0304504208241c940041041c90315190044008020030207402d1300050740da103000304031030340c080c00254011140c03d98000308203414541000b040f11010b030301c104100d40400c40f0009440f0f80060903642c0c494400d00f06441c008d07540c0c0c1802c0249100d00d518022030540b80c042d047c4105138100344841e05130f5000ba030300d2640796522744600346c2c4da444801140a000d680001010104203c08207091800400103d800e800c21609951180d41154501d80182c2c0d5107030b031141540148101c041251000903c1c0c121400d00400d0b00301d10026850303 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 104006834 1250 104005584 104005607
    0x12040506040306020a020a1b060e01030b03061b090a0e060f01020a1e0c0302041e0e0102031e04050f0105090708010b060306090402010c020f13270c0501080a0609090c030210080106 79
    0x5580c0109403402494024800647e603240c01400c0f2105850140780407206884c2c2030300501c1d010030712001c500d00070703035120348584c015041c80900108025140c213107409508108000341500d0010041001a03600d440c0e5560410091204030400e40040c00d2010420140d04003403400b1074110b42c07014030100d01040754100c5003441c0079070022600c441101c007030801543c2240d417500042c4d00b103410202c0b1400948060065103210a000c0e56080085501406c60907081c0e100079107020001550805800c410103400c6c1d21403e41141c0714000700c903031600e0082403650954004032210740a80d04451020000e010082c0114049407004942040c598501400050540c1794060006810000c001c4400030841d2150304020f60810700c001c182c0c2440280d00144c0d080505440030140000c8094003404c80031030910892240d86c4650701410784c0c0302c59400c0c0b40045441000c002d10080c0407648840c07000825448622a200d2014040c4104024507030550052000800d801c41d00a010001450010000070303521503c1c0d03605 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 104008084 1250 104006834 104006843
    0xf3c03210f031b0f09090a050906150613141305011d0a022b0f0605030c04020307120501180608031215010e090a020d27030c06060312030c02120405060403 68
    0x2202e840354140b4040c01c104a10200311401000607141602240c4c8a010304a0541c0c1100c61901039030315032a4a205a5505564010480e801000030401298200c8003440764080c1c0500000d0500c0214505045080d5030341e0300c049020352100030201a64140281010340070403d140040c0b09a51610400079000502c0c90101480d100040020a012682540440d6403808a003103a80307055520890365000720481c8420307005e5600c0d25200d2044c0365101d0301d0203090100c4000402410080ca440c809000c042d40c001091001048400d15810883e4244d51007464083d180030f440100301641e01c3c54009003101e12542202050754030a03c40171090400326440b290b4002c0301000e54140c00412500140c0380040740c151402c0d0b11480810405c14a01201c1c0c0c0030b89002015001d080c08603011a2f1041d42a030098141128140c2610711070f80000f080c02250340c1900c0d28441c082c00915150f823a110003980c6140c0f001d0340d10002351200c404030003040c2e0400c404103138110f1040249140518001c0003482c90310940c0300040c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 104009334 1250 104008084 104008087
    0x6060a0519120e0c01020106090624090503060702030703020d0e030a020f420a0203031b07060905060402010f08010501020309040e01060803070c080105150f3c03210f 73
    0xe00c45110700c0e802c502d0074103407a0701800060715001c0c009448442e12020103005600e480000113146c042c9001b14802c640da503003015811800c00c1c5c40c080c07141022400c000300c1804030081002400342c40400c0090f2180030107501658a5968518000341403c128107503000c00c1042c1c104101400d9980880c448903d99411aa001023103400741d0049800058201d200c2d0300582c640202c0d50030482c042100348081c0101d5400b0700d120000341c3e007821014501806400e000168010700c0015005882c40105041c0c1c07900101000b81002600d60b1200d0039121511012239081c0c0140c1c05010840d40c100806441d02034003410f1580c0b696041c000000d50b81e001e14500e5a11460f1100720740054035030f0a41c8100080c00304081526640c5100d0b080140c00e50607140700c0c01900d03610f081d0000340891201400b03183c8003107008004886082411040003603164440503035681494000c5801015800d0303000c8001505580b03181d9001117541d40e1020542080301e03401442c1000e40000314000180011102101d140c500e5940086 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 104010584 1250 104009334 104009377
    0xc03011d0a110c01060f050a0f061b08070606050f030105091002070804030218090609010c0507030302070516090501051507021018080f100612050d0f030902040906060e06060a05 78
    0x80c00900004400b46000341c80c0003969903002c0e40b041d013010342a00e480d04010758095560b0014401034221034070450440c200400414407203070748659100c072030038100e02c2e2171111030404030b407545400d0768812901201c241d55103078010450790616141e400c104a50850007088103107440300c0c005840311600300791b00d0f284ca94005149002c00c1580403d2700c000c0c640203801c6101c58000c29240c00d0070101e0076141000c544c4141800940c0038481401128004880340d0b8486040c030131207550aa0103074010080449050145499408081452190420040100703070004201540b4200911031441028240d844059034200301410160300c601f00462100c4d1041d03c0c10040c0b03803980402c0f05500c0b20460b0032408040c00340032420701061000280380100c20032000010095103070381d070044190f01d15170094020b2a94025a12041c1c1085c040e010803094418141000720320340c0042d50008007210001e00c0c0c00c0710001d981d1f5400740f05116051102c80d5200109846841c43d1403100e00c0c1c00b070464081c1c0100643c103261280d149 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 104011834 1250 104010584 104010601
    0x60105011209050f0c280303051303060e210903060402060d060e18010b0901051c0302010e0d020307060b180a0e0717010b09060913110303040b120406050c03011d 71
    0xb000c0030301d40200a4440f1074070b40c1010b00d622441e58078480e80c41a070703442c500e4190280341d0011400c0300c0100314110202c0e00d803459038252465003001d1480e000c0d0118007980000410480d006244c001d6031400068150f101d00e282c0c1d09841d810f0301d11001c103d691024800041940c40014406d604250122041da031101c58074a042d0026001a801c550380300c11804052220f09609a07070207803040d030351480090107644550414400106401d11599500007250003400030104035112800440c903000303100100e00d00490380e841500d8a1845900c80c40160b0000a06030300f0302c40b03188941c0e003042e5002c90b00220002c03000419100418005030407400d2450b62130030030841c40030040140c0d00081401242b100c0c40342540c2c07160b4500900504040600808204002408924004003040d104a02103104a042654503484141240003c0541e854051000300008901c8501110140215403802142403019192515180c0f043c0c4101410321051001c048c00107102d8556044c0192491142d000c1c0203840c503580d02c101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 104013084 1250 104011834 104011841
    0x6030e0c030f0313080118060b040e07060507030201050f0c19110601090506040506010f0f030222030803040c080111040b0a020a0c0e0601020705090903030f0408120a050a06090e0601050112 83
    0x30560602c07400840b16509100800030b45480c003100300704509003541e00c003511400d840d894000d4484521032034100c540005e016910034001039101500020f170419080b46401e01d0300d12150080303004114045a581c04040e4240541035101d4441410060307141844100d00c400390083e031860002c1580d070010301c03540d03840c4107440191a940c412800c4500740c1d655510500c0c0103100c240c032840c4c0a01d040000040c046d50013154813242c05503080e41d41038000c00360b11500324025003000c8481e071403001031400703490304100211900b01c0c055030085c10443d07a281040e107043c0d03460182d158070001180e410002c184d90100352803416207080740e4002000690791180458228101682c0c1d5100801c0602d00c04004205280c40010642c455202a001c807446642c840d010002e0100c0d007180c04449580c010000121740e0300c1c82101c4150000c0c03003a0400e43c10900c08030569459001e080b03618a0520380c0e00c0041041111003401b9420040800d01d80400142e120030509544640741409103d05010800130301c440d8105440c0d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 104014334 1250 104013084 104013103
    0x60807031e080a030c090605070c140a0515030901051f030609080d02070302010906050a0b220207021201090b0114090403080601210213060905031005060609040504032d0906030e 78
    0x1030010365030701c18015000d0000c2c40d83d05c101c00c2c000340d0a1348001c00c0c0319018074102e4000c01e80100c80c21140e0340c07415120001d40102d4000a907001425010001000d80b107503030510841052405c40c998892402184441c00c4071401806c5c00310b0b02c281c0111f1310180410a05100b82581c0e003108002c207040c051414a01c0c0700b84180300c52105014800640c00c0b080c540d041d407101c00c503a4440c1d01c003400a0b40b1440c80c1c9074142d8840b110441d501ca15082500c0b40020a4021805800a0f43d0a400f5003400b45680018020348004414188244d454000e002e00304241044480c0c09010f00071160144003245101049510800400041c18400ca6102240043c1e001d00c00b00359103100c980d0841b00255980603034050182d040030040d680d058590140200340d040c000c903c401c3c05e454002d401044803c6424554802420001c1c01040d004902045002d06580741c900070700d07201c0c03070181d02c038a08801d45400c4448451305480c2e070340c3c9032004014180070350080d42c0204840c04999142c0b50100308003040307004590900400301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 104015584 1250 104014334 104014343
    0x51003020a08060405100b0627030109030503010e07050a0e0f04062103140406140304030c06151410020705042003010806010618030f060203180f03091003060807031e 73
    0x24080001d003079000083c1603208500c1502aa4441110105003100b62111018401d6010f20148650003490965190080101b014100d480903200c0b600c07400700c0d003116554401500040c1c00000144801008484107030b40011b0103140075840d00510020080c10039048030600c0e03228244d4010179410547d03d07600550301803d9400652121401342c9020401e0884d501d403021008200c01c0071484e440007424000351390484040351103000000d0184521103005500080c4208e041c0701101e0718040128660b449520801900701c11001d02103820452031001c04440c11075807610a401d898a00000e207640032882c242100c0040d6008100c440014400a080140e00081c103110040c0c040000115840005006412100c040e01c4201601030b642d00043e00d03007a5540405041411301280702d60003d0310341c1d07005681c400300941581c0a01200c4000a40c2020101403540d80c16500103d8280f5035881e202c0c03c0c002d461074a906041180c0703880e1030a11501c0d00c0c210311004c2c01c2102c80090308040280810303001400307503a10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 104016834 1250 104015584 104015599
    0x130605060f1003020a0324090509030f07060b0a0905130b0a0612050105010302041113030803070e19180b030a020d0f120201060e0601141b01021c02091801050a060305100302 76
    0x100381c0042c000c5d0000c0032002d0029042003801c500ca80a8640c84030b1a4030f82d211900c21205040117038040140401030b0484000348400c11031001155044030191075054482c040110328450b512040041e61101500700092091401c400d11412000380d0507842c9009521a515441c66030707031184c0c0d1034000d01c0140e000d805108110708405040100641c0100e06880c82100c04110000c000c51580e41d4500500814901d5004103040038000b0654136006503610516a140c420440d50040002c1002614202615031507100049803d20003141030304001200a0344112040107450340d480c0000b641c40d0312000c0040d0042c428841ca240c140000402d0107d80f0a0704000399901c4880000b81c001d008002c144207480c0c106d018100810582c1d1f100e800024030400f400086541005c2d80440820001c01c00c044000001c1c0d0350030098110060502c4040108080d0301c1d40006032200344a00500145407001ca518502d82c4a00c00b00600003aa5501106003e664032450001420364820540b511014501c1d040698025035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 104018084 1250 104016834 104016859
    0x609240e03070515040512010b060a0e03011d0d090e06030a020114071703040605070302030f0402280b0a080612070b1b0703060509010f0902100c030210020a180608130605060f 77
    0x240101c6e003043e90140c140800d803aa01c1401c031441c050b42c03194070950401c80c0e080194803e0303c140c4124180100005030320310b041d242c110201c9100c0c1d015400305c3c0d003011200345c6403145c00c080648020000301e0251a058504440040e48a0b004000300905020705032040f400510440f4041e50b00301c2c2c3d401909032048282c44400d14a82c1c0c0c0003110201c680c20f003003900245a86110740262030007050400e040301d606072202e50802107856085541c01c6000c01e402c1011811a0303000070100c900804000524698a01c2031140003800141e004100d41e002d042d0100641c241034500003900b4089a070003240c011b88640120380c5585143c103501215005034441d403000401030020302d0b40a01d0148440340c000300440514106001c05840c110708010754042a02c04001d0711081c0500e200365103140c400d1066841540007908403a0407030708903000c0c0000081000c2080300800060185120140c442420240400c0c0740424025101101c402402802141c0b0341000c65242e071101c618081d402c00008044807070000c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 104019334 1250 104018084 104018119
    0xb0406020f0f07030b0c09060c06070504140a12060e0a050a06060608012111130e0c0102070e042a030602070b071808060c072a0609240e030705 63
    0x14160074642100e000380b441002c1a25030004160381201d9004c08100d417160b490041c002042d030040c20300a500260100002683e0800a000f000d108804680350203860724140700360380490051121081d0700030000e100c414050052101801d2a41942c00040400e0034008014054205040050014071034800e080b100381c100440364200c0404c0d00e08590300c1040c02d81c1e070390103503d00c400d500c8588400c0d0454525250070100382c24490b01a4243e101a040016420303800d5800011105003040417196604224070340d2943d5030b03051290200815100f01034008500342030320f0b50310706071122041940e9404440c10441d0381c214220520f460007981c0081046454105900301004020700440310200003e01100c80c40300131010200400c03040e00d200c08000e003001c0c1c0c0c41441c401401d03440b0200540c2d0b00143e03500c014600000d117003001c9070724180c01e401189001d890110003425251041d0020007210b002003210003103800342044020703661143c5d4500002840241d10109050007001d40202c2e8001040c0741c110100035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 104020584 1250 104019334 104019343
    0x31b0b07030b0d030f0c030201060f080714010e0a06030513020402040b0309061b0715060f030c0e0f040f0b1f141207050d020105030a180b04020906010207060e010f020102040b040602 80
    0xc090325203003440100000420488060f0000100802040c846140d6142d02803180d0500022a40300c0d00002884d1a2540e00d689491050340c2e101010a80c04004c1c2803201402c58884001017445c00e08000e03250070388400002d58256807034011281010f50b140000340800441e00c0301450450340280007150b650b62143c4150202c2e900850350714507a84a0321007c2075140141020160504011250403403d021440e501c401048503075180325101244c1b00c04000c0384001c0070001c420001c522900a2401843c03804135400110400103103011140c0c5016001c200105a00300340210100da40420909042d80e070344080786c43c060a00f00c03000716000c06100d00c00f00d00c50389000340c1c2481c55071b021a525091030940304010760f03a030b0596003d01c41d0407011698071600194016401341d5080f07221490041104160f40c5003191000165050585000c0820070030b2000b581814064141c00030020f10203080711504258018050190460b14181007100b0f8070380081c102c9200f0350558020301001c01740603540700e68a00009594 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 104021834 1250 104020584 104020591
    0x2090415051c0305190504030813060801060c08040b0703020f070806070e03010204030507050910090507021011160206132112080702070b09040605030d120b120604020d031b0b 77
    0x10001c1009106812007141e1552000d0765043e070314545000e20744060314517480081e07840f00060140510000c00068040d00c09850704000c9803500c050310b6440c0c484003e0100340c0c10303030111042c41624060080810107541c200c50507510320f158002c2c4e48000c0c0780740c201c0c0b400f409003001c0c6500380201d110100c2d01245c04500c00c1e015624030f664555071107112104240c00c0f0300c11032000030590b0703020400402990034240c2600303602c558440382e100211680c5a0121040c0c4604541c803200580203e1004c0548a545108880d800414012580c1c10300300b01f500020f2901c840d80c1c0c40a0312030b41021656800000c144101c000207048042c019048035181516911b01c00b100e040380440c0c80c04040300480e460644960003581c8075400c554018100f00346814188034081c3d201012642c0c001d03441e0400424240c50030000c00e2020400d0369100b20071031403181c10380401c075441100b03018840d024002220340c41c2080041d0258001e0380440303a05540d40740500e816a4509540410b54040110b104507a105020024091611 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 104023084 1250 104021834 104021839
    0x10903020c27060d05150105091308030a0906020d0c0909050705030f0f0702010f0e0c10020304050109030b09150403051207080c072006040801090311011103010b07060209041505 78
    0x640080141000b0484108040300c886502282050341d003000c80350b0112941000018251402149a9031510390512a01000144e007a4003020010845801e000c1942580580a4a0b18250025450743c840ca85031002400e0050350360784585000d82401034036410ad541d01440c0d01c00401c43c0c0d0500d404050420103142c814102154070308400908920700070421a0b1050040c0d0f035221490703584482d18001032420280c00c1b039086640e02d80c4043c1d6600614403c1004145261006000440340700c810090948003d800c000d0864005000401503660030400c1c010549502c40b0000c800d40ea500b5007103900d001c8a8403440140d04c224803080c401419080401411004204001a400c59861040c103a80b40801510f20394184102002200045496050703410044000300b8244c0215409110020b450b5401c203800c00d00301a5522000c0000b01074220244c20a262045002030241c0001c0201c0d101080c0014402e1810400d00040c02c0c60401c5200d9048902c0010000d1040025802400d02140d041e50f00380100d60 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 104024334 1250 104023084 104023093
    0x5040b09060303030402131e05040510061406090112050103030c0218010608010311061b0601050301060e061f020a0602040e010e061804020103020a091a0c0c010f05040303050913020c01090302 84
    0x41241400d140692295102400030751441c0c6840e800e02240c0140840480d2010b0743e21801c0700701c803410044484618040e03044012030f070b1b41042c0c1406030802a0141100322941d00d84001000041c00c0307001c80c245610001c41708903480c0d480140042e1403024440000c001c0051601c0d0000c0f0030142c01240203c51715000f03803522040080818450442c4420078001c40300854024001000069031310500500b10940291000b07040c2050641c2400d44802c1c03070a241c0005410501c0180240d040901c2410000c0c8035040f60002c40d0300b0844003107001280711a101445480c240481444154000c00c000440f031580040b0440d0340395507a080c646000c00c0280201800210f088000c10700520303084010040c09402c1c00c1041c1c43d01d031503030360065001354031041c001b4041c004007200010308006106420301c000d2030305620050b92880e80000301401d2010703503e4217606010440340c0d07402c3c3c1941d114042d9030a032541810610b55454020380007c0003180c0341907605131503900010304807240080640040007283d10030340868 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 104025584 1250 104024334 104024351
    0x709230a022508090402070c170606030105070201091a0a0618050402010e090402010f03200406020a0b010906080607080a14150901091a090615130303080105062107030605060a02070504 81
    0x684110300e0301d00080e011020604c024900b41c50310b1350003404d62621400c2c1e100159a42c0e000e011104041c611914800b0350402c10400c48142403e002e01d69110300f4601c001c01403250a640c03400e80c40015070072081d15411804d030004a1912160340b000b0080c00300040800c44c130407201e00143d00a0101140d0884c0000d8800a0120f41030514040c403602469050b1242c1211300a5103000b18001d0110040b00f4502d803111280c00703d8861404c00042001c1c241035405041421000d051070070034007a0607884410b0807882c00c1c004114601d070101e15a50482c100c0e107012003207511100c0008018110010075181841101c00c180b02000041408aa0303590030243c4400740396a84e103c4030300003155540b410501442003c003a00900303520340707418400d82c841401410203c4182030300607840f080350000d1601c0c000300d021a0401f0b00506800c0303040c0500500c0121116440d29803080c81e0840030074628080d50b8644040d402c0440c60982c02a04184082c0102a011303d4540d00c068070000c1d0f541a083c46050f014070b2806a04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 104026834 1250 104025584 104025637
    0x705011e211b12020403110415030c1e12050309090c040305010c05091e010f050a090801050a060302130203070c060c020f0f0d09170a030f021e01020d0506060703020709230a02 77
    0x1e0740c040329088005c0b818601c7c200414080501200d0410b4090042d29010110008030340e14031040261074544249203400d0000c0110110b0710780960000c20700e1a00d40d02d0700b2800640004100c0d122a5010358401c48640c41d00e10010050340510b0300001c00c0d950038241d00760700e002d5016001d400e101da011910381c20810208103813039028076115005140011181c011380d090482c0908014401140c080ca411080650740d007040d1401c660003030316102c0c405a291700080082d0b25052485d0314810901031011072844c2800d040103452a0305071500100b0341030f118074500010a00a1242e640e0411302001070300c5008500140c1c00307840340c078002219000300d60f0344170012a00c041c4901c00c01705900320303800c0108085040b60700e0a45680c503000f0140d200310b00c108201070746140758119443d00100c0c40c040016855440d80001c080c02c0d94002802a802500c00340710040100c1e500242040c100c513801480054054083c07180f40c0006c03c1c5441d00c20800174081424042c9940f550707070007896549031031004100070205042c2d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 104028084 1250 104026834 104026837
    0x9060b040b010f05031017010902010e060310050d1401021803100902010c1403090d060903080c0a0c0b0a0e030f0c06060d0b041103010204030c0306020a020705011e211b1202 76
    0x46000a65000d122407009000300001c603041b100c02601a00c0c00391751800c0386403480100c0c03041140b0716511042007504558001e80c0401010b80308448550652802200fa519494164821a031252012001140a10106400f4026243c078814000d6684100d0b44c940c000745841c181c52054000c0c4520b0241c3c0c01401c020303103c0c20f0b950560587d290252010715890f03009a0403440101038480d030104000002c02039440102c031500c0c0c00d200321b20209511100c3e0a018040110092551420290030403025030303501d82c4171480f40380856005500b401282c0741c4141060003069192010141032100185001c40407503110040c000c046100c0e801c032200d41d030701c0d00103120100804142c02440c0c642c1800c04580051040504c3c80c86c408005800182465540e0b01da072584031500d9072003615615400900c4c0c0500aa052124901800081c00c0c9080034401100003400110900700400c403c110128100105081ea01c6641c2840d461030f0400c180842100c050319245000c190000d000086030b01d101145408000340d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 104029334 1250 104028084 104028101
    0xb0a02130519051e030106030b0405010e0102040b0a1125050906060702031509151003060509010b100e01031d2413020d05030c0a030306140418020127080109060b04 72
    0xc2c80d030322a10f25020900c40e5681e200f03044101200c540078035603002914240b2824004501984003591a8103203810003030301310360084840031140d900400060000c034007408100d91003a150380c94248240c001104c03180703045c0500074850101c5600302c000c01e03000e200240d081c0c1406858080b02c85031030544031f42c030070440c862045000003500342c1c01c40c0703600c07140304041920440d6100070307520300b9219410710b025401d0404e80401c4800306000d180740384051007403003580d10034103034000c020300020001149903100003041d01c1c0b100340c03c2c01d08000160048404c02e91013600710b00b07400310042440c03403200301e12018100c3c1c4600c045000503018002c0101250040820380140c580a43d41281000c900000684c09201c00070698480640f232900c000c110181510104000d44052035010b039400190317203400d05007080c078910800c40e50b1a01ca50304295006424100c0c00d4a1442e40030380c2400c04020ac01d008001d0100402d100d007a10b00445014080b0003d020003041d000b403405203100303405c10401c0e00d1a00c0d040004030340068 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 104030584 1250 104029334 104029369
    0xd050301092d020705030d0c02011b080907050405090c1e030c0a0b0708030705160308040c050307051e0a050a09140a02070b04020d1401020d14070c0302030f0310030b0a021305 77
    0xb80e1034803101d035a1580c0200015806070b03080d2440c00b03076174880c4801a90030b500340c0000181c1d500e600f400c100e181c240752031103a40151450a01c1c0b060601c0702c403241d41c900442c0505481103955401081c909813041120403141e60019003034110802c3c3c00034020303c0000002c4511070103401031017480001803901c10744e52800c1c0e507444081c95080c4600d940310f450203504000c2c11ba1003440410000e0940c2008841d589601c0707648255202a0310345024500300d18001c0c444c0e44081c2c0030f131340440c1090086654100a01c081144484003030b00d402e8540c0703400030f00008d10070ba002a0704181d4658001c1801541a00100480d0740700e014440702d140c687c440210200e100f048400381c4041e070b507070300403400500c0c005140d51800e50060700e80c8240441948d4509007283d11698203580810741c0c40d160898034800c0c01310b507107501c4641c5042441a145003074502075164440c01c5541c148910f40040015046845000490041c68002598998500c3c190f14800004c1d8040c1079845603245c80068001100e1901c0300c050341c0009180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 104031834 1250 104030584 104030651
    0xf05010803040b0a020129120613060f060506070b01080d02060c04060f030b130207140f0c01080403050d02040b180316060e0d020d050304061715010c0807050d05030109 74
    0x30003c140703c482c2c1141a201c8115501c4007400c00c07403491061490703419007180800103504941c101e001c000c20510840003010f1190801001c1010b130005050309407500c15044000855409511b918000040040f50000c5034002e40101e500030510044c4441181641d500c0801c981045e030185009980c0d03080c007100c0300500c0d03074070420050020030b11416840354015040d05000c07420310380050008404500c01149141455804100300c4144600f000c1745050f04001207001d04269506c1740d01035611054507018441c1070205c00740104003014824400c41e484026210000c646460711956111b02c580d100c1c080305c160f02c910301840c0768464503002c103200780031909907600d2401d01392034484140c0d11300c0c0e00b00f000c8039844202c00403a074025031903c4064001c507620a601943c0d0302e90a041e0041d013100e40c0881041d441600354010030200c0a0041c00385180c5031024204040028020b103010710880c400c09a00400341e0142c03440d036036009034201c006141030301e18400d02444a8000351a480c01052052401d450b54440f4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 104033084 1250 104031834 104031839
    0xc090601050c010e0a06200405090402090402060c0a0305070303061508270118020108010e15040f020c030d06030b09010e060112020102070e072c010804060509100e0708010f0501080304 81
    0x810041442180b40c1001091110307140b10043d041020440302a0713002a200d52000450808084000308405541d00c0000c1c20300e800c01002c510305e4800100000c0c0101e081c40c0110702556520410f48921040181c110303000f0421a142c010190741020b4401c902190911038040361169401c04425998241580c40f40d08031f40d208080075856040102c02d00c9170320b8107040d046101404080c041c3e82d22200030250a1008815984001415200140c1c00480048941c20a00c10301c215603070750340f40c0c5140302150080748200d55406414006e12400e424003a0500c000550f4403501c2c07400360000001c40b8014107005000c0e0303070345103001d03402d0303680e4000501d8154003d400180500021382d01c41400c00e50062040b102c0342074580c002d0041028090f101071011501440c0801501030341c840e480c1001851080440800254000000e815080081e000905850311007002501402e0100118458217440313a205001d00314060007407070b44030442070054400a508001c01540460054080d00d0b0484110700d005600e02403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 104034334 1250 104033084 104033087
    0xc0906010f12060b0a0915030e0a06020705070f030609020f060309030d0908090d0b18030a09050103020d0e240a0605010f0807030e06010e16030c020303010b07020301140108011b020c090601 83
    0x2074603008000101960349101041005083c03001c1c01170010b550701d0780c130307082030038183c1d2103105205440d40c000400d030420244e8000c1c40c0d0b000c100e03201d0080d80410701584814040c038000b814007282d45c106100c100090800042807000c65000200c115000b650030a10a502c40d1091007802c2c0310481d10382440d03034010003140b1440001a4800702449000f44982800d2509620020b070012550101c1581c08003d90010b1110300005150072600e8400d04000071450084801d401030280802c51107218107042c0d000c10451052101034018104c0c9a480b6400d807401340040c0d441c0034070340d801a1040ac11150988000080ca0300400d44551070613034405840765405080444400c87c0d42c40c0c8010154410140c45001001821004000c52400380c85070b020f0070707681490000c00c4000e281c40d603880318004242c1051600101140c020040320305641d8004081070343c40d001400800d0242c454011130300070800004e800004c4000044d07102007840d030290045940c400c0119482269205082c2e0034140c2e000841101007107596 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 104035584 1250 104034334 104034347
    0xb030703020f1009030506070804121b030806010e04060801020c07060e0303030406020313051b01120c090e1b03040605010603060b0a02070506090111010504030804050d090807050409060b0316080c0906010f 90
    0x265403516041c0d04042d205c6d5149130030400f060341d561020900c80d405100400005d0392280c866a452881d01ca4030000f071101300c081703c0c042064006000d010b54480030800790303441481004800c85016200380f210a94405105000390b00071080c80080d4060000c0205405119180111110400500450441d11039466140081d030003d000440c104249010300d90000700180300440d00d0001d00f0701e540b42c4486200d00090300c10b02401070920003041c50011040c1c9850741110110301581c0c500800c0411654402e00100c540b10f00000c00d40c8202000482044104003094010130305071080f0b540c00b031128a584d0080c0c9900380c040d080809000d82c000c10818010303420500c01070a500310051610884502230070902d2801c5510580c0c050f030010721850704000c1886020000f00c1c031048a1860001e848900d000d40da541c403091240035541c403403901d414000042c0b062130340080130b400d84003c081d12480c6011007016a520b501602c640f007010300a00480e85014602080c44038412841a19400381881200b102207130704 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 104036834 1250 104035584 104035609
    0x70902030a06030b01031505180d0804030219060f0e03070c090c052a121e070807081303150612020607020d060509010b0a0e010b0a0c030302090303030709090b030703020f 75
    0x540b659600d00102003580000c05070700841c020441420900044403540c01550402454202c008201d44c206c203410030350000e91261200d4907841d0032003103501d440c6001c07070800c800c0742c114a66500c04801c1c407a0a00000354841581800500ba040100c00e60508031a5100c3c0130f8003c0c040c0c144441315508000c1110b254010306d44040c400d2901c0352500400e800016001e1608641c0040f00c40b42e190b0007400c0c01c0d00208030188065428000e600d0400844c01681c0303058a42412515007128400b1589008102140056400d002d038041805500c42c0101075911550214034401541c20031004020b210075182e042c401c20056510304c821420b150388143d002d104036680100c5d01203070081082028500859010301c0317282d014100080000c114201001c040210400054002084440c0078000400c0305124800803034038036080380d0414000d04440c0782420b400900800740c3e1650117000001c10441c0c102d074000d14080030b07900c040030201310f0501c1c01c1040c19a15030217800003d40018441c0e0800341b452030150b045016 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 104038084 1250 104036834 104036851
    0x303080f0712060603140a05060a0902070203010b0a0e1017030d053312030c030a08130606080307020406060e010801140616110306090a0f0f0303060510021b1207090203 74
    0xa0b81c80c030804901088808a611050000f40d4400d00091006441000682c00c00e816010900c101d0402d10300140f5040c089104450440b40d00140c03c20854500390041c85ca070940040c1100e15003a41c407910300b00040821107610217000170701c1102181100801050142030b040410085081241e000010f03802420081c183d80b8a400c46803801c940030f641040d0804106001b8038090303000070101007042c0070101302c604110036081e42040c0880b0388a004000161041c158682c50064010746030388040e20104002000c0c00780c8846e04003000461120000801404000d01c03d0f10100300d030f180d0718901100c0600b000d1480758001500c10380100180034400c50741c0f01346100c004080504d030020111010007034919a200403600818041c080d412a0b250600c001a1f01068000c00703407004405a513a948090052200300130103c0048011344420f1601c02e62122015020144c400c1d000c2036004480039544200005010b00448402c3c0c12010341c600300f44002229042100c030040c00128201200c6002a4000801080c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 104039334 1250 104038084 104038097
    0x1c0b1e22050607030c0f020705060702040513080a0507300f0908010228050418050901020f0406020c03060603010b010c06051f03080a030501090501050a090f0f110417070303080f07 79
    0x441d00c18022107016031030a4a00260311141000c0203803004000381054415900070540811180e1100303011901c8a5604513800102a0750b91400d01002a401100c09007003414040b8454003125003000041982c00c5c0585112041e2141c504041c500c81c1001703081b0b07580c40303000700c6e80f160500c0c6d80103004c100d2a40545060904034652120380e40360880c3c121044120344041d001c0f48a0344e441a18201c0c0550724001d80c502103150900340f00c4940c91300c3c40203002c500c0350075a6490016403803003029410790700b0f0300c81051641a600d80e5204002507495900ca10020b00c04e00801000c61756520b07051180502041041c1c43d0004420703000d4559000400b4001e1641c5402000380141540000c0f2001c4a00f018610030080c044d241c0500301001800c850058122050742c502d0500140016a90b8482d054112001554040303001d40014000c44060101c0a085d1840907081c01201110f140701000034005035004014600409421a2980b550b645004c2c070010300410303000c0e070101e400560180e6129a00a06c9401d114 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 104040584 1250 104039334 104039401
    0x609010c060b09090a0b010f0f05130e03030a0f05090601050901060507060b0411030907080c060d09020105090a0b182e021504050304090b010503061f02010b1c0b1e 72
    0x11101d0f0811034056525411a85402c800c00155644450261100c6940048280c1c1852005a4003007001d0082d9881600c1d401c0100d200b45016800c0441c3c2101c810054985030704088003160302812030701400c000e8140c144800112030b0440010406e040381c800400c03c2c151a4031f440d8040c0e62661107418161091a10b44802070f030540c5542c011007004100c2c2e40c120329641d10f088140c140c2802016081180c844c0c000d15107204680d039480094520f030710b00c00040050114503620050300c0c580f02c4c0e81502604900e01000002d401d054a4024006180c055404840d181001d13008000b541d04401d51800460010640d10b40d44400000d0808110400b03680103c842c402102840f086e08050120750444260b400020248000c0000380200341e402c0f030080c00d01904500b04000021341042c1030050740614202c064800303100c024403d401c1003140c0c680c007a009070000c00880d10380344044d17002118140d1f064140000810394602552040c4034000f040700005080f1900c0f48900d418100742c200a41c1d0706d40182ca034108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 104041834 1250 104040584 104040589
    0x9030a0f02010f08070926010c031e020702010c1103011e0b0a06031103070c050718091a01030201050403060902041d0a0215040b070303020c07080d1710050609010c060b 74
    0x111144601038825684100320a2000400500d0048580010010640180400d45800c45a03440640d04544801d1840302081c90742403141c40e050303440b01401c45d82009040542c80b034140c2d10010304842c2075034088020700d143c8902401680300b1074100900080791109000c01080e2241b00041c2c440300010000700d5040d0744500301c50503400f50040030808959481e11013516a1501101200c01009641400e00c00030040310385030b8025000c000d200c0c000340b1003a20085010081d0500460000d841104c0d44049450a046484030044c01c5210f0f00311a00310b051250072074040d500882c10b50480384c0c143d50386850a030640ea0ba01010f408a800120703041380c1c41b01240c03100005010f0030380c41201840001442d9911841c01040100e8148100080c614441088140318001c11070007103800044e054103025a446050081040c40c05d5040c0c1d0100e1040e020b094458200194400103440c1604880c50300070900b501c3c0c6030030b100c208014601c203181d4400b00070440343c0b500d5402481d200300f036203024520000305c030300484c4017 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 104043084 1250 104041834 104041843
    0xc130204030f080d0f06140d150e070e0f091c02010603050a0b0f06010918020a210213060329040228020d110a1e0f080a110115030312020903 62
    0x5080f01c4254020407072542c2d502c0d0034810409171101000d4240911442c018903040c00401d070b0181c0314000d148043c3c522042c03144200312a003800b42d01c07220411103280d61015440d11030b83c13140a680d84c000750b81381c0800d004010800007180903804c0103020b4075840124403034079540c0401c052508025552200400400b0820610140028600607a0504440e1034100071980300c510004100d00c0c10301c43d68060902405400b030707420f64641b03883d036070b001a607981c1e1408082c0d0384220240d20f421401714002944041c9400c41d50003414501d03080d0300c48200c60540380c640550030340fa980e800c07040858000400c40d1115172181042c1c001105000303480186480d40b0742050f8844204440d045607038081c6101c82c7d03814100d9042040c141c0154003850044040c1158100705501d0b250f02e070401602c00043e202551130790204d20f0354030304803080e808083c0c50024000f5207001d203070980051489902081644000500c0b2503c1800346e4014521a4003032102c0c007500390707541503030b45002e61608403001e07540c00e022198498a0400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 104044334 1250 104043084 104043113
    0xf03040605070c080a051203100b04241106160e0d03020706080c0708040506091804030e03010b012d0e030304121203020403170309030904050112030807050406020c13020403 76
    0x503241e680c1c41c49181030849091400d40d00c125060b910011800021601c04100880041c011400155807034640c00804840096142c114004164000600040f2440c040c080300c01e4102c2480000e008124240406907030380c12400007600d0581e04080c00040704c9140e03140103c1d20f612513030f0410564114080c07001c1464950b48580460140c0e00c556411b100ca19086850300b54080340d8040d0407803030a12182d6030304030180101d100c0d20b03009650100781111655604108680b60700d0722001c003450740e468107060044c03cbd070442456450095107030610007009540304039100d81a0003562808580d03941014a0302c1c041b082c0351004010704000911815810b1540d041c00208010980307a10103621200d0942000604950722100303c10a00d441004200b000a00000c620301c0412400942a502d90b07841c0e0009500354468203e05507841803801c0d0000c075690b407240450498040c0290344000c00c643d141c0500b1f54080c8594001c010150b40202d42101252900c03400b49039a1600f50000541415600c0c0c6d503100d5890b5140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 104045584 1250 104044334 104044337
    0x712060f050c030604050c0c07030204020f090424150f0509010e1002160503010603121809060308030403020c0414010512030417030a02160302180402190801020301060f1e110f030406 80
    0x1040c81031305d20740750086640200c41080f4041c40c00d622034130b4541c2ea4104e240300c006d000720b401144440704103c91806540109a020300709102021840302900601c4641c2c480341c0d80c0e500005000450801090100e14010461907110348603c0011100183c445820120036103040100c90710b1900e6407034448414071404012960020400903954181544010035180c002c1c6001ea85007030000c10124007100130000804c030b5241004840c01c420801019003814080e04144002800c0c08000000c0080c1b0400861061340a03909481c00041e1000422003510362200140c002500b40d03400500241c03401d84801103c40f0804012240b070140c1d40c0f071901d04000307085c501000031500082034501e00280c040c8112001514003a840c2000a420340e07002508042d1449131000c00d00e140080060115204c080c0044034401c0040594026284c0c0c42c51074a001c4e40c800d024100019005100040209000b00030419408014460856100b085558101c07483e403c60300c41084e0038810103002000110303042c401040540001e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 104046834 1250 104045584 104045587
    0x418170306041802030c04020f0f03040c03030305010501030c0c17281b031d0a05061c0f0605063001031a160f0c05010b0a0801050f060d050712060f050c 67
    0x2020400c001c6420000c00e5011940b8243c100c680141d03808078000a50b03e0040b140143c86030382d100581009805400e40010b8006000800d00040c044815100b0040b01d100365814002c5a807900011004c0c1c3d03d0b80020b9101186546281d00700240401c904445d82c0c0c0c0c41c114290303007040c80c0024800c60703030b1150074000d034880400c440b10419400d5000701208014415049038244605042e64010f0500701e500c1c1018041072010700b180c0049030381d0141c00000600f8001c01940d1281040542907401c1c1d0303480600c030b107942460003540b103004040780e02541c011500001d14103800c01600c00004569902a0a1400c00075203950440b05514640b80001c24061400b0301015a00826460041c54010034085c1101104020a49040001c02e0307100c2050700000e480340c6003821400025180c41ea0160003844003560b8810040c00c400b00b09410158840f620429880003004c86030f4031081e042c840b01c1d038203c000142503a04648801c0c0f21442c86c09103a403010700c1c824900040d00d1290040d4000885606545041d4141c0d030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 104048084 1250 104046834 104046841
    0x1218010b0a0e01090c0306050303120703090803040302031308010c05040501080604091406040c14060a0f02070f090c12060302010203070206071103030403030809010e0f072c0115090603051504181703 87
    0x418800c8028407405ca007410401c16081500095803400f1395503c65440401400c00240d025110350040044258461012912410035140c0030752240c00c0b000c02c031000140346020008904805004071148890f0a032511441c09040000464006000808294100c1e480c0c0e0f15030780000d0751521603400a003c04c031000d0034850900b031406046800c1241e014054604010311307003004540d60306007190090724403400d14213950700070650168180a00c5901c03103170b0030003411040000c1c501c1a0790006d00b0041180c1c1e488801c044489800f050031254940400390040e4810700019006051000040105500449001c5100c0000100181c41c40c0d01c9034200300e00244510040c40828207090107540b0101c49000b004c7c14024803101c5c00b142e40c541c1640f0500701c0c8031040d6546420b0600c2081c10060403070f480c0c00c100044640c0c5411403940020b400305070a02c0000c0843c0c1d0f0006045220b03108850040b000040c1901d001280300f02000041d0080100080041c0451140b0a0000b004581c0e506410340107030425139228613 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 104049334 1250 104048084 104048099
    0x30509030304090e0d02030a0e041a0907030e010b0105030c0403060b0a2d0e04020d030305130204050103110f060a0801060c03030e01020c0c01030608030c0c060c0307020306070c12051218010b0a0e01 87
    0x45c08041d5041d0340c0103014580c041c0790402c401e0340d000c420581d40010900210005440540c0100c130889800c00c0960003806261540740d0071040c0c00034240d2009028810002c4011113070303440100c440d450800d00510050000403040e03002034404090082555447c25143d11030807910300a04050a601100c05c44c2542c032481e450211071500816000e0142456898190040f400d400030b0481d00030700300359651002909000c0c03030301840d20308160040c0c000c010968480ca4140034251400b40c0541c030420621420344180e2a15400311100c420f561303501d0681d142d180c08001e80b1408070105c812406e02da240d030144099a03400344003524919140c0402010081052800034089444542010a80d81c200f0001201080400658004452001d80358190345100b00d000741c0d4251301401c60000e501d0b0280390b052000a6030b000c413000002e18046e11500a040070203c00660b19445070b4421043c07101508000a82c000e802409900d07140c21030000042010000b0400084410240ba00445d203200c500000510944 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 104050584 1250 104049334 104049343
    0x60406030c0f1e0303051b010609060b040503010509010203040f0f020a050409080a0e01050c0a030c020a0e010e0702120a0906110708161415070213090501021605060f0601050313030509030304090e 86
    0x603040d0f00030050a58400400740c1c0704007040150400000c0d5031031807a400003540408018001e1980c1004102e071103240c6a205540203100c2d040c481e40c2030402286400c48184200c0c2e015607801980d031a8241d1032a540c020f02c4c0c40c809182030340e10100c05480001d007600c8034050721a080c4d1045000035598940c1c007030081c003825680c1584604003d014400c00030b00d1000003d5001007183c04d4108071004c14018170006013003281903004020044600c0c000000c00c46040c84032540280340c990269200c15140e080410750901030754a0080015500c4030082104502500303034840d0346141101903480041d2140505407034007003a054038007c41d0300303c0503080110401e00b00410031880300c200c90108810405214040a40c0110100030380f2466001c00903820080e0598000450554844020354544c03407401080c10308049610001c0d01c1a005010011b51106c0710446880e03c20601619030358190b0303c4460100c0ca06a016120840a200d420880f061003540c0801c090001041100000f0403a15031103102103051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 104051834 1250 104050584 104050619
    0x1611150a0305090601030c2102040608030403050d0e06070201050a17010e15040905030f0a0c0f030503010f14030d0e010201090606140a1508010302010c0f0803070804110d0305070b060406030c0f 85
    0x81d80043c1c4c0180002004402d0b8402100c41c502401c4140c03003c48080c051203201000402980a49403c1c0000f40f2828044040c1c4102c0303000e0010b4607003641070346034140d03410f2201c0b40d2400d910035800c200500c01580101c0151901401a00d0900100001c4485c01918040207030440c00c40c0000000c10001c0c0b20101841200c80120705581c01e12400c1710503540e4580c2c03402100030321401d43c034021904090303051050b2848411039402c1604441045258140500203074002e0080310950900c94101048604680c02c4403840000003400511021002d007a0844da01d60450b0080e03030440d500e80c41400081246030180501400d40c0030b4000728500d1550041010a80c5940d0044440005003409038400c150880c24050450341c0a0a18021200e19440d06c910414583c000042580307034080300740400281c0c0800d43d58820b6104401402c00c0c40344440030010508000d4100500042042040100042c10280004e404c0b0303401510220f05140c0380e13600c5011404154024040d540d031b09c07003c10401030b1403407101c1821 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 104053084 1250 104051834 104051851
    0x200a05100209090f06030309030a0c0e070c02060a08060613031410090f0308040615060c020a0f081e01020903061303030b0901032a0b0f0a03060504111611150a0305 72
    0x5410045400b00d105100001c0a134032900a40314000b84441c0c42c1071080300c145e039800805403400d035519440d03d080c88420324000e018401003032074001400c050080b5a4441080d8004011070b0519102d00c3d412904001d0051010340c1008003400316020341091100034201545c031401841ca181c00690035642e02e0b0000c100c0144075883d05110700080420700e908841145680c040c80c1074041a5100e04012010b40900b00c0c01c024081c1460030006160766000004400320382c8201c601d08503013a03591241c1c585020060007002000d03000201c0000001030308041704211802858000760620320400c1c0040c1c02c080c41245c80e008000c0c4145200d200705540741c46400304020045400500765415502d90111142d1881c40025281011109a00540103110300c2c50000f04100381469560380144c003002402a08051640340101b8100640490a0300e030502555003440100e6031980d0070724548111003e40014040000c1d12411030003440940300313071035283c0118024620500150f543c0c03400300700010202d4200500014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 104054334 1250 104053084 104053087
    0x1020c0d08100524091905010210110d020a02071517090102030f07110c0909101a060a031e0204090510060c02010c021009050315070f050403051c200a051002 69
    0x46141c0c1c03000d942c4607640c00da001d2000013104500701341c1090741c81488a01540300c180503200441661006480e07105480080c0d086d54003141030101c0c0d0109507034104804406290301488129126101d541c007400c5a00840d1044a0f42c042d40e4000d0300c00250a00c004020000351000d02a0802c07081b450b860a41009400000318034610703000c1c40c40d11602c1d00180511081000b06030660302d191404114484804400501503031003401d0190340306550318482c1c0e0850307500e036040c0705140603000303403001e130001030f00f0000340c803282c42d0001d19201100180034040c1611044110000b60744640c4800b0310191014207400e0400080e01c0c103200c0c0b2803909491aa0f0300000420215191080040c0d921400010b1450341c16200306802840300c6506841c000f55607080260544101e40c80c5281400c4003a51190040607242c80e069000c40050030100c489104500018150b6400700009061006203000b4003e003000c03061410541c2407220001c07030f420b1484c60300d14401042c1c0c01000b9907014800c0a03c041540940280001c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 104055584 1250 104054334 104054339
    0x301050105060c0c060f120a0603060c030603051f02130b03040c0b09030c150f070605040c0e070912051e250f05060d02160c0f080328090801020c0d0810 67
    0xa903944e075040e45a94003e036004104490068107000c1982c91050004420440d0b034079000100d50000c4c9a1803100341e8940d414250303d103a00601921485080e242c0002c050308200f02c14042211552000840c070800950782088a030000080008009010b0300c07062820998a040a082c0340030064180d4105011040b810050a44a41d0300007440005498058406481400740c10104100d503010782409140c10b003400203a011700704031541d032140f4442c900c0f071091000215101c0401d074050203000c60b282008113510b40310601071804030700190100700b4841c40450f10046040303502045104215100c1644c240d00805c2d100c10000b40c2040c00406a51618075180c405920700149400001e44a10405d0b00031000000c07032045a840c680c040740c00c0180005031400b5007101502e01143d00140a00c52848a01c804c0540030807400300100440d102d410442041c810398004410f240260134200c0c524140900000c5030000424a500380042c0c03c40c0da5030800600040076403d940500a080001c0c8400b00170000e940c001e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 104056834 1250 104055584 104055607
    0x7030212180703080c07030201080108030903030301030312022502010f0201050c03010504021617030103051603080f0d0b030607020601060306051c030804050a0b1504060801050f010303081302130506030105010506 93
    0x11584088500c40804440280710142030034081540c00140411000160100c41e00c9000542034088078804c0c0c0c0c0d055110781e82d5070002c0b41c43e4041e051a01754142c00c100010000302e0b100346094515400e550301700514002d14143c031021000c41d22008810081190f208030002d642e0401c54101280308140000c2c8802c0c640000351100300c0c030050007071070f00c2241c0c0802c0c1c200c0070440b11001104101e41c0b01150001c104854400128650803d103c02c840512076005039641240c1c4803400402184c3d80982c0c5036040c40520b003240d2049070842541c0300c0185559401c502900e0fa02001040d0060b4401e40281941d0b50401000406560854020724050380201617200303915a100b03000031889540514012003162038034504141004000b0201800b401802414400d80a185028070380c40e8610458080002c1075851510500742c0750304940605440001900410129004442441c1e000c100032004038105002a400203c411a41c02e4100c200b150356a000c00c0035a042c24030950b809028100c030440e09190b0300541 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 104058084 1250 104056834 104056867
    0x10203010306052202090414070b030901091b0f0506300402030c01030b030c060a1103030c0d0c090e0411040e0f010203060901170d140d06060503090d0e0f04051308030702060708070302 81
    0x20003040d840c6032042c07641c0c23001014401e4002900c40c02c01440d0340c1c0d0502000c440c0c081c00c0090001d4840d94172403a10640143c064040010859070f6140b0003c0340940781200300a02d60300708582c49070200592880c424002d0880f00b5000c4541d40360003070180c80d0f50601d801410b00d8042d500c04000c1c149894244d10031000c0c0c0d00000c17001d99141003212169556420070704112580403070003940b5041440b0120500003d4040030006e403001d0040860700700580c030b0a10f201242c42d26004c2c80391250b03042105021802280448030034020000c0e010304045200c8000e91000307443c0c40305600700046240d5022041c010a07140c6210454010045800003503921304c0b14281054880207802d8600090010204010785d0012014003035444114207801304100ca181e54034000b0b0407580c0119140c0c030030b0340a0b0744144090f02e40985a10a41c86401030b141020328a43d0a0a210007450050685100750583d181c0c0b240001d4001d000440c032038109640901000d00f090350004d0314010700584600141070040c404814200812031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 104059334 1250 104058084 104058091
    0xb0c130504091407120302010c0503011503020c070305060109020d0b090106050f0d0b0d06050412110705040b0319051e0d0c061e0e0303090c01050c07090203041401020301030605220209 81
    0x1e4000950141c2c0c1d241003051080744440318841802201c40c0001e0f5441c0385420400424001c0d00240503050100d0030803202840240284890b980300f50109550041c8240d0190030b807000140100d4546584030b4403064903200099101c0c49126400060b082a500c21501440c18200410f0b581e080195040c207102a00a00945641c3e000166010030144003916007070300702c0d00d40c4100291003140440c500e810400c010381400c440998202040760440c41c09644034240603062041e010000c0c040d600c0c20441000080c0412220030769041c4518401c3c0c0404200f00640c00c840b180c42107006080c0703a2455280300c06904441e1310004200d42003481180c111580180304141a1980000300146450034a10a41010005a28450600c514100c1c91090592000004600800d144403c440c03020072640e004481e82e1054030400d080340d400c1110200a9043e4540246800502c160b8544444034901402d0508a8200741d0040d6410741d00e070386c01d00c100083e10040161a0320a001074071034503500c413600070039030003203016 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 104060584 1250 104059334 104059339
    0x20306010611100c0e0405091603080d150b090103050105011701030f17030a060303201b0109051e01030b0105250212070f0806010807180b030a0602070f0b0c1305 71
    0x142c050750b6101d00103100794124070329072280401c080128150010103a032502d09109025910300000300d2080c1400003100006030040d884401d080390f04503510007046030060000c0c5180aa111016800b100f0100e05410000e00080a150b81c1c40700d01180c00107041d00c0040e48154184420006204445a0b0a01c40c0505480d08001c10801c1002146020032a030b10040000703010005001c424007551030076a401900072a4044d646214940c59070a200312451203210046e161940d01081805040c40328502030046819014140300d800c03541d40d000401d002860050807650094605a42800716681500c10000c0d605400e00e80f040c10b12050710060070b0b110200b2103242d080b04020404920465481240b400c81d03185624064581e09a0f40d0001850742d203d05000e0200c0074045c290000c141944001030300d40846912020000d90104040c4070300c0020002455030380d4060048d1011100811380d03a000400283e8407511500450749410300f0000400c1001038441c18100d14200820740c0e0103da68403a0070b090b10800c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 104061834 1250 104060584 104060597
    0xb2e090213150e030f12160f0b01060f030c0807050403020f0d0204060807140303070b1f050306070e011b0201050d0c05040509010b1b0303091b040e2b0305040203060106 74
    0xa0089201d00d0300d0055002494802d04034400304109980400d0700103440350140c0844888081103409503403100451011448102d1052181c5c003030507103032001042e84150044e4000a20140f86403202401158240c0044022808400c903c1d060b82d0740c11312419031032841d28074000190b0f0070070b480001c069100300d02c0040c0c07141036440f403a450760359100c00c00c19995070b038018402c002d2103a80315003180d140d42c5c41f44200c01b07920000c00c0c521005c6c0d08001c400c035010554002024039265032480200b03030124200000e442500b9500c8013010071907840401c05a030080900b6161000d03405e515000040031446105122114903802548090050360443c0c191078240710201800700e00720441482c100e8090040e980902d40c072100c00e40001032401d148a0003406511519990a0b900300c007156802c40d528842a103400c1c8055110b03c8500e154680a80102c42e001c0034001d2000c103001c80801181e0b032901190001c0341814024019011600741c1c144038890140c0412803c06000d286801e40009856100500c16070f010b00c0311 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 104063084 1250 104061834 104061847
    0x11060609041b080c010e03060c1204170c0102030105040501170607050306131b020607080c0d05060609100201060503070914160212040f050a0509010b030703110d06030b2e0902 77
    0xa28000200700d5800341000e8101090ba2644035641d140030208203580850240b06c1800714508010800c01d10601d0826017446c60401140c0c42e01900390001041514461144880090030320b04042c001c084000e50320002603180d504040c01c02c42247c4042c0e00c045039009a03500954200b640100e40307907500018904050752665501030103d80100b6021004044540c50803044207080060007454640c80381c02c035800c90340250394000041d2a110410780d010240050103000708170000d0790b42d40200b6408136000d01080c0c10442e0180c00702c1c00c0e80c101b4103e0007001d81d440781403d21880c141000080000c10811200b849081c02c000020a54803002408241e01c40d000e854100000c28000c00407144038004007040203542c1e958801030031b1503060046c0913a5200d0848400005200d02e840d10046050340c1c00e02201510b5521034280540090240b095500522030041c043c0c000340490030700c941130082d40250b248841030300d40f00300c40c5810b00564041c4032815054a02030542201c4100c407070340d4103075a04200f0041c0e80300d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 104064334 1250 104063084 104063093
    0x105090f092505060c0307120305091903030609181505160c050312100e1b0307050d110c01060e0a020a0c080d060b0406120b04090302030d0f020408060403021501061106060904 77
    0x7895a003200390055030000c5d0400c01804d00000400e03003940644c4000182d0454003a003181503c10640320940d8030740c05419142102d10b9880c81c5800f10782d105c0d00300060141e60300d280b80d0081c0c5005074410f42801d40740c50a55014410203030014030f40d40c07420f18010401450801c9440051a8581c6106010020101152410000c0820450b102034240c130310003160b1071501c80008441c41300240038500d812140b03400072820007450041d01203040700303440030513600b540d0b139a0000b241c60740c11000f50004180c3d282e171504107104c0c1c40c031030042501c035001c8000822010f040c51021080c4410161a454800e0b20401c50705030080d40c81981e1035205a80244080c1d9610289400c110181403290000c0c04010390005000074819040300f010410184032081c14000c514220007007208a4545a4000e0b001d170f0000c00c100303507000744198807070f0345864019400103081c580c4a10b24145442c030100c6045025900003440c0f81c0c02000e240707a01c1401401d07a031030a0014184100c00b116198140502071134041c508a401103020130 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 104065584 1250 104064334 104064403
    0x90305040513020301030203150103031d010201020714010209010221090d0311071d0c0a0e04021e0d02030106110703030f03020d0605120c040f0209011b0203160306050105090f09 78
    0x6260090150501000c920b0903000251300c00c0c80100e11a00c92001290000704070f016605040b240c15848082c0e941c0d03082680d0700e002d41c100c912100d046550810121000420140e400d2164a40035800161100519400a4505003181d9400058000f040402c2034002d035600080f80e840c0c00050b14244501103140c0380030342d01c0a0155483c0b0b6400c3c0a04440494802e00e10340561803c18000b0700704801c952101081c02c812072055540503400910070542806440c02c1a40090020000c40f41142940c4030200c00100c1072a000b000c3c01c3d040340e40e000001000306d1a407250300c400001d4401c10144c107000d841c41d03030b0113880e417982e406d0510181900402e803080714a00c40d520000c020900a0000300c1d583c03c2c40500581c4400c3e210803402d10462820001d4025a0742d58800d60f016440180c580d944101e00140c042c0800c01d5045130101c1e40352155441c070381400700721100c603140114070409004c1601d50400781084501d903801451030a403240441c04104d008440002c614101c4036408044200b2a2103601d51107000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 104066834 1250 104065584 104065589
    0x20307050607080c0c10020a02120f0a140c06040b0301180204030f030816090f03080309032118010c1205040f020a080f010b0a0501020607050d0609090305071103011e09030504 77
    0x3100c0802c0507014080e560008100c400010b000ba142140124410041084000c85400006a0018510b24010708045c500c01026016a50844404040c2e50309020726007801d88500701c3d0861080d94005204030b000b0000130111010881d41c182c103090506040014501051282e9031606415181d002452501d55040b40c0103940c2218900c4424071082c10003500c4840e0545071000714045080200407103a2059a101c0140d030341c05402c89401034035644420005400103050402180410030810a4900c82030520303044101400700f000c2d406203000d041d400d00140100c41300c09070a0f41002144011194003508408241e1441180000d290311a420500194813210310020b400484000021803c003034000b5640141d031042100074003e800062040c0b01c1d2000c2141f041602603480500030950381e40c011800b810b05e0b1880303103000041082e90b40203200240c6205110075000f00700001034841c24004d04070211908200207800030300081110804035200038804020b401d61055483c4002ca04240c0304600700c900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 104068084 1250 104066834 104066839
    0x3011a03030304031232101a0c01020906190f020307030503010510020c04050c040513181106160c050103050c13092319140702100207020f1801080f0c061602030705 72
    0x2030090840190070603510041d814080600261b00044220580361012025580c65507041015000c080c088043d00f41c000c0c03000310700c155400384005d80b0951a103401510400c1042c0340c402e0b200d0590503038080c1c145a11000b20f4021034000300448030100741c028041b2411110b00303035014220001418412800e20400980c4158014185814410001114000b40066800c210344020102811500303600483e0102012018020901001c05020038021041c041020202501c1c1900c1c02e082c0c4041d481340d0b003003001c1044400e824005024042541d0612a4560100301012142e1a20030320808081d040c5409100304480c0685540900000d25001c250040150741002030403042d900704032000e40415030190036a00d142a150800c2140450364a1002900607c15034000d0b041d01d45140300b070000a5885281c050b070b00039281c11043e02080c0c40d2040f10322500d00d0181c45450031541002951030a04d181d411000240d0360003058824165903c440484070b425400c1020f1014140319440401e0030b0102c01da120a5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 104069334 1250 104068084 104068121
    0xa0b04230610050102160608012c0c030405060609011202100201020c030f1b1204032d030201020a02071406040504052e140103020301030b06190312050903011a030303040312 76
    0xa14003140188510a49a09800340c5404008150341e03180300c85804c2c400c487c006420200108160044250b41e5103c40d8a60705071076200c1040c802d10456420320079542d600844900008010910809014468102c041129200c029514020305c81c0e2a080321140b001c0c2c880c01004035910503590003541140c1100060005581c1ca40351603920f000c5454001d51110824400741580c0903a10036004941c04055a0607040c005050a0450b00c03800c215210b0301a0000725110300d2503000303101d80078100d0140b030031500c6039001503554501107000904084071903005e0080740f0760f031042e4068166580c2050b030781607400541d000a188e0f0b80c0c441d00b544030130000451114401c803400c101800380d200c4410900741600d01c11270040c500f091800c40114201e1109100240c02c90700c0303103030125419141c0b1402d41c02540591010944c101900c03030303c0725110401c000903180041000010a981241428050502140000310700c001c244031008001c02d4891000420041c2040501c1d0307484030441c5805e600ca4a86e22016000c1c25 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 104070584 1250 104069334 104069341
    0x2160c120b010801020309030f0706110409020405010e03060403140a0201140c07051c1422060509190308090d031b0507090b04020702010e0103111e070606080a0b042306 74
    0x600031034015006840c2518140c00201c0e5105050084034000c0a98600561031312010b41c54000442e004614202d581980304d81036000c82c0482540038201400d211000180c0d40c5180c00005030074140c5117140a406900480200301c046508951440e49203101240900d540c0e1800410481c0140407149150000c030204c0030501070545408000f51038003901c01c00031078a185081100d841e5814440150b840d001580e0030b041c0c1c100454481000c0c1c8003048003041100514090402ca0b405090122340080002440c08104c5000b03a06c0c0040d80a6003280849061146160950f21801054880c40b240030703015030590320b00301c0201031181d182e101c65130541e45000011401c1c54984039490b0f81c05031050540329411305032194094607240c4200d684080c2d05854031807134200b114005402401403003203a40d0811209001d40b50082e01002642140c80c400b002242e0fa5851542c6009000c6522a400084d000c2c0d101100d910000b0706220081c5400580203001c80100c0c825442c0382212443c01134031030070307444c3c0500b00a2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 104071834 1250 104070584 104070599
    0xf10020d39020f0a030f030f050d020d0902040b010908070317040f06020105040605061008180c060a020f010c05030103170906040308070303090201030c02060603100522030f030b06090904020402160c 87
    0x8040682c401c9489207518403280007004a0221240000307441d0450590700d02000034099920500c640c0058204a414076070180042402c0384c01403806505d0380c0c1c1e281d4034004110310b403038402c11140705403d091070038405040c12415592041e00d130000600006a8030255a09106d900741924000c0000003440e4224580790140280602410b650480340e1a0810020460f14540b00703010b1013911a007a0344403041907441d13614a5034031741400c110030b0300180501003140c0c00740d4464100910030310182d6001080307902d40582c001400c50720040710840c2007007001d100500000d05480c024040c00818000083d0b150500b5400080f85413045500c011702c0d107000064034504140e0187c11070324016000b48c904000c0540705170026611344804503115036040d0015006100315160341e901c0260410604d0134003c9040840c04094028400c0424059000c24040108e8003185503041c010101c1d01001506c0e950b08040707441010035206600075000922441e0003143d407050350ba1611840e44003880d044003ca00301c96948054 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 104073084 1250 104071834 104071937
    0x1104090e010f0e030a080105040c0e01030209120615120d02061812030114040c1e11010b0d06141003020a0b0c0a020901030b1b07080d051e0f060f10020d 67
    0x3414007141b101070000035a40340c240304002181900d6101c0c0590350b600e0000440c0254840082c00c0d60011001c0300c20f0364010700420900384544100e80c3c00740440c10130b50382001828604004240161391040321501103013980800d00a4228501c144682c21000052038680d0400841c800c1c42c40c44c42d0004400011a080e04404040e8844825038040000140032603017281e003210781c07070203006503c58940c82900841d0700c20714854503000c0280000154006c075020000d07080c3c600390070050b02c100c0e440c0c0c03100041441c02c180301d0760f400c290100c1c0c081c2c044628550120b084078000d0320945220324404114003c400c4410311070200080c0d0b00504007845580c40303241440440c801034840828a8400140210604c4100c004580c80281c00900c1d141c01e24103204880405418010702400703501004481103215825400f80581c01460040110f0402d481c145092043d8207903c2003140344604048403c0380d070340c01d03000300310301642c140b15160040643d0f9140030495202c81e0100340e010746450300c49450f4482c000846c00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 104074334 1250 104073084 104073097
    0x5031b031f061d0f010b0309010204031e1407030507030b10050405090106030308340e06030403091d06010c060b01051b01020909070311030f071b050c090a1104090e010f0e03 76
    0x9820f5440481184403c82d0044030441c0e034446016051001404800c0f900c0e030240d81c2c03103c6003200140c6000c0d2a5940e01700502400c40140c0c6218081d84a070608003c1d58200d4507030409407400040a401c1d281d92281380d03440555100103040d41400d00007260411540d40c03100c0d0050321000e0424400d0303007401d0a080740200f80c1448243c0c0001c0760b4001040c841a0300f1901030140541c51580741e89000c05c0799103061000c580e6040d8550510811054140303044d141c00d00a141314a0103600d030052614948901e10130903a2000c0c0320072024412141c20042c40340c1e0403070001500a50010000100e070074145006841a106803e8415044800519445941c4005400900170703a41d00b5101c05000d03848440e4103a0984401100490b0301107005d00c00202c203032201103503065000f082c51070700080288603030750014403070004114180c416411000d58100a8103103c40c195400c4400114204400c4040f0340550040d8000e5010b800003a44c2c03140e141c40c190007401d400800c04110700700410462904100e02080d42c1e035003c0e8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 104075584 1250 104074334 104074349
    0xa0237140d050c030904020f0405040606090e0609130609020102160803041d01030c0b0706060306060e01240f0320030903090118030b150613030507060210020405031b031f06 76
    0x5010781d08100707214005903a550400c1400071414080e4150801c4080d410500309500b00031018400016982d8a03401303442e008204a03100d10510504154030b000b0200340c0101168007440c0f2450030721181c0044c1041e04030401d60006000922500d09100413424404410103001842c1080c0708080388800c408402041102c03046500e00c410144040c0310b080c1d0b200000d10000d420f58004250030401100110010240f0b50300c1150001040c1d516035035140200d88080d0000704401070aa8018000303031b055500d40d0b401c01c00c98820f048d00c0c0c995142d94010000c0000100d400200f40c0c540b00d2281401c101c000381d03a0010500300002a03100e02d444000b15599821000d00180000c0c0c0d454070710100e03505141c040d0003e494010030300101c01c1d030340d04180003001c2c2440b060040d0040b000308100d20243c40803081160141d0712a0f8050024585083c80c001e00d41406492000d180d07501c100401c00c529900002c02103019a1025221603030380b00c2207000031b0300f003000c4803c3d07000e542d0000503003c024412840d407007841502c441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 104076834 1250 104075584 104075593
    0xf12030601180e041b0b031608060f0f041d060903070308071407060c0507020d060501050a0504061d04050f060f06010215150108060307050409080d0605060a023714 72
    0x3681c02c40c4598503a600c5081c500500000114001c5200c00386500048079064400c0c40610b0b580351180714160340112201c040244540e507840b007403581d1000c02c154000a084441d4000b101e5500d00240c0300f8a5065072140c03080d980c1c0c200b070300c100d04580b030f14024174500c9590950720b00b4941051101d4483d404401c044000600c80000681064012081d58031204030b100c413441c0c1020707039580d20301c1c0c020721020041d8070034000706100c0031b00165a030054150410348a54000b189651422041c407115285641009210741e00301a0300b0f02042003031240b2054220085160b2010540302e41c01c011342000899032240f10540102c0c0100074902803260503140c002c403400e03421600540c80c42d1104d50181282601c035070100a0860300d080c3c0081d84180c880c503800c100002c0c00e40300e40f166508002000c07100c86110480b075420001c82c1603082c00c079061040a004000c1910040c2c03900040d601b009448801369810620018a124240c9545030448000c00b5950150f01d00c0c0030002c0c0245091005a5140404d250000b81c410f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 104078084 1250 104076834 104076857
    0xb0a060507060b040e0d030b0a03080301120c09050c07060b06040b03011203090b18090403120c0201060509090c0f01050307110303040602030a0b0f1005090301090c0605190906050d050402030f12030601 88
    0xf068402c00c0c441001c00405010000c1b10403100301d0107001480d500c90383c049030301e41c1e022002c1860307900190b0003007040084a00d101c030410300c0c203811500c2c103a5100281240c604001c22200700140d00072903503119807090300007500f02d0880380083c03014000d40e044062074440100000c14400c002c180c515003064043e032100c04a0076070750240d240d482d02c2556820011020341d204801c50707600b086900c0c0340d041031007424020028041c8500602c1101c0f00300c0d0702100180e44648081119013005074080d0b030000c44c241c4c00381c030000b103042c5d0100391141c0404200c6070400c000000001c0843d48289281451480ca510669580342414200400a03400658901e980c0394034100b0460110b03d0f0100d10b030345500b140a04205280109010b041c1e40c50707000502c90903055500d40f18201c001602c608242409004140c80d000c0d112114a03141041030410002c8070001d1040c4074030240840740d0004140c0307035480c013560703804183c0c0d43d41c61011908040c030380304140340c0d184194184a5030011145000d140f0072070080ea1421070004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 104079334 1250 104078084 104078089
    0x902031603020a0e04020105070506190e0705090c03070207090c0e010f030b031b2214070804082215200309060304060c02030417060619081f0b0a060507060b 69
    0xc029220095100840080401600c455008101d900c5401410013030704110654540506051080320070810724203001c03407031a920030028418000b40003040300081695900306804108520405413000203207000110020350b15600c20010700c405048504e0701070094582140c0d01410307455039180742c030340800c40302030394500450b100344200c3e51040c2004000f015502040c101c1200e002c0034202403203410500b1402e0410152450390000c21958200ea040007400340341520b160200c2c0640904a5010881e00b5018040402c640406980d031040c58030301001c100040c10100d001840c0c42c1d660115007030303265580003804030903044018a0f0100303811050107030340101c00701d21042d2640302c0c803012554408414000b090214ad0705074451900c2180c2c40c01203a252a03101c80c0284100d4181c809807624940c00700040000341e061070322840c0952501d40d503080002c1414080c030030780c075074003198010400080c1d101c20071403e400284c0c2242c40010006850b2040f10380d10b80b070f40180b0540c8035080c2074402d04d0910818005a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 104080584 1250 104079334 104079373
    0x7060813030e041a15030a0c0503040b0403110727060b0408070e130c08030a0f02060f0c0d150b09040b09090a0201050d092003010e0111090112061503090203 69
    0x3140d00d0350b21503145107240300030000100001c0c001d180c541412000340400079142d184460607a00c080c110b44503103e1804000c540251550040b405d03042240a01c144000100240000c0f90401d504d810540e06030351188401034640000d9500c00c1d8846a14a15001018009021002503142142105100c0ea6480e088528803a1060b840354221541c030070402041034017503400c095078002c841c01710f5481708442c10703490380c014100780b64012803c140c1000440070041a0850620401c1150500242c4a5407030320315500d60f000340004011002c01140081e404500036003c0c2d104500841002c03803801545915030074081c00304d070005120680038914003400040c0f14a028403083d13104420380c1e40100343c0301d155a07004450903042107880003802500c4094400026280c0c80074515044da410788840d60401031501094251000b82c408403c56034548aa905402d20780d100407204844000c0c20481c4c03061166101d00d800400b200c7d840000150501c0c140c0c5441c943d4580c022103000e9000701d086800d0700001c40d20303070000b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 104081834 1250 104080584 104080621
    0x16020105090c0a0b1b010c02300a0c140a03030605130e06130311011107020f0409120e032a030105010f0609060f030b040c0305010305060c0403172a070608 68
    0x40d83d1090304000d84a03156006101083e9140c0a285125a40407145425518071001d20005070b04903a181030404c4a01009100f10041000c0c507148c8a8001d680700d500303e504c0f40c030b050b107820406c15420100074440e001d1041420040103000f202c82014050500400910041c02900e1151185004035080012940200c01c0040510f0021301002c2e22030350400961804101d10450501c5452a625541e044080c070644104501108100340e0303c0304103104010700484c8001c0301a124510b4811a40302003803000c01400544111070415100111b13442002900e0840280e51020041c890148100c91408410040c03c0031014181d001380216602c915002c2d43d118094080c0d80000750a00300100101441401264400002400d00094020003100800c050350100d00f2104007217502c03000100100301041152a03030111580c03401c40c0c04c15044d07540e0400c40008070f0505603c0d611011031800901c48407440d054480c00c107103c010300741c0c000c01a5020382d02c40c100e030b1259101044000001030700034804011000716 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 104083084 1250 104081834 104081839
    0xb160c020603180a05060901240b0d1a040908180103020406020d050304080f030108030306010e01020607051606020d02070b1e060109031202010b0405071d0d0305120c07060516020105090c 82
    0x1150b49149441483e0040444180c1ca02d100d50140304020a5050001c1800368001c4000030400c0780382100300500003c0c002c41051407040d54400d08120700c42603003043d01c444040d87d600100714072030950250340c440c110802a6951040c6003d801100300030f0084010200b10390000503840e50004440015000c0b8001c512504000d03070071079011614064070582c019580580310707805903402d1804100307501082c1d030001d8000b4600c60f4000410b00000d581c00c00240c6c0c1140c1001d10082c1218074000000900c1409414200741d0085540390b00c0100b0402c4640685840c100f025108540350040740c00e208604032400e0b00c1c5801c42d000c4203202041d90f000b540ca1110300c50304040c1c6400d6070701491a92400302d40720a41c1656811035582ea19030740129592070040c280a01c84960301c1400742c2070314241460303441c141d020700c0b11b01c80e030444244a0f0000750800142d80d80305012508080199075040140b54003482448402811540307400100100c050350307032103000c1c24020356034002c1066a5070022010743c0c901110402d075a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 104084334 1250 104083084 104083087
    0x605060301120f031103160b1b1603050403020301050702010204030209090f0607270b0a030e0f060402061303170403150b0f090604110c01271101050306010e06070b160c0206 76
    0x41c081454144504a42482071900101c10711650105c83d00310b80040a002200c4041101582c051201307030143c003a040318180d0001c0d0a19510340504408610800b04140c000d00c02c4140c0f920203242c01780050380e00954014000748103d141c4240c00038000d43c81800128030800076130000c030b00000400241d000c83c103041c0400038019a1240c0304195006403000d00b2240c4510a000e88660f41012580305401c001c0011003502a1072f603070041c4010b02550190003200ea0f080d03100c9aa0700040310000100c2c90f400c1901600c140e9a00c0c840a20000042c00c040c3e04050300300381c8224200c1d000c03003103400001d0044900070030030307201a40b2001405034281e0340c07940c00042d40403400c82040061407401803a15900030000400c0041c0c0668840b460f1b0403a50400c0700104070700e95440c007219481528001d4040c143c0d9031100c0c400107241805039130744181600c141d03103142d0400402100049072039008608841c2a00001014180c42d40300c1c1d40ba01030081603003201d52440003241090580803480c018940c0c1080103500a0459 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 104085584 1250 104084334 104084369
    0x6020607180e1305010c020d080a150b09120f2a0612150d0f0c06020606010c0305030903120a150602070609050d0215030702030c010510050a03030f0e0301060602100605060301 77
    0x102d2500e60058512411906100000d0300000d000f44200c0801e0b485c00e4000c1c0405564545d40541508801040100264145240e8411030f064162500080e00c9142d0304807912200c800001c140d04141b41c200403480f512510004652101001850300d01c242500c111b00190b110915019002d00e09030110802e030414028170066002c00300151100b54003e10215007940c01008420010345200b19515084d501c0700c0d8140410b4080c40124100c4a0161889000800c903604002c000246582c2c081c503409401c0140c08404204e03070003800c0c8100c540c5500f120700311300460700300202c8440040031a005c0030740c08005505000140540040f402c04100c0d0450340300c0001292400003070000304240e01404070b90020028120401004902000c1c60046090364021519490780ea11b549085a0003e0122050f414601001308415600c040c0d00400342c950620381344100c141c1d2800280c54585444a800b40c0c95400d103c40810220b41c0007a105440e40b00004040c0300744ca985005000c010300c02805404a24050624803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 104086834 1250 104085584 104085599
    0x405062d0601030c0c050d0e01120b0d08030414070312080708011406130302030703080309070603020c19050c0a0e0901060b1608030402031e0a060b040b01081f08070b03010602060718 80
    0xb00c000200941003880b9113240c41d40d00c81d424007e01c00800804150031200c072586550340001049940e000f0300c44104070045403200041c491046550004050080010024040094403080000c0d000521001c40d003146880c0d242000803010b001c018400001c150000003220b00740319001c1c26040740c13881040c144100110300c0a00a40e9400084112108144080000300580b400c0108000440c010590030b500ca007085c101c403600b09021a80884201401407041c030007810f10100c1c21b035902030142583e04034220078a1928074140761001600650000d16400f0000304210f0101025114506c103000800501d919200103141d6400b402060340c812030160701c0342000041c514001150020300043c200c0c6c0801000c900d401c0c0b80c0d80c0c600840c007125500300d071021104002d41d9020304142d900080b2000d000000c5410002081000d009000c40e440c0c1d041c030300b01d0100c81e60082e521580542805001d95425544910300341d103e540c400e1203040700501c602d000007040c240c803036280d0304e0709015100000b0096030b280072031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 104088084 1250 104086834 104086841
    0x309100b0603060d030f140d05100503060f152d09010501020706020c0d1b03030504050f0108010b1806160f0209060a0b070b071404030501090b10081f02120405062d060103 75
    0x4880b400d02006001c80390081547d04094a4840c100314000315042c509120701255511050348550b000768025400d1100c5c0300c81120b48980e101403c0703032000720480460341c00120005416121a37290480c2c014040550000c1c40c0d96031800c1303c2041e509500ea03070340c0c0c0d68012a07507907110348138140050f0000140a4004d1a044d5a42da1400d4002c9011070350021580610042d62000c2e9030086020480005082016081c00e12125000038400d0828141e00d40c0340c03440c0c202c003a109030031400e60f00d24451105009580e032401c041da100d6040c22aa003804090091914840f0303841402020381c810400b23040007034250f18110710744005507030a00802a040640c82e6644541c0b420000c1c0c90030040c85010519064a4200d48000c0c0006500a034000b184050360f5060030804880b01400340c842040030720800744408200000c207a1880c405004070f2144d5500e8a9012034000d0084003c501003008076081480244100060700c0b502994003100202d509518040000744540c01d414901341d40d1018140010749a503000c3d03403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 104089334 1250 104088084 104088107
    0x60106090603150504050c0703080109060501080a0903112d0105041a092b08060909070b1e070501060501021005060d0204111606020a090503010b0a26030309100b0603060d03 76
    0x1807002d103d07034540000509550b01180c0141900a010038924280350b44402c41c24010806440b0030080f046c2003e00003042c2d9040200121a45500c400c1c41d0b8040601c0760160b80e800c030300d205c02514600300c0d401400c110043c903c4100340240300328010310b14040314818440c95000b03580c0700540511441e20301c40040202c0c000100700340e03454001d81c01068121112010b094003034101c010307004e86d07240700c40c59005050410080e18a5019505c484200510508002801000e8031440f000490300d90b41d00004542c60300282c002c0046403100c020030740c43c0c10004150050348c156142602540e843c0c102840401c411a2070486040e98028200c1c019503001d0b0800d6030000082451001c1d00c189450f6901d01807101020640c40101c07451580002d90300203c0364041103000180408800134444800c1c140002a4180c2990117140980ca00c0c2950b10500c861003e4003011900800500b03032600c82c5881000e03180c03549040c10700e031305015042c40c955511526008045038400d03040104144080c03403094030110783c40380454 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 104090584 1250 104089334 104089361
    0x12020909030d090302060a1b09030818031b12030a080f040f06090f0302011a0d0b060105071211070906030503032a070f0c051807030b1503010b030a0e060106090603 72
    0x400030840300c2400d600900e96484c0c0250002d000608004c0c104508403031503a01034504c0c01d1000400c0300b441592151079181140d410441c2540c540100740f03d42c0c9925402542c01550610176078505d8220380d03002140700da0280c0e40c11a40a9035000441254a0b16442400b184000140318000001c51001511034001d40003802004030a007904026507464007129141c00054070164500c024010401d6824007550221402d264489404500034202050800c02e110300010710040b82c1c1d500159076640304005903811a50040e107040f46004c0d140074040d0900c1d415200320034081c001c00c200407a00c602c0f00d003d080f04072980640118603649d2000c01c5900b50091001d0036000e6041c4d040715030014a030514014050140c018048007601001c141ba001020b000d0030b41c0254021403150b0014007001e0043c081c1e50794800a0703802c0102d01e89403040c000075940343e59008141ca4145d0701100208a00003420701440c82484601c008012001803072848580c3d4200c244610000224080010701030b07140b09801c01c04005000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 104091834 1250 104090584 104090587
    0x30f0607120c12050109051005030730170301080106051921021215130302030912030702040504061d12030105150f0a2c01090e07120e070f060305011202090903 70
    0x20f0505445003079000d0a001da440310b040c007008444a00241b4001d1400314000e245c11850110b240c0341c06206407651040c4965150f83c60400c1d04030100c8514452948030740d41d9080704d00c250144600031381007800b40c1d03041e96207805404582c1c0d00348101d007150009485852070030010300d003555080c031803c3c0e508421101e209801c8003190040c2c481507a50030240102802810942c81044030380444128010540f000500c85200c480000c00d2700801200e106820070341326003521300181c1d16007515610032032000a41040c580000c00c424051141d02c0401c0047c10860a00080d9868050103903646100e40c644113414201000104420302e8020012310300540d0580c00c290825200b4201541300e84c100408031804074801a030061038035000800d8540350b0007080e41403483d801d002c0e080002c0c84015540500b092004054000c41c078660700541c0d0028900f0340c011010f01092802c414001d403184154814840c503c1e0082d003004c101c0901a001d0075060f500b01e5030300480c0001441c0c0810000001c00303414561217000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 104093084 1250 104091834 104091857
    0xd0903030e010e100f0626120a0203030f070c0201020723030a080d050c030408070b1b030a0911030114160c020306010e0118020708160311011802030f0607120c 70
    0x1428020000300c3c00c0084090045254132400c101c041e0381c910031305200140c0c170382501030003100100000982080380c010100003c2c4410140c1031450b002000403104480c2c14085000100340e64000000c47c4101c2ca4810f200c1180e440d400c0341603404d5400d4400081c05a0421a4280306980030a45440c54404401e242100b401b0800310200e42000f00d0702c1400c0c0c0d0501c00000d405d01c8001c88500545401c00c514003052895803030103071aa081103005090000304070542d01c0c4007040c851502c00455054130515841100d54038101290140014240101d0489407004095030b03460451030103208219403003182c1503206260759140e60110b40c1c220510f415003414043ca410100026032010000340f8060000b02c7c81c103040c0355040060200000010010075040d2900400c45080042e880d003042e6040c4100b42070b804580300241b450b041c0d800620399400311120350328041040f48000c00f8030910170056030098080c0c4404940c401c01454607044100c50600c04242c1d504203e02d02200103500203500c4807407502d003d010b00300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 104094334 1250 104093084 104093111
    0x40b04060f03210c0302100c02030906040e090706053c030702030a08010f060c15060510030b01110a38070503070f0207030c060311070614071206030201050d090303 72
    0x3403960010fa0b21110340c24506202400c510b1040320702001c20703050845180e400c65030000e541e11280340c03c040e0b500e6198907e00603114000c0050703450103c002082d19894640b1601441c56003d0100c9100010f4483c40c40000b03561405042202c4440b0303804600080303a002c1e020000c01139003000482c200d041138104150360fa841d007040e0002c1e5000340c007140d0146a607101c0d9040000d00c2d0b00f2040c0c100140200150030708102c0f464001002800d051ba01c01c4e240560712041d40c00e0800201102d43c41a90030036145840703012481e50640c0809207808090300c82d00c1c25040c0c903025059403180e0060005280200c000e410300e2071424100301d03a245415516849000c2840041014168903909580c20f0010600210902c0403042c0c20601c40b145416980c4018410a46151112135a0080c00e1150109260780c80d034118020b00308283c101c1d40c0540e042141840b4207041d07182594040b000848940e80020030000c90014983c00500510003101e405942d4582000031301c1d9003000c000c04204000718280b580e107648148217030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 104095584 1250 104094334 104094359
    0x30408010c0908060f010f060305060f130c02010c08040f02010809031903061403030a080105060d0902060708070303060b0a080606090d0203012318190215030c03091c020c040b0406 79
    0x1c00703903101c8940501d04184140340003009045280c48a42c0d00c80140200040944100c04a5426280114003915010082001d08100340e2009070407400c03c0d4010794580300305030081d20031904079a008001d01440004101c64002007a50010724074950035440d400950320891a403900304080c0d2040e6440c010b400b8080220f9030864082c60000b10b503c0744400c110014580802582404c000d50107545003c030540001041d4020500410703100e21800701e50a01005d102d81e1114420355070240c101580c502d81820030030241e4012450840c0060f04122002c165402c041080e26503040f410303280d0b04140c2e01c40d0402c12090b070f00f2002ca50741e013021b020001c0d030740903a809011b6810085880f921044450714103507080915181c0080110362600c01c4c04441100d094000110104c400d50b1804083d20451510710004107003401d000c1c104400e00300b0100034000811140c0000b1802800c450b01200c404040d940b480c2803103400c0c014808005070300a49030000d41401d182c0c100000d101c0e0300400000721962140e030400c151 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 104096834 1250 104095584 104095601
    0x302040f0e07120209030a1704050d111002030406020a110d02090a02071709010f0c08121f05010912030c050a120f020f0f1c140703031a18060d020303040801 69
    0x71014540074840065004804054420743d00e410075032a1000c10000302c0c1ea0790b1101440140803107203040d82c001003100c0070820f8401806000f08504034061850600c0d43e90b01c2a00f07100d151040360126130f054845400001164110b401d65000b824007000f464031008041d08407040303000d0300034043d45000001030b942c00c0d040501c5001e00100050b100da409081c070301c081119a0100c500200000c00200c4810713a084074170600303da9494502004e82800e64546441a4015146008045424002440601410b03c40381d17070f0544641e0a13840040d80d5440c801100c00300034521800000b160407a0301d100c04130b48107120b007070741040c0610301319404150641c1d1502d9400030200e1035080041c4000e0000410a40d0500c0006e82c0b840da490f00915104d01c07413901c01500c0c0c600c1141c00c41d1240c03488040031005103001e10b609080c1d005060810139110700240c10094050100f190209003142000c04003810340f85001d902e42014503141c10304200840d03031202d0a000c2540354442c02a81d040c8420f1000180660090089094 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 104098084 1250 104096834 104096849
    0x50319020f0d05070c05061b07150b120a08040510050c0601030503030a0f020c030f03040f14060105210d11012714120d151706070e190e070302040f 65
    0x82e507018100c80301007160f0b4080c10103010080c4216207900031480019526800940b04803a050078580d402000c14060701c41c4120050140c140f11003074440e40242da60150348108000d4a0b91000e900050a04c19110708003050002c11600041c841400a030406c0c014100400c40d00b400d02c0e0b1302d0050b420981d103142000c241c0c4116180e40c030000c00c2101180d5107004121040b00c41003015410001c050380000c1d101c1c0618401c4000b03a41000c8009030034400c00a0390900a10380042d0700d149500c03810703420b4586403c401d00640d0301801200030f201c84000484044964088405e9000d8040c110703010b541101e5aa0080b901d0340c256640b1150f4041406440341c1482c0d01081c0c2010742d03484004410f00d082d00103011310540040190700207403014800c801d200c00c2158000900320b038000880d464040c401c00d03103405098000f140060070320150525290b000007080c80c016142070b11788816019451041009a003601c031003403161815509020403c2c80003205a5540110311828098100754441c2207446c0100c071254820304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 104099334 1250 104098084 104098087
    0xb070501050108100b0d060504080913050121050c010f03110d0203100803030708040311120307030c08060f0a031b09090c0f0603090b01230301110c060c041203050319020f 75
    0x9228200a07100d8001d0340d0a109210400060340000e021014520010700010f0311740c230014080140c1503003142c0c02401c00505101d581128400c1c001d000b0402401207a80c000400400980d44221450311a1a071650000c000e107040d0402c02e004590100c109407001c81410b403242c0341e282200f4011400f6150b080c040410058803890103810003518002d10381d104480da03410030402d010b02c9076070115141c2d5015400d8281400340c5241c4042191910002e01c1510f24440c00103c2030000265050b0009240071a85a07901c80c070382c0d2120010800c41c1c4a260310010741c421224101000003510001069034029481070309454560390b40c01040c0309a8540842c111a1554104020300104560384800800361250745404c1000d4546661141c4055006001d012a400c8406641081003010302c000001d03140400b40092020660f01c00c501c0c4070b00d070065103000c01319000746800a8480d100e03500969044440300c2c229425100c2d6607482c2030740d440d032000d441002200252007545c1c0005401d400100311a01e034442650b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 104100584 1250 104099334 104099339
    0x306150310022104030c06180b0f0609070311040e0f010303080702150105040b0d1b1701050402060306010e010903140a0c05010302190806010e1215061915090b0705010501 75
    0x5424107041180c0344162a206021140000c000016000561500d0030240d581c90f803154102913502e0b0b0a44400240a903080083c00c03881c140c1464031481c0d40f103200300d0307010000e134072142c0ba089200e402c100d075004c5c0c11442940000c0c01c003510036080710b041d00c0a2009032500d019200c04c0311032005482112040c40f0b01c88086e00410401d80d020302c5882c1e0201444c030140800041051507180e21031344c10320656110301c0c1c0312030000c100c99403400a0a040c150340541040d6180b2102170300555080540d100d0035080034090a201003401c0010302880d407140d68010644e902d5545d4510054800c3e000100c030780c1d070400c15100c501200040245040111000344d9900501382d80e0000d2609421444c11500050304040c0180840300400e9144000c0c100c1c200001d081c0f094030341d80e4610049a0381d00c071410300c90b0340c0803100000110000710b0115440f1855a10140000c0d0a0742e180001d000140c070008038180815002c2620400500c0c0d00c0780060034151007103142c1980100ea4030004202d482d00001026222070359100c004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 104101834 1250 104100584 104100589
    0xa050c1c05070e0a0e01050f04022109010f020c0709020d0207050a0503070506070309080706050705090a0906050907050703080a09051507020102030a140105011d0d120216050906061c0b030615 84
    0x940f000f03998101c49000d05141071103503e0a2400061040b58020b09009a00140564039501a02d14188a203a412540717500e08108084100900782c0741c1a1140d46410107000d03880449000b00d0b9883e0b40c111001349446860304410b02c1c000d5003c0c03400e10688030b07803d01c80a00080d00501001c041c0324001c0d40155101c259605110b07003072140c0900444281484c081043c00052003100960b918a42c10980010385542e41c81800d49140c0305269419500136040c07000030500d00e003e540720380192003090f03600b40ca40c1d9840c540140c5003072107444005808600002c3c00520701890740e80040d0320461054054898442402d02c3c00b143d03440c0c081d48d080025035008020000761502600c07505400140710301f044c207181e500d4640041c10350190001108181040c1d01075001e02911842143c400050703220440760141511050000e44581c0304584102144150850001b050310b07001540c107000303940040906160507071421000c4404014011500b1f2510780b1043c80314030b15070742404136610175080e9501312056407211804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 104103084 1250 104101834 104101847
    0x20a020a03031a0901060804030e1011070b090a05060a020c040903030203090c04060302060a030209031603121d031002070201210204080114150d140102041511150a050c1c0507 77
    0x8050600f00380e4940300014640d201d0090701d04540540c18440080e0b101c0741806ca800d0b1040703592450b08172922003c0f140c0e049a01403a81181030801c0000d40b2641915011402514460080c41980c80f105070b481c20310041c606140200030b00382c0ca90049410804030140460f044d41c031a1b40c01070b030100b0340c00301c00c001c62680d0500c1000e802090440b010850366095600007407450098040d000f04055011a00902d1601c00b004034038a544809110705240381c0e504d1600ca0790902d0302c8542e1070700040000c000c190a001900752001c8030b600004000c1c1a84902038510360009400c00344c010b90402040c40d20110143c0207030312800818880390200981e41d1420301c0c00441c251510320800d100030828110400406840300c58210300c24510403254080006058108041d40d003400c0c82c0000b0183d4400240040d0003034100110780c03804001174130b030307680b40318502010951115405020007459000020002e119845d460b03100682c006508003165060511107040d600741c101080c00c188104560f181d0510421680210 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 104104334 1250 104103084 104103101
    0x2030403030f140406020f0c0a0f02030705010206010810150905090a0201020115030305030f041a09030a08010e010312180902040608010801060f080307061a100c12031b12020d020a020a0303 83
    0x30f0201100d100b281c9069200300400180c0030590120b55503c40c540c615044400000740c00040300c08403907103401c04e030140b5100304004034800c1c03240300c070006015400443c003241201c0c03e005c0600300701c031003001c61f000c05090031003045407144c0300740341d80801d0f15402881914010207000e4010314002115200190850700300e041e03007007020110407608100203641701c401c495010703070304902d10040f030340b11494055100c00041c00501d00b03080406003003180400c40007000e4041f6165955581005076625001a42070300028000907010a080024007a100c41c0121421802142c0b04007100500c6941c2e00c0d4210120b801c96006100059404001000482024024203018100d914031102c074071407500920503500d00c01c1140003003007183c07160503c1000c0005d6481c0e0028906c005410b20603603c45084000342000d820b01400c580340c208044401103001e00c2403003aa6100d28184a03041c0d03600d050403a0540303540c0070001ca02e0060035020050a0003a02050018100c2584030341c00070003504241c2d2030094240d80580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 104105584 1250 104104334 104104361
    0xc0406030b10061404050609063007050306010f050306190906030606050f03070515070606170d020a080a1b05030706060e07050c06010e250e030f030c0601050108130b07030203040303 80
    0x2032100040306a4204c1190121001115605da840000e00702144caa401034101c410030034040c00d101c1404100014400c50411078911311581c0003541c0e00f602c2a203141c00140c40c40ba0002d880d900710310f9000750081d0011034200000078482101080350000350403020071150400c00c41d20b0f0b10780e0810001c0014501650002d01400c80342444400000d03804030340c1c1c030b00c058440c4601c11055800c0421041c0c611400311500c1c1900f150040c0701e200c1d22031f4804c121407000c0d00594590380c840d803881048c8051011602511040d40310007064900700143c03004861084000d0303451105032290360744e03900000702e04000400900d4414100442d03d217140101e68240c4a100402c04418050104201c081d60240400d2090645417014203404058032801e401c1c81001000e02a445604503c114240c0d41c40d0b50000c1d400400d07a07100f207007103941003810340d46a40d072280981c40e20001c0a80c07202006009543c000c0c40895400010307007801904a000d43c2d240c0414080042c0c03804004668004140400d065050240700c06a6052 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 104106834 1250 104105584 104105597
    0xa0e0a030f020c040509101e0c030b1005210603071d0403030b06120a0f021615050c0c070302060c01020f04090c02150103051c051c0b12010902060316020c0406030b1006 74
    0x6c0304031900c45182030b00400c0b007240c5d29a0018418804811090311405103000200701034a40100042d00800781800241c1c4100d00c0c544002082c14442e0b811554600800c580d50314482940312000c190080001c0d0075940d05000d4144042440064081d5010014501030a4900103003002d09002c2d040340c20300c00c1d030385e80681400c2204c6103043d92600c4032560091400180058801c031110703022802030148142c070b41800300e02181008140981c40755840c0020001c3d000801980d1513402007007800d441401a01c9641e5001003004001503d841d00c058181e441c1824005031400c039100e04400c4c425845500407100031650303041000311083e0304000d400404007181e05062000d50642d00e4690b96900304600400e0303844035040e07946035010320031070954084150b00c0c08459021100000d4000107807900850450007030010392410140b1007070500900150300c0d0041c080500c2c50311030b00740f01411100980880800d603c50100503d08586603807003400021030082c40504050701f0804103401c00c40030f01e9805031080100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 104108084 1250 104106834 104106841
    0x3f020d05010f1d070903080c0f010b041802040207060b040203040c0602010c021b090709030611121303170a020906040f03060509060402090711010906060803030403141804050a0e0a030f020c0405 85
    0x2928142190700f4102d901c00074140da140102240c1300302181e00000c2041e040460201d9543e68001441403070001803a00038001e1280390800e010894141c1c1020020000c010311180c2d015050550003001c03581d0040c003002c142141c06001060076648140c40444924109040400c00c00d80d0a224500f4000303140e1016041c0c0b195801d18525403605210b11161185044001140d03089018401d020011503111505010030380c40589003051300c0c0c003c01060040740101d480016216a04030142c00388103949600d4080b00c0c48a540320301306621100030a6001201d0b1301300f01c0c4203640d0744c410000c0d00040204401c0c1845070784c01c40c03400d44d06641010b011000603a00c10303000d2100513681c51a49692090b240d10301341c01340b0756031413013a00e0140c40c401102a000724680320740801c0d5001d01000540c4200e0107504c4590848800e0300e0325590038464400c01e41c44c520824a0010001d1409801444c0c0054290740085030b81000c0c050020f0800c4201441180401e030b850002e106070340d8043c000915225004c0f502003050b0324 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 104109334 1250 104108084 104108099
    0x30f0705150a0504090c1209110109061e080709180b0f0402130501050f0d0e0c0a0503030f030105042a020a0213060b0913091a0a06090b013f020d05010f 67
    0x110300034a42640c0c6c9900003901c0162140e44010041c40e0010720501103101c043c28a10b850140707800d65140007680498001c170b04a40a4041041101072043c2d1a1824032441102180e50301c0024149204101d0242000100c08000d040a004c1c542c402450000d014480c1804014401d00c0602e0f129018600600a01c09050941402d0004030340e8282045540c076251040303046030501ca140e43d01c07110289050540c41070014002074040c6211415117481400756225000c0594900690389103001c2e031101000180058105a0081c0d9414080f20340d05800350351901182c28001001095854016442444034009511f800c0c00c8100340300f44240f500f00320700317030800c00035440c90711511445078000c0c80800390110041d0015071048162940040710340c0200c01c80c0080403030b5040010b0f520848410308090020503c14181e10422403403e00585621503402035624101800c0f03190b2600b10020368071a03004061715102d0340301461001d01024803005965035441c2c0300030404c072041030700900900c1c54044024880c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 104110584 1250 104109334 104109337
    0x510030317040206042303011406090a0905030d020703030b010311040f0608040804051008090d030c30050c1b010203010302030a0f050309030102041502010b12060123030f0705150a05 80
    0x841051140c0980c1d50b07400803e0300361003258841d400d10b0000009502c110303080030302040a001011002880a80f082041c50344c0c00e41c1040d50080d50002481010601c409240c3c0ccc0805240c43c46030781030f41d007440748039a0480104d801150060303020030785940440055690502c20b20200200034585141000e04001c9240c0c05061345004010a02c4410030100d82403180304e00a070307402000000d00d441429030303800c040140503030002d0703c1e034100b18841c24001e481d110b8043c3c021032040795025580d0004c402d05502a84050300701c00700d00140a9480354420840c0c80e0070b00d00440c0d00c0b4010420003a9a104881e1648005500014984403941c4e4418801440103aa01182400030b8030307048405039030312001d80c1c18024118495000e4103945507100103000552200210b444190580040d0002c204500301d01040c4441c500b0b203207814000340d411000040c09407071890b41070b003511a038480d4080d00c1c449800d0000300b45491701910403d01d450740481c0c0d041000d440d0144411a2616003007140301d003404491200030b001c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 104111834 1250 104110584 104110607
    0x3071d1008070f0207030807080901080a18020904031701090506031515060318010c080106030b030a0c0e09070801091b0f0b0a030f090f0b06100203040602030906070c0305030c060a05100303 83
    0xf000300882080e0030780c0b4030070001030700910341001d4203e0b503400c2c0d00d01e46600640d100d162020702040d040030014038186811302c03510244907180002104a64034960800600c0c110041040b0706012400203004d144c20021480c060180041000000380b60911700d04161130810100e03604c1d01001174500401c031500d201082c0c0e28210303c10940d81039840761180580f440342d04518000c00400d5620308042c84c0402c0368000c54090407107a50382c5040080d1001c840c28140c07a1000100041c003c1d0300c0302c8001b0880003144c180341d03552028a10090342e010360b0312400c0482c00c1d140d02541c1070b925040600f500040340e841050b000c0e4020b1001000c0c1e0340101d031400411140e81e0141e40c1401003859903500110344403041c1c94104c0c00c4400c0e40220028850b0310713245040c4a01c40400d035440313030190045d80801d1010038000400c41d4150f450580045050251150400206500030300084030b5400c280340300003000031010030240103c140e00602912240c507002c4003a0b02144d800074110b50185d0740c4604e0801c04650410ba41000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 104113084 1250 104111834 104111837
    0x1060923040b0619080f150108070c0204180c0e070206040506040305090a03140307050129090a0f020a02030a0e010201140105010f0315080c0906030a0b131703071d100807 75
    0x1c1440b203581c0011940c1c0506607008660542c100d03140003501e680100003078442c40158840004540b540202c00c4405101400003e0105000304d000c684c00c01c2c060022002400d100500101d030390a80c0400c00480604000400c440c1003481c1c5030144070f00c0409018075540602d0a100622603481d058071100d50703816019001500b4001d0001d4055140c0c4c4a4006001c05180c001c202e04c0c2c96164101c0d00140d0341c1e4444541510305519000c0201c40480000d4541c2d41d0202c00344443c2ca140000717401c200000302001600b01d44480381d0724850b01e020f080c030300d0007e45907400740c5401454686108100c054060307407006c42243e0443e403420481a252954910400c1c0c1035540a01e040c03891000c07880e00a1300141201002c1c00340b00807a292000030818070000e070301072034820103503000c0080d0b849400074181e460a5440d8004c0450030f040b00001c0c016225130b0818036545014030b10114401100c1c600f64041c1c0c0d401600e403200040c150280e0950980705d540d400c44a22001981d81c0d00e20b020603400010045400500081c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 104114334 1250 104113084 104113091
    0x3040b041d22052506020c090403080114010201020403050a0f0b0901050606031612050103050304091401081b18040f0c081c080a0b031516080103050d0e06041205060106092304 77
    0x505000f002c00150b01c400c6000011504403020105203400103090b140700300300043c0315200b4112542d00b0074110041c0071310f43c580c41d03910240c0d08141c6c1c081484401d00c0309903811907500f84000408503c04203d40511f0768024400b040d014495801c101411040c028541800c982c10442403050a480b6441103d40c072070241c0042c0b501242c8100811180d01c290180ca0000c01d80c1000e002101740032003c80100201c6d0424030040040004502081000c0700c0f092107030300138542208184840706034000c003c8918103080141080241441c050a50b80c2428090f10f094403401c507070388442410014044000005441c120000302406013031410100c011800b040d625400300910000071a001c1c0c90145c1080109000084c10b8410380424200c80340700c00c0c441110004003000c2013203182c1a03203c1c0a400c03568181c9402801504c0141a604010b8810148000c8200d410141c200000600c0340e410410000c0e100344a600a0301443d450420000c2c41102d0941041e03003407401d18a41032162000107558060380010030b44020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 104115584 1250 104114334 104114401
    0x903070f0b0703120b040903121a0a0b0d020c0d0e01031805030307210c030f05060a03050334050102070c0504020a051209010905060f040b0709120b09070803040b041d 73
    0x15014100503260039400908000c247c1c020543c10100c105802818500c0c1000f40003821208540c0300358022803296080f070f2480f0001c2c00303188408030040c0515995818054601412a0b0000746800c1c440b01550000034846044030205603414003901c03503000010882e0004089150300d506481c0d01c0050550741c10b1103104215850b0032089160042c0c01d1102083e4200019400040f020b0b000e0213041c1c7c2000c494074035200c00201e907490601c03152003d5035000002542004103101c0d903410380c040880b162156800a44000907502000381d442c3e0341c4114441e20015844000d145080000c41c03106800c6940310b07074010b00c0301c103401d56413040680705e40c1d1071980101c3c0c02540380c022a00340100070307100000e0a940110402c10052000000d40207001d00c0c458030540e00b6030345d90b01c841200c00c1c4081c0e0003200c171424800340040740465000e00303a1303a8103c195101a124415070f21500300d03156a01c20b0b4403d5110380700201d0b013041050300c4000c1c100b40414040240d03015515003d1000320038843c1c44010364000200c046002d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 104116834 1250 104115584 104115617
    0x2060103080d0c140a021509070e0103080f190504030302010e070b0d0b010c0c060504050a27020304050f070303030c120608250e0f0a060503010e060414120d020903070f0b0703 77
    0x2c4000b07131210b04009594840300d40300020740310100340300720405a04108000c101105000030b012030441742000080c0381c07981d09541d5480d003598811a0003404090341400005c1e12050010301c140f101c00c465481e419a501e00d1450040d082d21801f02e10340d0b5080d0043d5208101420b03040c0c0440b20030a51010002441d03410369401070b2440403940710040c120610200303000c43d945801100810958038109d401800c0650b41c1c2e058003585034881000d4500c00f2400e4800d00c000c00f031140d00a1070f0881d100b4402c1d944800000426145001419030040d00000e4880d40390310038040e00f01c80c62002c0c0000c540030500210b030400d000103a6a03d0181c0310f240700c00388031944211a56071f00d030000e01c000d0000040414a10300748000741c80406d40080d0b07149400549000c5002941d464144501d24803146a000030300240d6842d40c1381d41c01458402c0c48050264000c0001c0040c074081104000c0034034000c800c0700140c480c44079000345840e00744d05030840c800745681a1011f015680050050f40d041d00d50500c1c0404050221048 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 104118084 1250 104116834 104116847
    0x705070507230a08030a0e0607020907080f130b06100207120c09060b03191104051306090c020c030703080d06050d060f0f0209060a0503040609021c0308010602060103080d0c 76
    0x540940603101c008501001c5141001c0240700041d000210103010500400000321028460b60a0552080180031049800780c01d00d450f01800c018200380c149070854000c00c0c04010104c40c40c4000a003003e04200f10784090901d09d54000301050b511003480d032a9503584204010b0041c01ca0352040c40e441a031007100c50710803c215409024030a02031072000c200f034038100b0505a030b6801440704642c10b24001094429020050701d00c54900030351904031a02c03c20260100600e1400c0c4140004ca40410000c1044d07200c1c1205940e140c03400c0f403000a40e440c0f402c00c048003119030090410045400100500d01955400103a503c1500d8100100917920480b52002c0402880140e0013243c00c2843e500814060101d150f00c6024080400501445800004801c4104a00c201740030b45601400a202110515115002465105218400014148520b07400084030051070341c0d68251500142d001d0001015841062a40109551f00040800394115039414946008170040b240a40d99514008001e8510645 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 104119334 1250 104118084 104118097
    0x201080a06030c08060f15060406050702040e030f0c120f0912010608060109020406020f0705012a06051614070b0604091b06050c01060f080c060f040f0e0106080a0216020105030705 79
    0x20210b80e135141e04068481c0700440b8282e00792000500010100c5414070300d00320150b10b0040c0024540344c00c0060036606a0421901aa009035882c5500410700d18100700424040c040c181505896000b9200001d180c086001e040c01d894220078407801e860301c0f030410700703035a4103020495146800c860510281c0d070042040340c0c0040710511aa800000e4081031950050050314090360941c0c55480d41d0000a40d640c640d14424140040e4902281584541d8880301c40044010500809405620b0b42e84513074007554000d940c20005441e1240b60380b148242c10600c15050940040210703410310300350b038803040301c6d1142c0100007600994039521080700304104402040821513141b8001401c06403501c8004102d9040078481a040b503203494800300b0110118201c010440711400003c00b03402c2d00072024842d80390042419080907180601011503150110051803000c0c1140c096200300c0c540c54100c0080418402811000d1240c4c41008080d1203410880b030b912404035020b091a5607252500f42080b1020311400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 104120584 1250 104119334 104119343
    0x304020d0c09090b01050108040c030201140c010504150c0f08060907030e0604030305040b01051504230307060e010e04091505090c0d05011d0111031503010b130902040f180201080a0603 81
    0xc1c80800c80e1509503100d8407095004440c04011680c0b54401910008401c2d03030003803d80409040200015841040c000504000c08000a81015013890042d8291482034070f049031101104c000003410100e0610405800b4045c40c40d1840c0341e000f2002c4042c00c1c01d000a4851402011210700082c58103019402c60072070b149104d01107070160326050400030000c10060350202d920304100000044c0919062520f04511540c00000c1890585040305e02691444400c070403a0801800400b16400360b9003c0c485d02000342030985401c4014410b8000040803a9a24102079200d0713441d060400c0081140080607000300e0502d0b10000400c0d440300c0400d203242120421013a540a840130b5904010000190003a410012186404036a07a0030f03500901420703182c0001180c440d0410620025168002140c0d00c20040c010190001465030002000300746c1900411a100420645840c200b90850410344542e109015124070b0400c52041551083c0060801100001c0e040001070800300b5401e601603440800150f170311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 104121834 1250 104120584 104120603
    0x703020705090408090f040605060d02090406121b050108071d0d02040501171207020102150c040504020310050306060a03020f0d03050405030f01090302060a2307050c07060e0a1a03010b0304020d 85
    0x62420740c44c0c6034071003140c280c0a10162400c440c5507080500941c0140c410080110303003801d10036943d81000390400d2a2940c6d004d5102c03100003900080e810300031801640142c00120701510380700c2c2c0500d41007031650700140c1040024070400600503880700e4241042162000c0e1001481482c90001d404400c40d900069841032174200009489000c407060340d51101c0f241e8003074030304510a1000c90390031800b4078000030340917803c000c80a80c140c03c01480e03041d5000c1c0c403503007059003450303250004242260400c031004c1031414208141841540b50400007103900401c102c5450010506550101e00020340e000a078902501c60800c10804040c040c8003510052b18020301141da40e901f41c20f449078042e08280000394050f005502c082046844103024100d51940d0380c500420055462510561504900915003400c01505100c050580b00017440311100521560b9a28001808001308002c2001c2d42c0c5d0f03110815184140c2820401c11707003400b058904642c026151a61030307a403203001052010340c0841005280902 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 104123084 1250 104121834 104121841
    0x81e01060f030b0f060706020306150c03043b07031e0b0405010f080601050f04020d240b040f0e10030f120905060412020409110d0c0503101e02070302070509 69
    0x5005100006401c00c5541c148406040035040c418580940c008072500020700b084a1004618990001c43d04078002510302c03e24002c507221003141036048a07044001c0760b00000f4040103092120b9040104000b801c80404c00c1500e4008107481d8a4003001040c20040400703100060841c0c0c0c001d07801040f803d0800c0e0b13610b124607010700540720000e0640390503507032140d46000e001041c2d48108401e178000f681c840c040100410717400c0c4802c0212078807034421020780c0302d50204020003110500380946250201001c44520b201d09007104805a8546c09802074404480280410414103c1100c182c004940b501d00500000e500e4000003010142c21a4001078074a07150203010204220780c8400c10340c00b482499031a40d904079101e004010842c405e0344200582150101125009464660b0003884000d114034210488041c01001141c02811007001c21340c0c0148680c2420880380c14144440000344103090b20801c500642c0d4004141260a034040d130108913039010402070101030082040c0d001400b030042c0001010314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 104124334 1250 104123084 104123087
    0x30f030a030906050106080402100302030c090618090106021c0c14071d0105012606040f1b0810030b01030b0c0c01020f0712080c0a030e0307060603030807020d0207060807081e0106 79
    0x2c02e0110340c064508400084c80a101d007164034040d41d80100300e41c014488101088020b500042d200d41c485417000c10804a02e56034080c000c20f441d900056581035080c1900b410482070140503480a420b41d0004040c80e0035038100500151841ca055040c840c03800c90060915803540d85c2e0500884000303100c0c40c40d0220740030540d05810390380050410020b4100b0b80c1c9402c01151002c40341000300040f040c0305212140006040741140d94490805800010b07a040d240013006c081d1111280c510303921000d4100c91072802940240c6240c0c0c0080390385040300c281880c40d41c031500e1a481c1484054030001400010070203180b07040c011a03140c2d04114000307540b50409100c46400f29030200004961402803040010250b9001d502c1c0076109104500013a41080d500c00d5054000d00038625046011340801c00c4110b0016120f40325220155000b82d50f170803428903110300c0c081d00c0c00e81405109410b42d40101000c0010301e41c0818003a5204801c4d14001e211603d61006000c6c81d030f00e4802642804402c040c00218200703 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 104125584 1250 104124334 104124341
    0x2010e0721080f0d1d0c03030a080a02071a011d06061204031103030f06010905030a03090b0d0207050709050708010f030c1404140f060316050904020f030f100e060705091e030f030a03 80
    0x41d0200000380402d4000a05843c3c2d1641c111b032030755030543c0062000e81c4140e030040c26080d90110074144003501d030021a07650038074000c40b01c0168070180420540180070031910a038040302c01140d0380d8000b04182c10410006600c1e0f002c1d13100c0c200e1214501038005403c051003911003a41c04a400400c603502ca041902c0c00a20281044505a00094510070005083c0c43c00003101a0500e801d6100d8035001410b106090380d0580c0060090110940c08100c0600043e40400865001703020b200750018190074014001029030b54180d00402c04403141410900c00300719409084c1e03003150210394500120303282c40400308000e009a901d11368403c1c2c91002c10064042500790310a0310400049003a5104084002c0d586030040070107003e200d822080d0f020004006040c08241205003440060840d1884000d40821038035045d200da5a440c1c000c0d859002645914030304004141d00b06009052407400c1000c1003020902ca00c1c0c480706c1c2500d01030144540c448054400703100710001c110045e025aa41d030403016a01030080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 104126834 1250 104125584 104125601
    0x302190512030307020c150703180b0705010b090604020405010504060f0c06050103080702010206070201061a0c0a060c1101060b04140d021206010902120a05010302060708070c0f0306090302010e0721080f0d 90
    0x340c0624002079035945040034544410128000c1f03880d042c514652001ca81940385070b01800c019004c40d070408110381c48040090203946120f03070004940d00c9804d10900010701006003039035000b680180708c14002c5a0700001aa0180d8003903140c09035a10903480012036031415403484c041c0005143c2800802440391820060000034000e0302151501e40300c0c0002242200d0441c0300c1d0107118001c2400c00c0035180314440041001c2c0d0014011550b001c00503841e901d045841c80003260004c905d101c0505440080c00703009030002841440318007400e0520340140c2071802609610b1441c4074088a03c203150840d9241c1c0b42020324020041d0445040d9a10b40b1341c020002e50008103018180b03100703c40050700e01300d03c50040c0c0b41a254094051410103481d6a1500703107503004103004485114059902080d00c1058001d804000d50246d0408a96018541406401c4441c013502c0f402594202a000340301d541807030121404065200b46140c8103055003030410030400d0140b508144980e0740d000810451f1030304250412400f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 104128084 1250 104126834 104126837
    0x90b04050f010e01090e03091002010c1704080a050702030102120c0301050f03060405070e07050d0504050a06060e06030c010e0409020603012309040b0a1503050a030306090501050105040f0302190512030307 90
    0x1950312600c02081c4241d109200c1d129031441104014403101c8440c0d001050090f4100c000c0b2030402e034080380001e100303c85a5401e100141e645900306128154451000d2503822041e841711100c90501d80c4450010b4800c0420050a000d000684201151030940c100c03020300541207059031250030010484100c0d0381c030070310595210307820a03088505685804500303540110751050042c80f2041c9010700707624200100518500602c40e062202c0e42e2102454024103102d03134800e0000c2e181c80c4c940b6242110466803d40c001d039003420f2010f0f0421000307485c0010b000e0003855003404d02500c1d607120680050058070702c00200079040000480001102402c0040100c1003c420700280031600f518801440304080040790302511000e40800407421020803a4004c0006008407100300c2c00700c40c1c1342c1c0ca0712b41c5081004172049000030f99405003046003003102d1048901401003464103915191410034140d00010041c00003a21486c20b04110310800d08880b15231800520018003881e09032160b0710f40c40c80d1240c0040f54100c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 104129334 1250 104128084 104128091
    0xb0c0f010f140a0903030e0307141c0807110f010c0c050c03011103040b0a090b09030315040c0504050111010e07170c04060609090e0c090a0f110304050706081f090b04 73
    0x703008800d80d004041c40c110b0010340d060496610401040050800a08143c05041c0d0314503c009007424144014054503014007442c1c1070107440c607114603140041003065054031031508400c8401030703903210b610190400007500e0700210b10800c000b051800d0030414024000301d58a000c8140f0310a54014900441c0c1d58001e805541000c0b50700020300d400c0e04d20b210b068000a2504100240000b42100c94103a00000841310000d03095840340c1d03500c000d60209455440a40e0701c08002c002c1d01c2040303071204004006c01030b1002e10044091503000750142c00749008040c1400110154640c03482d0702503102c03401e40002c0c041220181e90382c980071612071840c120a00d0310540039801d8490340c1c2d030070507010320707400c03a2820340d10079000900c0c04000c0b200030901605c2d01074aa020b114020240c95440d42c03d01d40c05260560000903041c003040700410304883c20a46040102e4000b401008040b84021955000711030943c20140c009a41c3d8000440818845041d608030303241802c40e000c903a8031110761010b001800d003601c080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 104130584 1250 104129334 104129351
    0x3020c0f0d170606030108030301060f02070f060801031506030201050f0d2003060907020102090f040b0103020d06060504080c0d02060f1b032b0515040b0a05090c090a061107060f090b0c0f01 83
    0x13001d1100b409042040e5108100420160744902c0804d408410a4819518043d4460311140b2140015620507000150800300500a11403080c100d4030001c00c181c2000c100c902c0c910f07030006e8031034000c800075610900b80101c0c0c0401c05200e260000840300c00c1c52048444041c0c03090000100580094074000e00034500c1000080b802401442100c190000081044a030f0500030f00400010302085042c036410181c0a0150010311105400b60300007500c829141e00307440e0b07410080700b40d01c1c081c071084119104172042104035000d62900c4013141c90580c1e01c1203000f5900c40168040d2803100d5481c4407405110704c40003804400c00c201050102d00040e1546110808070004d002180e002d030340003a03618400e0301c000c072001c0d01400d01d130a5200c00d650040141a03010080c1e43c41002460b9620200e9840d603000701c00103410b0002d450021141c802501c0d1074109002d8543c0c0201c061356440006006100030300060300500d112060003a9150802003800810b01555100c580003840c0d01e403101d826200100390700384000b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 104131834 1250 104130584 104130589
    0x603050601091202060a0504170a0201180b12040204090b070e090105010e012705040c120509010c090b070201020114071e0504180b040f0e06040c0506040e0703020c0f0d1706 76
    0x82c41200e200343c0c00480c041035950200b20240d403055070800203220082000280182e8282d00d0060307d103103004090550381d00c036800050920041452a058258000d400030f20240c644882a690150008210040c2c030343e0f102d00c0031400515017500301038116001002040038107075201044240d105000c3d9a99000b0340d984400548490700102c01d1240801c410144042110607111030303601403110742983e1b641c40d00340d0f0b4101180844500c504001c0008201489030b0419151500030386800421403c0200f029810803a002099950790b40158456000e00054076401d580c400d4000300520750002074200c07030a041c6102c019081015044103403040780c41c40043d11100c980217205131070031280d643c3c3c04000120a1080454010074203403a400d617200d9030710a40300e843c00c0c03d64411075070003201d0180105042c0c1000d0902c0c05650944d03511861042004100c00e0004c00c120406194220b045400c025813104011864282031401140d04800c4a204540c0380b480256800300c100303421102036508945082d1100001e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 104133084 1250 104131834 104131847
    0x31107030e0d02032a031b0609060d02070203030f030402100306080622080a05040e09070302010507020f13050f07120e0c120a141b2d010c05030d060603050601 70
    0x401030040741110416030341c18140507080002e16031000f000d44492404501204540380980000500035683d00c0002a90a08080182e115940b40404d41030600e0544040021818418001c5e41805814003040c0400c0c00c4000350180c0b11300d560300805032511030815906090258000700d80c103078400c0b400c0000c1e0b034045500912600b01690161070203411640d54103110854044992010300b100050403100f8507000c114030398050110011155221640c603450440c4040d40c40c0c0c0040e20050080c0c018540c00c200607038000040703641d241da0598030142211b00101c0050300c1e141030000302c415050300700780400c403120402040135403065507035441e142c04051480010004680d81091914125805107000350918500020700308078003a058400c0300c1090031a5562501c252810462120752680800d0404d44611005000100ba010081e2034203408c802d200c451164626404030390600c00e01c007000c4034005569209050208460303800804680e510380303050144c0c2c00200018410a000a880d00c004551150302ca5407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 104134334 1250 104133084 104133097
    0x131e05060a0804020f06130306140609011503090804050310140c09090109020306030304051801081c020a171b060105091812030a1d0c13050c0d050a0209040204030803070311 76
    0x156100b0082d540e03035003800245008803007820f0717204005100c608421101000344001a41c89a00d020a1002e01d1034800f012400025003940c1c03145c8030700700060101c401c4a80c400800010346107030201d021441e9040c41d4040b84581c1e08115058054044600c0031844c2c40d8110a94002d8240c07131241c00e40d80d40711000c458900803a121a58462020740c010400300c40241c0140d50015402001e40346019900c000003001c003164a101c3c08c00e40b10791000100250001448082c44100e005000c042c0215600c0030000d4035822101c1000b0040780b2642016001c211005080d2251000c90020f130a144207003400c4015602d407001d2184e14400c82c030b000c00107052440c49141030821407105000818520719241d00035502c0d43c100404241046541e10502c0300e402000c2115582e61052030300251400f8210302042c0036040106848102e5214101001d115902030000d007220240004400b000516403100c84410001e071040c000d01580c0301e4004200441802080c0000794081c07001f603101006000e40a15001c4140c1c090310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 104135584 1250 104134334 104134337
    0x40b090708190203120703090305010f05040f080309120307030603050c06040803040303051e030103060e0c01020a03120c0507050d03052e0302040b120f01020901020d1106010303050c03131e05060a 86
    0x200000396a0b6910700d5080d101440142680c0c0203c0031760b0682c0c445508205810b40001e00314410420a0040c02c2c442d4280c04c41c2d102e0740c140214500381c0c0740c5050500c9200c030010040100040001e01d001030038002d84052660b01010550b90342400c0d03000401603c100e0000340c03040d02070700c038869841c2d2800360100c40c111055140039605151854030203441c00e4016001c074004944103d02d00710185c0d0041402140614401c1c440012060142c2001030b16003000c00380c035203055600c041040c0000c41d400c00c10103000320300040c50100f008100316078100c90038040c2100050a0f84500220280d01e1901500f11398131a461240c50105466000707421803420012041c544440b40313006803000e001500303280d0025400c580024128000210207840400d01e441040103021910b0303580401c41c45003a40e0706005000c0f1080103454814001800304d0101a00c410040c4401030601400080131005520103009a070641400e00c810024038540d40c500403800c4291200804541240d084408a9a880c261040d01c0220026 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 104136690 1106 104135584 104135593
    0x2102011b0804021503100806150f09010b0706050601030e03120601030b01030b062d041401020c0103050c18010203090a08010f0608070303020a171e03040b090708 71
    0x903400e444040000c0301c0c00b4400540e07200341c26101c1c1c1c0d00c00020015a42d03244c0444560505117240d001e1440c9000d000200a400310110941c0d1900c882c099a0400c0c2c00c00b810710401c003403942c2c2400f490000301c00500c165004203040c4d078071407540220103040008002000070400d6240d40c10100c09403c03000325034000c01403607507810f00680c0b070100005e080c00c0c09036140c0517001962034007807002600c081e2413120304180d052072000c9018110f40b4001600341a40da0f5202c0101e81c100c01d964208050140c0304040c041e06040d4071a2007485c0c40348074200348580c18038020340c00989286000002c620304522003401482030b9541e40c0401d038002802c480c000000c00c00080094101610b481e0b9100f000345800004c81080402d8001c20300c2c4540540c480340441c0f046829040b90001401900314690282604540a06050404000440c003d50003202c0c200026901c8414156030388401c2d00415005400 = true := by decide +kernel

theorem cover : BRFrame.Cov 103956834 104136690 := by
  have h0 := BRFrame.cov_init 103956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 103956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 103956834 ≤ n) (h2 : n < 104136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
