-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:45.04682+00:00
-- url     : https://prove2.me/submissions/0273105d-1d3a-4d9b-9bc0-4d4df89e290d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 559532374 ≤ n < 559712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 559533624 1250 559532374 559532377
    0x3030f011502031b120703051b06060d06020a030b03030a0207030515010503031b0a08040608012d12030309050d0f0f03060e060402030402040e010c030f0f140a0903020f01050c040e0a02 81
    0x41c41c00b03400a62078030b132050030352450b100b82004141d0014891001841d1441d0750042c043d0031018420740f20b0b182c4072115100034895103203025502c0b2070140e0203e001c010f019522074001c460240d40000d070040c1c3c0d840540c5011000303400030103002c5800d4400096504076440e03001039508100c0e8058829240d602c4602c14115082005c28030510358194004d000000c50701c03500500140e01005400100c1c0ca400e80c02d6541d00070541c00581c00840400c40c40e800400c910058104844401c03205681c80300c0306000319200c0341d40011801c2c000c05101110902e8643c04040c001e9102c08001500134084a03448501c0c1000103184400c0c1d40364003000200c1e6030040b00c035290b00a001351000e84d441d41c0350402a6995100a00009410040c002c3c0e80c000e8603415040c0c0d8400d03081c8180f9103100c05031303580840c80394100803411050356505040024000e10300110740410509000c1d603682c00260740c0381c0208024009003001c83c546001410981c3d03c6500e005c06000595076410010021101c10701c80000c0b45513541c400381c4049 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 559534874 1250 559533624 559533659
    0x907030b0303090a33091833170618071814010501020307051e16080307020418051504020d080d050106090f03081c091b0e0c07030e371d1311030c100203030f01 70
    0x40d80320720040341c2f0311000f900303a640032050030030100e400e61550341c000000425100345150b501c181c0d1b200002030741e101c4044065405817070300f07000039441d0000640c0c0389a901d8100e42c4062826006030320321403150b0b10061044601c0303000012220400b803a140d89000f9203d510075001244100c0c40c000c0400d100e90302150802280031782140c06003d491840142c008141240100200d92240ca01e5240c00f000a00b0724000c2c107810201003c0001b625810a00b02800d03144ea150070001149010403410800a090203045078030301e01e44204807203446070410307000e040070380382d410030003841c1c600ca546008240d541100c0d5a40106e03011806485065254840c10002c40d1080301c0d00580090090f40d1541c199007481f102a90010f40c0000b14140040c0c0d08442142500d159241c6554106135103500421076808501a0500159003103441101141043e503030000c03050b000090010114000004c06000940d41032010b40c40b2420050110781461150f07140003522a482103500156000c0c2e24000441e1041052088500c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 559536124 1250 559534874 559534919
    0x60503010b090c12250507021e0303070809030313120c0914010501110c0406121505010e19060504020f040e0f060907030b0303090a33091833 62
    0x54014040410301d020103000308400d400c01881c00c151000d0100b45e00042c121510b42d0758a40d40c0f203448900c1000081850100e09a081005e4000c1b81e0351039036404011a0602a031001c4031710b683c2c0c2d50902c0481e0842c0582c513482c6180d844200e00000340340c031507001d601303581500c1036031754070325a540360302038403017101c0c60380d2450290a8640c1c0018440740d4082c1410368100742c01441114000819040082c2c01d8030703c990051240743c00280454002c201c0243c031104020000e190081c003007581001902e40340d50b6001445260b55502c0c11048618484156200d8806080068400e40d40d442e9040605c6140c3c0e40710748540405015044001921148265049409000028060403090700c69030002c0b03024203007000a0350744c0341c0401c1100041559524403080010320201e083c000d55061142c030400c41d41c0d6846001500c4c50101018043d10b05940809124240c031702c01018086c0707003240c440b02000102031003115152026400141d40046858034030f5030520b00381041503103980468840822011084007000c1008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 559537374 1250 559536124 559536127
    0x21504032604090e0a0f11010207050d08070201140c010203090c1e03121b03130e0709030c0626070905040f06060815180c030901140906060d03030b04020706060503010b090c 76
    0x440c415400008a0001081c2103c003001c02c00d448440306103211b42e03030072100e4020245c90301c0c0341035805002c0c15004041c22240c1d907545c521503880d0940c0500c02c00c24028104480c50400b440100060020b503440320748227400071512450301409103a82c80b00c0c030b074004920400e06a600c002da1581040e088142200c80907000e403986e00b070402d14807003080e04403400d2941914441d0040d03030404007041016180013040c07c0c2500302400d15018000c0c0c50740101401807010440c0d059800e2021403c0303201183e0849486141c8140c0e54424541c070104030014014048601e069003800307001d003065200346071005403101242c04011703001c0b880b100303c42118030500c10b040c0840d48940c005854010171107804080309402420b20b9962000c24003015582a07021100c851640c1000310078071501100911a0021019000b0380d17443d90790070080d61442c2c3d1540010815481030f0f2200d12178100b010b1003a088500c18410107402591142c0b494602080034020502441c1e00940c0b0b0003007440018502070450a01590f0096080c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 559538624 1250 559537374 559537379
    0xe090a030806060405102a170a030207060203010909030806030f070e0408190512090601060e3703030210151502010618051509160c0c03021504032604 66
    0x1d560000000300000d0303015105000000d40c0c1e0301c1d0394258030241d100e00e0780c503200314180004881c641c010400700c40014195120300d01c08006074550b110f1030840da4001120b40d031901d445001c100d01034803c00a0040407140084000602540581c20881c101c503c03984407407000c2c0d41c6000c18142c1d81c1102c00008801070380916400c020b2401408501074001d40550421498450900060101100d50300005000030f8400030b4800044e0b440112026000103200014003d5540b42040040c200c50340e25185501c074040210b100d1089a06d6190038a003800302403c0709483e06150400004105210303444140c015029118010761011018414106049501950407190034140b01010140c0742443d0420000d541d07031268082482850202c0d148010801c05501207120f242c11500c6800400c030741c10900780034052802c288120004050818401d502003403801c401e4181081c101410120701581c800b0350440c410141001c20002c01200510580b40282c0d0150700c0e071190000b0307180c550801003055a04403401488103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 559539874 1250 559538624 559538627
    0x4151a011d09061e0405010b1306030e28061b1704170c0a1a0709060203090a06030209030102040302041d1c08040303110d020c10050705090603180a0b100905010e090a03 74
    0x4200d50030b424410200c284c012030f44041021a03200f03030400c40c4010400315100c3d145d901c441020314041e00c968607090191015000d4041c0e66032550401d400503051000d03175124040c1c0701c0385c284030701001e811050600503a0109440003240010320303500303180000c0d40403c1c102d010b03070b42c41c900d05401070b40e110201c2a0404854a0003501c29041541241203a000da512406d0214400003141000542c01d520015214205001d000d4030954403684045e06642051010001640e50740305010200c444070b040140c0e480540c40d000034024850790300029030162602e241c440d2022440810b4101d018244030440f1029089128a1002001c45000803400508000c00090000344660003100001c034001c1561030406112040410698102514080180d40080c145980300211402180e40040150400d503250000c0ca001003026488014404503c5845110008041e00e02c10030443d0601500041a400d03a410048109070035540c0d54411281280d081c00c3c008195400d25081d0355000b202e9080080a03100c41e650340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 559541124 1250 559539874 559539889
    0x5040207050312070e240306090901060b070501060f0b070f1203060f03030507020a0f081018080a080109060b090603041b0e01080102120a05130201050304151a011d0906 74
    0x100300d641e400184035540e2942000b110150280c44039880d10301d407076880328003407140e41549213144903010b08152260ba40c4401c0c010044a80044007038500f0344c000d035141803c41d40984204c0d405150f020000060407810b01006502071426284804ca1441d0340680d40e10340801c0038041e555026110003110030004002440e542010440c00e4624100482c6896032040c4007e800c0c20319500540106034000350050452404045c10b00c003400c002654091765a0400003d02d641c0d000389020700102a0342c40d00340500385039000c1c0742d141c021684800130b140e803a0b24200c0010100c4a00b0320603018030508144012903500b0600f404c0c1c449654003d8005030556849443d5610300c08542641d00c1c014018201002c51040700241c070f01401f03441d061002507a0f8900050240b45030f6007000341802050352500050000480c4811010000c82d602403038411780320385882c1402c821554610300e241625501d27100c0c0042c075000e207240c213411415400b42c03a14010342d01490380d0300704102d00000305079510160b0300c0001041d605e8030b00e8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 559542374 1250 559541124 559541137
    0xb0405012408040f020406060314070306150e1906020c120a020f13020c0a03030b01110601080a03180b030a0617061e18010213050321030106201009150204030c050402 73
    0x12081c1300300e0b40c0a40100e006ca03403051f004080040d4507090f121302c4280194000603004101c4e0310b400c005c0207152101d02c100140412004004100901c407036080203945a0812500c50304400754408010b60740c03018007030754490036451154014200c0c900c6075454404082940251290007415001c01c203591001000308a503145880c0ea1462135081c0012882100c04200b0100300601c2610001250341c0c40ca4005400c58030614490515644803c00603c06440c0c085503204000f0313070600707112a0320000b60103013607107800d2250030010100380040100b10100110b07801c2030044070442e03814600201c0007550400e4507500102d1354848001e02003420300b1107a82d840881c6560215507210700d100c5042844c0019820790344600554042d60740b2400060000786001c1c0080c1d815104480c04035003200000c0001212a070105100380418070240b00318090040000032050010200c1c51000e41d00040c0c0c2280b00d081c010f142006c02500c8207440f1940465200040c4d01c00c882c1640d40003031703203103001924000400c0040c2d440308 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 559543624 1250 559542374 559542383
    0x106082b080c030621010f0501270c1b030f140921070503010c11010b0d030c0b0604090c030b160302030108030d02161a07110c0604050d0201020a050609010b040501240804 75
    0x4c0d414500810750880d11851310070004000400c031101d044e41c7c0350050f118182c100010107850380d2165100020301d1840c41108400010340840c50110b84001038621704803080e00c0060580000e460b0004040d0303c20740900100240b80c85820000f00c0142c0c101446006002100360422011440340800a90441038911075000b00805c540145480d580400d0940d04141d04c80c80200d4030340207120803012002e01030250141e00661318040803400070385004004451189020b05120901004159070352a6604541e05d4940c10404940143c1e03500e00d481c24000c0000c6a40102c0051402044c0c200188240212812104490020750400603000d5580c4020350184622289903205d01c0f04010029405074800014141907651080c03c0d46882c1d81d000d40f14000031005011140c0101403850201e0341d502c010344094800560300303541010000e10060b803400700210006400352084004000d0200313815000b240c68060103031014032887e61380c0c0d03c00c4000001c1100a0301c03040c444401070001c407107200d4100340d540913008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 559544874 1250 559543624 559543639
    0x3040317060301090510020a02010621080304080702040c08040b06010206090709110405040f02070507120c0b0c24180606100f09120807230705040b0409050106082b080c0306 76
    0x41c0e171014901007921041000c0d80f42c0104d42c0200494080c81140c3c014404c81c1030750100c001d51140001e40444540000801c02c0b4008004101484006402d8410061b40079104100107540100b014200303da0803241110071502c000b0010300c0b036520100388907014014180041004900701000e0b1000741c10001c1c0d176540401c0040c0800540c030340d114052901c1701b40c426013006035210780c9810403604105094010000184000c40604002580919400101c0f0002524580c917050702d8401c260611100240d80301c4000380740000c000c0c4050820b00a00c0c0202d21040f049a00707d041100142e44400d01250340d1644210140c64043d1400d01030381c800035110400346444e00310faa031628213410307080035001d200381c0f0011008101001040313031608507020300c010b441102041100075000d600c0da98000d2401143d0017680c8454120340311703454a07004505029403140080c042c00b900ca07406240d0350340e80a44060b007100c651903503104110301035902581c40945643d03910500c0e550f43d0000048194400b51009802005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 559546124 1250 559544874 559544891
    0x1031e0506040b040b07020f030901181e08010e01290316030b040303180f060c0e150310140a1e0504051e010b1306081317031b03040317060301 63
    0x201072007072a11a42c0700f00351029443c2860f0500c5646800c00034010803c0d548201c5900400110000030388003182000d2070640b211441115004003040d000d64003140b004108007016028004c158004541602d0b0320b04000c210110107038102d1420f03121484c110b610500a207a09000984070300780c403018090200902100c00d400000c000c0c20b05000c100741c2c0243c414100031828401055494050100080c0c160001c60381000101d480d51907400440010041c0402d6440340c0012600e401250b400c0040d0f000284220041d0f1b20b81300c41e000c401e6004980e11b03060036050325404201e8855049103080d8044000c0c00d00b8410a050290810038160328843c11401c803006030340c00150540d11402424400c100483d070220800400184080a002c0d06801002030038000380412119042080d44c44170807100d02e0701d0810903c0d1551100000411070346803018001e814441411103500d908a00118080d00300421000083e10307500d1100708850100750b40040014000d401404620f0400f110000d400c2074008000041110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 559547374 1250 559546124 559546133
    0x70510020a1407110a1707120b2e06020f0115030f02090a020c030f071101080403051903020c03040602060105010f0c080a0807030e010e1e0a05030306270c03010e011d01031e 76
    0x180c49038000c440d00202e404080382a000c0a1005000802c024170411060301c030140c2d1002e41c4800010110410710084194003d40000b449c02c0c0c0c49074403080c40c00ea40ac2c50351707141d00b4029225110141c0030265903007480e00c8520050042c4080384126600b2034803020b80318046900700700d075501c00605600c0c0c002e43c00b482054040d50003440281224a5102e580640d10401468070082c19542030020a042c014030900b0800031070b03040400c0700d03403184004002c0c0c401e00180e41416002801400300600881c8804600840c280e0b0b000551039059407000d80f41d03104c8601003030b4000c9a910120b500002c122709014001e0300c44c000c2c0034180030b0b80c10074030500740403485d004906030090031a99162801c0700168007244071240100000c145021a413003484024244101903a01c4040d039070300c800744c505c1d40901214001041114004900c0b00340002c080074001e00181420030814034540c01c00c4c0101d07801c80c0550340001880403c015100180b501c0d0a660541c056840c2d03403103401c8140324404000020020602c441d00018 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 559548624 1250 559547374 559547389
    0x4021c0605070305010509011d04080a021e101104032f0904060605100314061c08040602060601080106030e1506060c031209060a0c021b0103060905010b070510020a140711 75
    0x10509030350f000500358988010455000410b074811040e500d08410070b1413204199501c8c899002e03401034040d0713548144842c4128a41034000b40c001d10601d81d0480070511981380400c0030a043c18151105100040340001c401c2d0661084d0f1200a140d0200781d0f0b4071041d11161590030440c040d00e80840401c1c00071030b090100d48020822201200c0c01a9540c0c01400540f5118180e0207228106107010080401410801c60400c0000b402aa11178050410b003c50f0502ca10450a85000c0d44a107046443c1c940c0d80e03a0281d42e40100f0740e081808102c2c10400441c000d8424404c5072040c0200400501a135270400c0c80100100c400a0402504000c04124500940a04200400e08000780b00010715080c03904246843c01d0200280000995170f0500b1118030945a000a0450340107461000c0d9049801038040180e008003103550080c052541400000160044107d000e008950f000301c040d00d140c011b10080c40300c200d11480d080c1c4400304844180f106100711299016205840c41240b0698003804403c1c00140b60 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 559549874 1250 559548624 559548631
    0x60c140a210f0e0d020303270304090c0504080706020c09070f09030204181502040b1b0a2306061f030906060b040311120102070201050409020702030c10110708031204021c0605 77
    0x2e62a2000c0b0f10f800c00003004140c1034110390784086d41c02d50519400b01c040104c82000d1581b200c10b00c400c504800183c0c244102d40040c0701041042258480300c150207440b0360041c1c4940350240c0950383c80040c03002e00100b050324064000070455003103a1b855800039510903008424400400c0f68214001c80140c0b51840345407112116041c040e940e20180f4605001a1407940300c82d0310425005000130803446030070106480c108901c151009170803403e0030766410b00e0000008000b4142d5440821446140180883c082d0360a405074800c0d01c040342e0b103603000c0c05a080c00b800c80d14940c0102c450780b4140301c20f10a1303001500c1d403403103010f020500726a58024499150010741041d00c090741d14100a085501d002c0005502d00c000810085d420101e090700040c141d07002c0c5124084206030002a0718046540c00d00c03010150541c0281000c0301c4001105000b04604850410480c1034031071580080b40010b400001e44030600c00c0c183c4a0b002c070350b480d9824882c0150350031150071082003180d00302100140c0d203802018031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 559551124 1250 559549874 559549901
    0x100b16060b12070f050d0c0603202b0203040f020928021213050a060911030d0c0203010b0406271415031c0503070810091404060c140a21 60
    0x80b560905000241c0440180c5c4090300c41c0003800985000985180300400480d0300904002800141c1c409600b404044454804002c0c1c1400040c1c01840a08200f0803145d0300e100c3c03608020340080e8410143c4101d00c420303140904041c541d4607141c401403802e41d281c0b9620544100411410035902064081c80300c4032041c006290503004030b40c2044d400703000c03052a81d2148615181109515503900d886840c0e040e910000381441e61606142018421501440c0d0703210240030f021a072412201080051910324005400c0f4480d50804a400700e20780342c9405508150380110f502150b81120b46500000104110712004820588507840800181076421a079881104c000601208406285003018104044025440201c61401c03040c0c103005540502907907030007070702c50400203035649548440c000d00d01c0099000c00089804c1c0303c07540c1070b0010350305401806640f041304140306081031880c0c203a80c4c21841d4641c3c000080414003030078050a104204a0080349800303201652440d01d10746015003540c0c1100303a03044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559552374 1250 559551124 559551133
    0x201090b0c01050f1f06050c01021b0c090a020906040b070212010e240c39030702040b0406030b0c071a0106050901110d09050f060f0301060e09100b16060b12 69
    0x10313441042c00c40c560301c0240000c0400c0d11109100315401d8040d114044c000420a01140c2000c103010254100d584000d0f481000420080030004e449566145044595016030f41c501e021510080d054025100c3c41a4004c0401d8140750900300c038041a0303004940280da205150020b452041807007031280c3c80544081e035002d041d0002c9000d40103c80b20580343c4260544202c480108000c134030140c3d0580d42462181d0302c0c1c408140608000ca84c101000c003441d080700000350441300a000d29000001465004c0c42a43c09216402060b010802201c00da8403010306108800000944490303440c00003040d43c40d1080d51012a0005114004181c101003608021b02086000810140540c0c00c028041a0205600000d03c1100543da10003000010548907040c066502094a07100682d0b17010161100298030700b011548079a59900000e010a110305402402100024080f40d04420405c01c0704040c4c40c0141c0801d0302e000080b400c51814540c0c0c101068491540d1000b2256996480312408000d07001280000c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 559553624 1250 559552374 559552381
    0x13060f0b01052b020403061d030903061b191806090e0a0510080f0a0308060607020f060d0e01111902070803070b150d0b0702010615020a060c0311070303020d05012c040201090b0c0105 80
    0x43e101ca080c0d2080200762780305120f00385a59a0014009910241c1c20300c5c20010907402090102c01802001e0009d142410302d5441c902d9510781c0700b1a4254110303100d1042d06281951403809071042c06550007400354682c0582c000038030b50744d0a9004030b50010701e4981c00c010856a5918a20300300034a14951041c0c640000800505065000d802d03990130600032030b0014a03103456540003131001131842c04601c0c05200c020907061601c90140d48400d50549250009010034802076100400769482101241802c00703a2668452146100240300e5042d5041100154501090368513102c01d505002000f903400010410300c801081c0c0c45440c0c03550ba1185c461030180c48981081c03e806802d40c1d10326080054582800c094500c5056800582e4006964105200080d402001502200502810a181000b0f4000088c0310010140c2c10740c000e2042e40c1d100f6404010690301c403c0028182015102003240d0180c0c120842c0e0510b144200380c0f190403d105040001380b960307441c90203844903008a212226144d40d40d8081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 559554874 1250 559553624 559553651
    0xc150203010e07030e0c04051f080606031002031b09060f0a021f050c07020d05010f050910061d1501090f0f17010504081c110313060f0b01052b02040306 67
    0x1181c3e00000d440c1403c1c8003200b08141ca1666400e0007150142c4a0b586401c0411401604d02501003070301205800501082916001038a80d240006d0713411902070b10030f01c001d4050004051003940d0250200d4062420f14032540360104070075400c9a40764603031140c0100801074959914034010507804080341c02411a40d640020f6040c09403003007945100c0d07440d08040400c550300c0c0d44201250107803a811074511022441508055006210a410072521645400280490020300041810088482c4c401c10721006032a800d0303502c45150382140901c90700200002003a060380c000da2912100600614064905641c0c0d6035400c040031a4951041c5844400302c801481172290070410030341c500c58098028802410309a0f0f46140c81d00c5107601031200903003c07411600b20500340c0d41007a0203007420040b88a031241842d10007000c0000f0113040465000c0e292900d41c1b03c2c41040ca0003180c080364816140c0c582010350403000d000621494030307a074084000c1000c0b0210100c56040c405040550301070100001c00701303004500d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 559556124 1250 559554874 559554899
    0x105010c08120a050a1a130f0e011503021509030a11011205010f1e0f1a04090e0c0f030604030804020105031f0305030702010f02120405041e0911040c1403160c15020301 74
    0x3801a0780c06c40003400b10343c154680760558402128082e41c00505060100369000003000404900c0c003065092548290621038401d40401c1074900803a241a00903d050410a441e4030030b2601440d0140c205070320400214070743c001d402c40350110605101402003c400c4181040f14026084103062520582c8240700074240c1b0103040781e070340940d80c0a00f40ca142c201030b402d0040311460b00c501d0008004110101c4103c0c5942e80a540040c031100405202c445120303068152141440c0c000310b40188001140e04c406890b000500f5802a501900e81c0004d07902e03540c004544030791005020000c60458440e20305100c3c040790140c0300003940940051600e5440c288001403e0342c4044060000310b61218030386002041100e0116401c440d01190001005450810341500d003c0e450a01144824503081e49442070040b41049908803140446c0d04006490304048140c0d0740034861103140290250a0001400700c92000040d5200d010300350610541c6205242e5883c215056036000c10708a490300030004008142c1c8012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 559557374 1250 559556124 559556141
    0x41110020a0c050402040819062703142b021306050705010f020306061c06090f020910021902010e3609030901050d180c080115120201080105010c08120a050a 69
    0x81301580b9003131419040c643d8404407101ca049001086400281c100480756020480480010103184880ae01d55030003c101100d0302c901c10ba001c201900c440c0218003075a501292003401e958060070f0796081802c001ca40d881083c410040501950800c480c540c5200c141040b50002e25065440547c4d52140d072525034251070700000c24000450050007484030540c1c0b658107440554942c43c91098800b801409000003238819540080702603807a01100352010426a0003c185000d03042d03d84541140e2139140c00c03070342d5801c01c810326039402a090004000641c4142e80300811928018810304420442ca010212020340503003032040d441c010070704081440360709417070b0040d4880d010070040c6052948420010b0498820860380c40030380c541c0c41509802010f5001e401c410071640113801c024840d511442000d00801c054441007a042c0031209001400340038000d8010610b50341a03549240d940d01e00801500c5c00392014108580b02002800108400306100e031000c1c1c45030002050103d4242400400703c0d08460300013 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 559558624 1250 559557374 559557379
    0xb0a0f17010b0918161418010311060f1c020c070f030c0b0a1b1104060b040f170708100507030507020a020102070b03070c0609060203070207050109150305041110020a0c05 75
    0xa2001181c03a40d404880b00c0d4410004c601d00da00c0b005445803400d0401c0c0d42000c5841905120880101e08808403401e202d054560a503211102d61108402142c02840709100052441030a0120441941403000290610500b90a095030402100d21641ca00c02425120f40d100c209030f0215248030070100400640f0001e1684410080d02981591a00000b80840340038004c004180010182850ba04c00c54041c0000180d40b0302501c214440e91800b40c5e03400224504071071249080c880041002a41d620031181103c041001c0c40792028540403139400c10300300d03030208100680a407190000c0c81d250217100b40d00c100250160001558a44400b01a0440300044c14500456204484010061740c000400c0f800f40c03054490081c0d100d035189001110840c400c03500082600703041c410f40c0c004008840d0059030042400e602902c41503a04c440045a40b40b2042c0705041d0009100d080600096000c0d0f80101c2d005802070340140c071038410303600104507140c81d83c041d4030005902c40d580500501100a200c2d40103072404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 559559874 1250 559558624 559558631
    0xc0b0304080d0b010c0209040f050105010602010b060405210d110601060903030c02091b0408030408060109020703050d02090402070807120f05180424030c140103091707060b0a0f1701 80
    0x41e84996465015a986090490340d0b580c43d54407841c0e025240362202030b40e008000d221507150607d050910382d03000880842d0190300308000890b80b140107000388054080e001c1e2546050900d44420422a4641a904c030440140c0450902d501d09400740a9887e000145494510a09410300146071410005034040d00400c50410014000603603c2088447c0c4550100d540114944481d42d1000001d60754400024807a0400903000039000320100140003164803003015609641e907120443c0003640715641c1c000b000207078100030b600008480783d409040325200141006013442c03150758450351681d00460040d036070110b0307401c400340029a02520030140d4030050301d0014100200084a241201c0e8000d030f20b17a1059807184201c2228005000820801c5004004414400f903900c1c1080c21008042d07020349000040f081d91003022650007030140c002c2255110300003400240d80b001981085801070942111503a84401c4d55601c0340d500c000d2150b01a181002c03000025510b403003060b5003290018220203415905 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 559561124 1250 559559874 559559881
    0x803032404020f09010305090f1e0c0405040203120c0708010f0b0f0a0e060d02150f120f09030403030e0f130c0315080304031101050c0609071701020310090b0613120c0b03 75
    0x51071000c0c2d03a43c0744006c1c20b0100310b81e2502e081c0c0c0d0b420710225458403040741c8145a0310f0316203c450318108200910000b429a140088240d00348170540f4800c5070041d41540c814104000403254480003016820714200c00e4800d242e8a41c024682524582c40342001c40c40e442d00203010302e51511843c0c03802000c100b11002c65541d8940326085400e14401080b07544155800d9041ca400e6403100c0400c3c0e0009600e00103015503442c010300780807481e178214000075640b007106500012a0020080c030218080d4044074000c50a180ca15541250051040002180c2110350b100103a8801d0322040c00050003041d002d400411010082c100050032500840d400e01e03596000011304100541000c02113074140d0381c00000000b44d031045600140c0c0c092091028150280c416070081000c603c4010654a080c0c49000c07004130419a85564072030300341d00054408051a04d1103c000b0800100716034420400744101504441c10103000008054007031021341d00894142c0d00d141d01e2041080704d016010801b03012104603e500350306 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 559562374 1250 559561124 559561147
    0x1090f1e0e0a0b0c04090e030f032d0a05011403070f050603060307051206010e0c030c030f10080f16150f0507110603070c050f0d0c0813080303240402 66
    0x382045030030094603690107040400c02401e20510310b00c15000041c0382603905105490802c00e900500c07030394488914143c100000200007200f2295080a048416030031510b9a5504504881c0d50f541c8814122008500f4030a203144120446c0e40f05443d001d0700080c5961400d10b03ca054440844221482500019000d12003000c00d0803009003030315000d44000d500e035501d04002c28904102e580045030b108916044503400f40314005100d90580340d00c005041001e4485600440c142d0009440444160100b400000c00700c24410918952003802c400c201d1001a589015803070030000341003800042ca41001200e880c006104041900040c00c0d04842e00e50b8210103450700403c0c40b01a120800e080003800182041840600503414421440c02003000e6035a041008000e0185050848216254000e50f1500c141150004c5065181c608550701c0c4c44910302d10555907210340750301c00d0f0281c140e070f54030159011a24100030005107100344513040600801005d0404507031001e03143c8915880c411401007001c441d410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 559563624 1250 559562374 559562411
    0x2615181c0207122d12020a0809040b030715030c09150f080a020c1608010506010c23030d0606020105010608010f0b191b1101230406051b010c0801090f 66
    0x2a90f4950a44030322000500e01100040007150004020101c008a402106100345000c0000c03a80310b072036809658000802c0980e2228001540074080307031814040070381a810503401a000e045401019245402d4070350307195600f21109941b860380080d40c1d2300c0300084003540103034022003c0d000c552484803103000100c81c02410200120074140c2001000d1000c14070600d040e8044c0d90a210383c41040e25100381240e060b41c2143c00d40d43c440c80c180d96082c800482c1c5a94048c030901101c960f00312624507044601040d012000385000d0428082c58401000030000e09440c80c0315540282400e0750000c103403940b6100c4020136202c8180c002d100c01c1c50384c82100700010003030801240c0d405403040030800300260101307600381c4003a4116a6648400140e10b042d8a08000700c522204122a1003600ea00c003d00350b980780316190000960b2070140701000c041000b4800280510040d00c01c00c481715415085031200180e9a509641003210754201040050f40144203181c40d5009000b1b1030826030700f081091954050099114 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 559564874 1250 559563624 559563629
    0x30819021606150b07240e2a0a120b061c0303180203030c0705040e12030105060d0e0708030705060a09020102060601080402040615120f062615181c0207 67
    0xb20390315502505a0707845948214000e003600301095840c0d401d1400c103403107201c4c084040680c0403001d00b00900110304243c0700304203142ca1164020701da045010310405032200d02058403a840007083d070500103015035035050300d50040c0210304001d4801d107985240410340000c01401c11845030b4918445001300504245858002c00d8041c41c0c0468101014480c5100f0400c52100c0690540000036180d500b490000505d2800c40708191020420159802c1d01c4039100c1c0005a041c2c0c1800d44104010401483c00300c0c06848103400c15000090001c6442219600d0000d0341c0e0b01218082e080440c0704000e0003814030515520210405080c44400303250390000f0b403036030b0300100020f060083e120003003019074440d9030000002c0c00c00c00b9017030410300d01c5801c8003500f5810709030500c2c80140e0170100d24884170413441c0100d008070740103400304200c004181c0316134103024100c00c04c204c100ca00c141c5650440d102c883c520000d001e00d048149400c2d440210210050508a0800801d28425600300c1c039202d0301980050702404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 559566124 1250 559564874 559564883
    0xb0c1005060a0303050f090d02090705090f0f06040b091302130305060a11040504020a11010501260d02060105010c050f06040b0124020304050f0a0302030114011d06010816031401030308190216 84
    0x2a96034610001807541e0307100b00b238065000300510742000364150301310000b80f090300c10459821842c110030104014106c82081060342d0441307000d000c01c1110703880200192080c550010400d0a8241561000404980010862078000703072038100b041050010500a880c0c21150a0100b4800c1020038880e000540c82144901d6000390b038005101149148121303048000d609115000317100c1560345003103440b04a1040e4803691114071491444283c0c0e4180004d00058442180d00540385c240c0c40c000c01592121590802600d01c1c0c018a40081ca2614040c850184514440c000c005075550400c0301c0300a4122262070a07000304150340384505180d523000400c0e82c04403503048420403000400c4002156280100c1e0b0b00003901507003000c2c035082420f1704078400641602c00c0c01c0900c1caa0b207080c804110030000750654115001c16004004104100d4540e524007803610b00d06d050110381480c0ea081000d8078250268001d900103640c110900060071019600680c104680d20021350400045003820200711248210050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 559567374 1250 559566124 559566127
    0x3080403020a061b020c041b03051f0303090e0c070b01050906060d0501120b090304140d0303020c100603110303070507090207140f030d1b12050903040b0c1005060a0303050f 76
    0x904041c4204103012000358441414000084a204902c000401c0511844090300905034540c00b641018400c86440031036104002c1136281448c0d038142c00800002c2d00c012904a540386254105032007184000c0001e6100e03036612603046103003440c80d0020007009030040d4404e00c410032141c0040707140000c8283c1590390848480015480b02c00010b065445100b000c14103490403d000018140014001500030b80d002d00340c0100c00d965004001a01e900c0703203000d042c64843c06d49a49a041c0d013041c00320030203864404d0070018600505203800c0f51424004c0d002562245441e01001c0c4100f00350706a07042c03502c0a041c0c00850902034540d407042d446113914001d01c02a00c0d4042054010320034040304803400203031070000b654001010340701301d1512030788940c2000da00382d8100304041850540c05083c40d03068103203583e50501c2d40d040110350b4102518002d44840858130003488007280c0002c40710001c0c408190240000c015111b08000c0e004291140204494410100c044041000c80d070884111842c05035502580b6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 559568624 1250 559567374 559567381
    0x705010921111c06050f0c030105060d020304081606051008010c090b1e0304031d0d08181305130b01080f030405060d0204180f0509070b0a260f040318050d0308 70
    0x1001d8031280c11083c90429502c0b4915030901c00c5039130240b40a01840540398042d035039440708150882c4820b1091179040082004451703040000c60f80a142c000d84104a00791500d10955850b045129050744281c4a445e070302c10034881040702c2055144020000313080240140e681024010300500007d2240d10104500041d41142040f40c0082c407105040040d1501c980300e040a040003044180780f444401e082078050203400c2528a03000e061640c5c5607901c40e400e1403811080b42c4601c003112136204540c2d0b41100581d0305100d40b030b60350f50007003d125003a648295047c19005082184001034183d00075074503508084100e0140f400040110f5080c1c420544080780c3d9070f1f13100810b00e4001c0c0718aa0001002c00001503054030b055807150081130402c0d032051401c0c080303522079640c1ca41c3c44520a1140080410081003145050390140ca150400420021000e4445480003822012402412141c84c051807400008010425030044081a19080603840900c8140e0510340841c0104a0a00c0c0190910900d00b000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 559569874 1250 559568624 559568629
    0x2100e03070503031206091e040602070311121e03010312080402130204180e0c0d060b030f01050c07120c08030408030c0d09110406210f030c020d05070501092111 71
    0x4407005081c09000c03640d482805000b05e0441110555400b0b108040040114032403c0c080211641c050341026002011b6444e10380d18000298400f081c00c5040c010300c00303118603076009c050107000d0760b00c0300c20728100d0b54450b00e9090640304d150301c0400c000c0003280140014030100d001e176032103a100304420f0305042000b52920300026080b42c0046040c07480c85c0c0c1c0001000720313360b00560342c078042001c00341d00d091180c20007901c3c206032540b910342c180039006006440c0c040f0128019800100d4901c40180c00d03940c0e0300c100c140c07078542959421900140300800000380b04041140360800301c1c88070500c600c0d00326808800d5540d41c4000e4840908003400e0100040040742801003d481150b90010428004101d00c0f111854441c000c282c07600c64403440b13180350960020340e4103895645030262030845040100d0401c880d5440b0000b4a005080503410805000e88060058070f40d503c0000d040c0f03018600510442e45071100043c1410865000f00c0c84224034464059151b007404800c0e000300a0b80031140f44046140c0c4400b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 559571124 1250 559569874 559569883
    0x7090612061127090604061401031d030a050403020906030c0319050705092a18130b090c0409060623030a0b190e0c0703020d2709020c060604050402100e03 68
    0xa4200096040e200414149424030803510003c030419100280b03169117403400c220460b1170a115a021051003181e440300690f10a47c4040d10303541804002d05103d1104502440c035541180030800b0104200140c140190b2400d02c00090340004100c004007150a00080803a4540d40d03403500c6071002088601401c420820306024400140c000500815218078220300b404d04050340810041c4071090300c4d0010080038045d2401207400380d414070515410f450003840240030050f484c1a00700d00340705603500a194000e030b6035451224024044071000e1a110750410010404840e4980d104500327101060701c9441400c3c5444803002e00b00d030504180c1d252603130b65410000700544003941c0c0701c9502240030418010070311b02d880e52001c1a00c50010081400b0307031311088002e6485c42a1708002e40540e100381c00c5911802c7c442d005104990000130a0444800301c5202c211b410301c1c0b0290444900ea68003c2411300c2001800c000081e0300101c101c0f81400641415008038039410010300c2100100310039103901307051a440820 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 559572374 1250 559571124 559571137
    0x30504150504050603070917070e0c0903011b031e020306030c1c020a06120c082e09020c0c040b0301020901080a050a060e0916050a03080d0c030902130905070906120611 74
    0x500c070175920718200381c00130300651860049000d0b80d844c2517070201d1000300008490f0141d4a03010112400c030744450074400c0507a000240a035034550740300e40c4d81e07101e014074659441451440c00d84020500c3d58481241104c116180305811300c55034814000c1002c10b40c2c0014482e0300083c2c06445095503031000b500c1c03045865080c80c20281d04101c03600800905e813a407000100000007890380c0100044180101c08845849042e1802160742100c0c1300b003000056890b028004942c0405416850890364418500c000d9800014281085410000800b156800d00d4010b50600c1c403021002149000500320018003140f6003d020f101c04a035540e030000e50031702c07907561009000e440382c85000c0443c1e140616815580c1c081600c0381031031004808900003820300300001a401079944c48880c0364140003100c29104007c02050103a80201a140c60030381015071a01d6000640020b0410004500600710b820b22034a8529203900011071240340c4082000054494040200c00700da0004020841034109244c3c14000e00488 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 559573624 1250 559572374 559572379
    0x7021f1a04180b06181609080a0b0603120a0804060b2d040c0903030212210403270803090909030d0608030c0d0c0f140a050d090e1303050415050405 65
    0x80b48200c900e002c000664401103106446051080e9100c1d401c0c0b00c41002d070140410f030b003000d146002c203c402e8002d074400c9103c820f8507e0000c441903a2001850326001c10ba61081d83c22000c07420900400341014000b0020481c4040401880c00c4000480206200b400401c080d006541d54412140156260030b10001a03150700200f0f5101c55840c3c0ca01401001c41b0208401d1045252004482a50b4003607080380040302d406030081c000150341881c44414903404a144000f0748624000300c0c900d00c503c1200143d0107640a035a46880444880c801220004540c0c026042100801602000744000c000b003155807816064840111030348030b13040c1c22441d6018961844101904002c0d02007034200b0000050049102c500c0115200d05140c030700c058a0b002c2c052400030788031408556603100818000d41a207901d608940003120a5803003180c8605062040305404400043c20f05c00080000350710203040190841402d182c4a07640c0e00032607074007520602c603074803450111018a12503070700700c68000c100342c800500c0c1c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 559574874 1250 559573624 559573631
    0x120f0501080706110c0a06081e0a051f080601120302070512370b041a07020607090e0c0a080903130306090204060b07022d030f0a03020607021f1a04 65
    0x100c0c00025110034407402000001005451000c000613000a42d04040318000f0302040c410300c0c14288200c41c100b6000f044500820076550700c0040c0340410403500d62240030003d000098a040c10003030a0000301e00020030325213503025104244040c0380c0225203241141c01e900c0043c00305031002e28040c1d04001103603000741d5010b14102c0d2a55418030380800e4503d038001070880300104403051000d24008278443c0785407550900c4604820007000070303610882590020f000b200102d22004d08030346c14100c1c1010498030003006030080c40030300c014903410450060140c0105901d0030b280b0703c3c08070b507501c1c81805a400350108004401012421094080c011152103900c0c01c142030007110345030304002001e4074101c00200c0c02203142820000f080ba2400c410f035200d80383e008140c0f0007400f002c1c08400c84120303041a940401300031062124100c698003000300507001030080c8041d02502d07425050117424038900030030010940d00071507801c2044001400302200c3c0a032070910002800410481c803468201107105850b50131074038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 559576124 1250 559574874 559574879
    0x909060b0405031c0f0c0201030b100e09070203040b0f18090405010e1603150c03020d0e160803121b13080c0a0501030b010c03120b0319060506100c03120f0501 70
    0x10558024019290b00360304903244581034240d503040c030030b041d42d1101001640b03c207440000d19115000340c4501600501d00416030300c426070f00086a481d164034080e030100300b4034483ca090604002c040140d200600d4005581001e1401580c51814800c071141040010000113404903400c44d2007151854907180079081040d2458549003050007450307654800c0e92640b00e02101001c405c03204514140941360300420700800c402042086034003030400da611810038543c083c0007031402c02e803c41c4256403c00411000034598241c8680b011407408859400040298108100340020b2245c50840c058202600880702c942c1504048480c040e075001e4030722849100751724848009010385000650f0540400122020000c023030340c9900540c1140c0c4042202e034040faa510b2000d601083c002d0a9160900e4020400480d190101800083c18010b541d1002c2d450452207401050a00006206965003d00305a500071f845003102d400182c904a43c0c0e2000400304080e204445000e00050740000501c01030f4042c05200341e58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 559577374 1250 559576124 559576139
    0x2070605130902070308040501150f090c0311030c0901090b0306060316090306110403050d2d0c0c03030302041a03060d08070f020901090b1201141b0f040b0a08090606150901090906 79
    0x140f041c2c8003980c0560905202e60941c0c258041007400300c500f084019200c40d44cd008184015040a101150074035030386805080e03090f14a100214468040340c2044c40da1121703120000b501003d482d0b00705406641d03043c010880141c60700401c036a000004d58098000d0440c001038100c48215079908010003c40c103124081d01640b1292024206a034403c6041d00e203049486002107400e80c858840a802c49040d41a13040b4407a160200c003050104540d05e440039110007981c07a08a02e24807107900480c0001d500281c100511180401500800d20a61100074a103082100c0001c02c40c1100c030001402c030714030005030340c0c00704441c5042d0520010790161a24200c3d42c0d566084200a02240d812140141c45203000400c0e58503043c4561190a4440980d200042c0c60380c08072503a02c5603d501ca1080c0041007088442045807a10000c0c100400e00a01015074510800030020710708030019000c0f000c0b6900c8082800300c0c550b181300442080100c1040fa40740c17154168030048444079402d80c41503100d6850290042042d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 559578624 1250 559577374 559577387
    0x320d0236011809050c0f010c020306090703030306050109060509010e0d021c03030c02280804080a1103070504020f1c18060b030c011106010614041a0d060501050901020706051309020703 81
    0xb21901c2581c26941ca0300504000140e0b625100001c1483d040380749210351502d4204401e403184401807400b00020038056003c649003034401c2c0d403012029071169004104066244c0108009000280303040fa05183c60014094168002c0101242c140403441c03465590300d13182d07005003411641d0005e1071080318a10f54101c03c041040a40700640000e070a1108200c40b850000419412100f9008042c040d0072400565800030210707492001c0783c11b01400c21000031181410040c000e4400e010350f442c0402c050310b603810107180c81c90700c1d072003140224014030160943c0241071003a69aa00c44110b0b0b28400c030032031426040018600c00002100c50821202614280035041d806000400d50039011910b804c1100801903d04400040034424183e001c000140300307140c802c0203645110141d1261807403c068542d21074130440d0700310410f843d001c800081082d0507690480d0080000500c002e00741546482c0764000001d4803030f251400b5501c2407180c0080e00f14607404880300d5a00050041e01c8045458034510b1074002c020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 559579874 1250 559578624 559578629
    0x30312111b07060207061b0f0f1b050a06090b0a0c023303010e13030c02030307200108091011160c061d06030a0e0a0b01320d023601 58
    0x6038400ca103004921213000280c640c1c2a90040e468100c45544242140c400b03034907032804121400142d006086d4001510714800b41c00007840f400d9241c007000702c5004440c80f10301c02948510310035580e07000e00b00581d0f80c00103400c0701541c20b01d40b8030940d034002e04c0405a0f00900c20400080d00300d80022400118400350047d102044c48241350303122600a0f18194030f101030300007809095004102c60000c500362000d4048204481c46c0309041a8410f411603400082c2180c110100aa521502541d156a0040301c0c0055024002d00c003420601c5050900d00e078400c2e07540c540100c0300d5076545d9845841c41c41607074503042a244d0504500008401214103498121100100b074411040400c461000140115034414540d61062030702501090031943c07061030440140526201c0602c1501031134a4000224032149150b902030288064901404061a49942480700d404500c0c840058070614240d811607641801c5a87c1d1386804850283d502050a945455456104071104200302c0c60030200555070a404080300c0d04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 559581124 1250 559579874 559579927
    0x106030f020403120c1509051e060907092004030501150803190503060a090216120306210309080706031a0d03020a02010c06110a0e090601020c060403031211 69
    0x100160903003155003640158000100412010300200421505c10424802854000c04000e50040040c0040030f0444521003000d48450b046119030384003003500c1c203020420b10040000140218a03084082c1a110005405440c05490325542d03802902c500e503000201e6402005a09940d036950b8a141250007000e03120301c0062800d1486400149452000c000c1e80d8641006025504d46002c80080880d803a5200814045d80414801c03400b00b281501b52002e095585155450304e04000d88500340714840002c540010820941054030500804c104100320003484401e041d07410b184107041d41340940d8528460b4007c1929407250800014100e81c0c103401c1400b1404000801c0c0318030003161410302800380703845030000d40540d201e9008800154854105101020b000300e40001d22050300004428440c0d010742e0304100000d07032210000c241840d018051a420401c00d0000313080c8501501d000c03c106010b40d20000c1c091103030307036101083c0c1c4001a41088200040b529407440c1c3e00d804282c011840c880c004000d408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 559582374 1250 559581124 559581131
    0x3040918020a060f05070809032a01032f0d330509010b120a060503061003060b09090c13020d18051b0109090b0f0d061d0309011403130218010603 64
    0x41d402c4c4c0100c840c04200d500c2d55403024505007150310798034100d0303004464140e01407040390740d844044080040011190700300081c00b143c4621a084c00181503c2c2a091002c0c4006540c14203600201c3ca034040c0e00240452084c00c0c503888200007234000004084203030040c2001201c50000b45107040b0381c0b5240080c850f01c40081c0890b4a9152800d00000c00024000e400d440c000c00c00c80004031082503992103900036a034060114034542c8441c040307410007a007600d00c0002124540004d00c10000c040c01100c0310800b0644a600451914400199903104282039140c0544107241c24070031110402d40499514000301503060150560002c07200d12544800701c030966980c028010400307440b01100346464094001651100447e07400e00280d0300040c492951010380c0f05030501d032070811988030b2041d09000f15005074800201a10920300709440c00d901da808039070064004109401d40c5a0300700a520341c0c2d100c0c043c0703d00b0b5207943d6506060079810180c0340b0060760000b1403403051003143c2031003507095041e14026036052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 559583624 1250 559582374 559582379
    0x30201081f05011416030206150409080f03130c030f0b07050c06071407140c0102160f060c480f050603040602040b03090f071406160503040918020a 65
    0xe40500d40d0200401200d420040010002e642c070a50401a0840491026510300204640c40c0300001c6000c502c110b0160b00310101b00070302c0810100c54a0100c075026942070018150f6550f921100d071180d890300384002c0340c0204c04070f0780e501004290f202403554840c0c03016070300c0d54403802c18400700021314a0403581020048006490148100280c03000d800311100145080c0c1c0780e10301c080c0da00304c0c92480ba40e80074000900c00701c004600f03410912210540742c04050641050007200090030b003542038101c00b804184454080040c60481c1211404a85652030200712560182c41c115220b400e010030030045070300c54806200200c201d2200c3d0040e8442170b2030342048100620890180c41c810440c4030304003c0f180d0000007040b06082c0340f001158070070710030301005140603110400703d8031a40064600c00030f035500811059800d088200b0480b8090030702420f03070450071030340080001e0841c0b2941d003c4591140c0d2400110003003160400903079020345210300b4144100d1003c144034410002e450709e17081e8070410119600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 559584874 1250 559583624 559583641
    0x30301211e060f0e10050403120f0e1c021c05130902031e070210230c030a060b120601030c020c03031c060b120403051818092e0b0d0b040c03020108 65
    0x1044010703000071011745141011210a04024200107109a081c069030340f1f08000400001d21554a84842d4480c00103010140d031100b052522100c004001c0040c1854001c0c400a03e40019070004080c0c0003500303039401ca01c1c001c030381107456001c2c4d0640010224440503001c1031a04a0380c000c0c2d807060105c0300540c001081402c00051081c8001d03250700300503810940300030000380a50f802c0720304c2e0100740a060340714100d1644050118020100c1d580200c2c11004000e001c1002242e001e0303000100040c54940703080c00b44c00e840d240345c01d420103801c00e0b051541da20074184089000344040191000d00409594842e5030300c00081141c610700742c90707001c3c84a10f02040800e910611500f95900c0240e9800110360341ea55660b001e44040d4414180c0034541e1080e40111a5903603030390140e001c40c2e1034403c040ea4045041c140280c501d0310025a12a090080300e0000c2200720040070703030b94003201304105840810203085900100b8140030356100040e200e02240d034200001e0140308000801101d1003130340c0c1d49001d642e0300c906 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 559586124 1250 559584874 559584881
    0x9010e070b0a120905030307080117010209010f0f0201090c290c030f0c0a05010f020a0f0c02090601030c1422060203270114070f06050117030301211e060f 68
    0x1540c100040e080c803218407542d22074820f2080149884100140a035030645034185941c0089a61400013169140103110024083c032104410404050003075051201040c0087c042c16001044201000b000180404090f4400d410541c50290001d0449074a00d40b030f030b12942001c0351400e07032403510f4500111542003441d08410840781d140000c403004c0c6062600d01e03a44141d050b030046210318058030802c034628001c90800e21070bc0c284d480303113102c0040c0e641a03002c0b40035009424a1070010280000f943c40c540158581120b5280d20510920340040d10716134000081d1000900c00c84070001a090208605c550003070344009807494440603014511203140e488008030f070b403480b410b407408000d07030003052407094204d6810700c074082240014180034903100c00c4c0d044410381541000c1d03001e079640c0d8150800c80080c005544a46400751a0b0103034041c6204107041d040f1a564803047c401c01c06030700c0802010b070301345108c90b072442142c10368170181e403902c4141040f01c0031003d940ca07a50240c0784645442d403020103442c3c0780d20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 559587374 1250 559586124 559586129
    0xd0908071a0d42050405151503011e08100b060409060b070c0f060518010c060c0302090901060302160f0f0803040309081b0a0611070506030a0903120522150504030809010e07 76
    0x200d443c0309542000184800307000080c120b140e801c0010030b8071036401d946c0c200c0407031440300d941c2d01d40a85944c074003060042c2c40900d113110342040c0f181860040c468170034049510403070b8003403444010442c4181000400c0c4c0d18415644043e401600c0c00c040801e4424120000305405406504814811500c90071034600c10041c9102c2c80003c107008220903030038010440454640c03107405040c812801c407020303281e8034240c5119064480000e980042c0044251500ca070446000d0840e41c40c00310f0404803215645010010000c0018110480714480001046102010709031042d82c00041c16450341011b107005003100740c1c41d000d400c09a00451724000d001020b9001e1994600c07900800b2104242e280400c2030350300319418403200b407031401100408101501d661004501680407240e001074540e40c6401e00078480002da102080c5003a04001c248542100d8032500c0e2052041c03462000d02c1c000c3c01f1850710310460000e0608410750b5a04100412081c0b64001c0c000a12501181009101ca000704500c0c060310b8a10a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 559588624 1250 559587374 559587491
    0x90415060903030804170307080115020a170f0702042c06070507032a030906110307020a1a07060e070f0e101e030606080604050d0908071a0d 62
    0x20700810200344101c02690308240140c030744074901c40d941d07601618143d104666944c0071529942c010440b052075481c1e004912003040c40034103600704495880c1c107042d01d1440c4414810800104808005110304070440701d0f41980140100620310155a020700070298400d00c03c03a4002080107580040c890110394284545d040c0d80d201407078400c1540d410f80721402d000120400c51048070622100540011004490031802134030751070360081c5031440040c2803034500d00613040341b9081800481c005844c0c01800400341c40792080c042d10500128405003031307280580c0300003900791410000d0480c0600c1c0f0211b8843d00792036625106041154a40300011034400341a01d036001c4c00c04611408000b40544102c00c3c0c0300f81c026003442441c86950fa9260503042e01c4940c0c00160240d0041d0051008100c030030400c224007000b0300e0030001030007450300711070783e4950300c0f20303c24281405260f1030f40c2d208210300b400c1142c100b088848001c0050021409468a102d03540c00000d4001c0c240b220640ca44540c042e40855081c3c2c0c000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 559589874 1250 559588624 559588637
    0x60f012913091404050d11070b0c160b03010e01060e010509040b120a0602030a200706090312020d02030405060604020c0304090e0708030c1b04061d151509041506 71
    0x50340c203055150322222050030241240c0e080828841e503507020b031000c441c0f06450314044a042030304003903041082c0380312401d09118220070000d0441a0208105084071080019981c4070b0701040091070406014904468883d44c2011020500803200c2d0301a5040e01c584644202c400da80b18181640c20304001a525400304800b80008682484d040d00504164032002e0708982400f18034468180c54001c0040c412210a6008002c01420000798849c0d03801c2100d00380d01515942045d404808810701c1481400781503607072941118018540521040040001408411980ca21192100400940041d2030071240c0d0f001d2038021500b1482c090080c0c4041c1e0020700003451401c0d240203034481c01480d40c1440002540101140050f0422082c80030b051446c503140090900000402c4205081c56003010782107101318a04503081c01065014030300c14405c49100e01c4902c0c0552030391800700034412030004c0b10710390141309180340a21050010001d05802d6001707079070500000149071740480103280359002d010000740d070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 559591124 1250 559589874 559589939
    0xf01030209060d1709010e09101a13030c090f0b0603160309050d0215071e03020d0f0c020106050418080d021c091208181b0a08010608060f01 62
    0x1041c041a81d0802c200a0240360880856503808603000c14a40c41d03058000d81c0440d0000766540c000d901191a5007046a82098500e418882603c01100c81d00510309070321a524078900041d46200c003101d0b100c0751003206075450240ea03031401900340031280c0203502205041854017002c1401c540107a428840c40140f6090a41e80c0e00500104020000b000b0321040540f03a80b010301c0441d400b40a00c550040065024010a9404c401031204c00c86014081d1000c02c1703600205047d50140c2e110001c003e400182c540940d940082c07082c0c05003d000100c4c2c0a061980c50403940c6000d440c1c055100508484c002c5e20103001d2100101d013a090031000320000600141c0040010031200c42e56039008185192803110030078110030804e44002e00322106010308503000d240b80c10b41000082d03004251658002800a05c144445003011420f07a1a0035a20203201d444520031120701516a4446030071001400c010b5000f04086540c42008680e580c0c07054544034a20149600081540040042403407180d08680750340710001c0b031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 559592374 1250 559591124 559591129
    0x30c1706160504030804030602071403030124031e05010305060a09052808040909020a0b09010c0204050c04180b040c0203073903060f0f02131a0403050f0303090c01020102030f010302 80
    0x81a407120300800c0420080400090b01a6016202550080c1001610382c0ea140c6000f002d40114854144070075072003440100310104100004c142c540d9940718013503e92203640d00083c0c02402c280300c865107201c0c8000d0b14101e0b0404881d40694100e900400480300c1d10340f580304008080720300c5464083c00a400141c1100715000c02c10302180d05c0e0520f154000320801ca455103512110340c0040d00140702d19522451150b0035442e180043c8005880381d844058a460b24001c0003034406240850001d01a0391200005924050450f0517200207003400c01c400c0707203803101b4011100c0c01440e516490500c5203184c461188039452001069170b504692000341c0d81000d5007100d02c2090705840b000c003282ca18540a0b01c4c1c2d00003204012440400542c407030000810b120501d02040e1050340c42e482004061503205004081110b10302d0501001261400d90001d4598a600c0051084521582e04060702903c945013581c800c102c8000b00451044260000395130a0750700c4000124282d100c01d50f014105032610700018405072 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 559593624 1250 559592374 559592401
    0x3040302011d0a0b070302070b040f1202040906050a020403030908030405092206020f0d0513050303071b0503031f0e0c030c0d230a0e010905071e0306090c030c1706 72
    0x42070551a505259030010300103140b40f0650b810002c0004404142503040680410040010b0085450810700301420070054030102c20003445484d40c0242081078070030954407582e10820f0400d40052041c0700c1c51804c10940c030041d5110b44800c4000901718000060a8a8080107031805d880c4d00070020011038807803040c0f002c1d602080c0030718a14624001508240002e8051000300015404007052a8894446101072400c90f54024041c11210255109001c00900b020044a80c01445402c00c1c00004034440007801c01d51441010041c603138480082440b0b181038603070b0309500c4500c45810301b14840c0c545400c02040d0b204402d17620740340f80380c4092020541505da008050001901807a40c00241c4200b130f16654602000a54213111140e401c02d8203004135074240740610030f5a01d150400070f101070301e42a40c40a995a410380b003200311003508a01000e104603040b4070208000c6800510074040100a405c040e428035000d880b0460f4108009400069540d0044aa80350031070b100300d01814880c0e5a40c221406d04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 559594874 1250 559593624 559593647
    0x2041706150909120705060a060602010203070c12170408091212070308061f1701080d1d040912020607020d110a1202074b030303020903150a0f0516020304030201 71
    0x1180201134841d407a1340c07443c03009000c10700d0041c0003c00c2541810955002107400300c0d04524116401007040101c415042101080d80950140300d1120f410000d910031540310003c0403520a80c0d540700310502080c4510180a49841501242d43c1096920b21002d03941e40c0304c2c0343c0210942001c2d0b06020034030200c1e0103400e81ca036026174040c0a41a0751200c1310507010090314604801c4002ca040b13011710050500f0070007a21409459031800034000500f0400d4040c0209032542e0aa015111017a14082250340b5281c000d0391070903512101b010500d0004440107510b80c0341c201d54000c014800e83d050310280501c2220700403060030060020303140052281c1c64003a01d154900501c00c0952103100c0b000180c01b4030340700d0226031a0b05007619180d107400c402040f094a0785114224401e90494001d007440b500a070318843c0341c080303c3d8141401603507413200002180c01d0221030400074000c4820a400c008100d04640c22060072003918031001c1000c0d41d00e40ca0040d9110381380000003030040c0d109210500040d409918000311 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 559596124 1250 559594874 559594891
    0x15090f050904411005060f0a0306051b0f0a0201051b07030503040f0b0108151303050a08150901090f0e0601210203031207110d021506040f150306020417061509 70
    0x8201e003403080c0e220041e105240c000d0481d840f8482d03801010031303280319058020100b19988034007944941e00054041a1134000a844660350380d0100341c1d00012004c41200f04c9103202e1000392100c02192010307045030840461329015500b040001201400d402c9500700da06901d0742c90040c05e01c40144c8040b02c1c0e54100070700c22902c0020501a00020504401039a4000c0c40302070010319000300c041911000120b4054039a140c4103440c001c0c280d0009812070292007070f070b403520f190072405540d030720f509591701c454100c6913941c11580040c000728200503160400740390f0592034101070001d250030791182541c800c824410002981100103040c150344024028002a55000908503820400081d83c80e83d203030001514040081100a11550760002c8140701e101070540e082d00103407228100303003140103400321070007815544190381e40c0502010100403940f011015030003000a0415603901d81c6080d1000354486c5c00ba00b400501540702c2d1003e001d50000785517101e99460301c240307200401d030f0400380540715402030320046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 559597374 1250 559596124 559596203
    0x11505041a12010f08010c0206160c050a082124040209060408011119020a2a03052a040204210501180b070305010501030e030a140415090f050904 64
    0x801c1682c01d200c00303018000303400c04000c03510700d010802401c541c4842640d909541207a0204010001c50b0b10525121046034100329103001864a880c50414002c4d880040c198400443c01040c1d00300b04001486451454a901d00d800d6256216041c0714401485000e50702c120342d00420048906040d0040c0034111409404642050344540c0301900b920b0301d14629685080000c141c030181d800c50400f20100b1140c090002e480110b81607290070708140401d200e5481c0c0807410b0303055010140202c0c0403102c000c58200d41035400541807c41d512042c0c101c03036806490074802050103940585003c1c403c890442d03001c4281c038000065000280b0984624140c41900c46568511007043c9900044106070300c69840b410b02510a0b140040014007101d0741038110350704040c03820301c1c81c1c000c054000048074518100d600742070214000b80307010000144255000b4515803000c3c7c0340c01c0da00c456040b0003201c080d078802142c0ca8041e583c0311014461841c2c01220090800e1219a1504040c1701c080c510b2043c54503220007550 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 559598624 1250 559597374 559597387
    0x101d0a0602060405010f02031303050f0706140f0a051e0c09090103080703080912090603040203010b10020a1718010f02010609092001020615040e0f100e06011505041a 73
    0x190210096034050005030300018104000c1090a200305111b0384884c04045040d42041d15a41c180c0c0170782c11300c00909000b4000783e0301032100c10303007025156940e600c07a5041c82504041c510055424109695401d05c00c0145404141c9042240c011244600d00b00301c01041c610f610b2290b14200c80102914003003001404010340245d135128803001c94065401150403031b81d14601481c0091001c20003d00701d030354617000180902c1c064003400d02214900e400841d540c1c0c3c0c0b2074480303000003030040c004211507a5208a05d0484a0019a0085003044c280c0e80511a41030500410303078510811485030080c01d22410001102d840001c3d170103001400a11801d80c4000203c07941c40c1d00300481283c0300c0d81d01c160f441e40004094003680c0010402030024166081c8058071190a045600340614211105000c3c441c0f82c488030202d200e0242003210290301051081205c20000b01e2803c20401458a80d41070344503805401d0000c180c19035080c850489000f240c2d90f130b29240a1a00c10000040601c42503c0c036800803082100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 559599874 1250 559598624 559598629
    0xc11011d030708030406110703050601060c02010e0924010e09010b0304030504090f09060e0102211320120a0f060f0e0a0c08100c0905040515030a12030c080105101d 72
    0x1c0c1c0260894034001c0d517031581030000140540c18144140552079200384800e10000d400860010304441260600340c107280800d1005032440891944039a4000c207104040140f02040701480181c4142c04840181c0c446905500449581426101c100c1d0445c2e0b0440040050041f200c00031070303002c0c3c001d19080f410107403604c01c2c820544d0880116110059101d031521001e118140c8584154040550001c45c03030110700d000031900349550000c15480280703030480013610040712a0020910290301c43c2d04a400c00c0c13441c1020421070035004400740e0080a44140341d056948002800c404000d81200010301e8420380c43d40e40341c0240030840442103203103403200c0480e40c01c094100710085400e0300c91088104041e040040141c038000018000000c0c0d0340c10700903c000926000008071040d0f074420f450100303035592441c8815030b44089941d9a550144540300b9103000b8407100c052800c0d00e04410765401c0c4102800c40c10100c40c1800700b070240a41c040c00c194403e1304028001c8100c9000050703034000b614414400c4500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 559601124 1250 559599874 559599883
    0x304120c0218040b060904031e1202040f0e0108060105030a2004060305060604050a05150402390106080c091f0f061101110f07141614100c11011d03 65
    0x1c208801d42c4260306100030010b00d0760920ba0320180642e00d0a1076440d00ba00c00500c041a051405002000c00c011b04e1a5400d114140a40c5001c0d1100380941d0ba80780e4071143e5403c1e64103548245501c44a000c000400c132840c01007074850407030340e000b0014a0441000e4403002c69900032001c2e05c405844c520381d00c090320b41e112406904011402000030700144e280c59005d2106444008102c184854507110400c0000706840748507000b004000d840040c0c03200080142e02d4145042600544840d51609074200320150302d41000c07400500204000f4804a0340d0b5001050b569941440340c0750740b20303000c0700004021080701c44000c00728003020f030342c40b40801d607691180d525a6041d039042070b800201c1c1d42000d86542042400780360428480341340e6a525008600d10b100302e490060072401043e07070a140003c0c50300400d003001821444002212080c0c601643c03109541d101203000725049004940003801d20340c0c01800b4100c0501240c0d080842c2142820a4500441c0c20380b40304030545204100a2081c90f016890820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 559602374 1250 559601124 559601149
    0x200a050d0c0804051903080c160c090b130c0807120906060308030a0b150406030507111006030b0a0504022209060203180c060705030a0e27040c09060b0304120c02 71
    0x7101c011282c2003e040090030100c5c561402085030a08911000c0001c0c0e1006046902079020445641c4515180c06d5442d01a801054050300e0401c0611000c600f03080030fa81300889840c07040301c01610fa8401803594030706030f8242800c00340105200d440000c10481c01a03030655a40e0700d995600240c419081d554440c11500240c006a40001c0044204000c00301d4030b20500840c400200c40710540b02c1c280c40c2c060b034100e10a6019010030035840c3c0d0085401741380900081d0f48243e44800c141d981040184491200815640c441a81d003840308030b021482d1801244200341c05540c014041b44a890441c8103002d80c405043c0a070001000d40e2401d44101240d002e02c05075004080b4280460100c01400c0e4101707260040c0c0c40015403140004018103000030f00004100e8020042d00d003000c0791029400d00c00104c0d10058040c3c400e008000700903105074281000006035108074481d43c0303110b000549402c0e1203000c42c0e646010b07208014200f08007081c0421480103480c1c000c1c002e10f142c0418408816030114130f0000961 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 559603624 1250 559602374 559602377
    0x105071e1b05060702130e01020c06090a0615051c0201050903031303050c0301020c030d0e0118060f0c020606060703080603032b06050f0906010305040507030516060e04200a050d0c 79
    0x71000350790314160420180000d060890b03000c3e0810000790002550a20101001d0010540d00c0015100811080d01528403020780b00003628034a140ca1180070f51110b0b1001021100c0342d10f40030070404c900908051410130303200e02500d9545500505843d0700091038040394240d0501c54140001c0d45199010002002501150055203042500d0340c64010321b80014480c10364481d0740107008601ca801c0001043d1035000205040100e4100182d2100500402d0030182c1e0344190000031005030240000c076005000740700210402042110402d140880e00e80380260b40c0a5800b050030450000803e2046104035080381c0020180c914000d0141d20484503145131030701307201150601040326004001148a8940103200588a07119100c207240c0004110000c018010b03418555940c02090500c241000301d43c3c0910b03440412500010b10301d5100c8105090306126a0000480c07011526055040c240540303034445050a8002074101c00d0090420070f103070001c1407524204503091040210660031801540043c2455 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 559604874 1250 559603624 559603643
    0x90e0304060207090e061f050d0605060f010c0203210f0a0f020f0c06030c0307110d0305090c0a030c03230304030b060a120209070516140705012c0105071e 68
    0x401c1c90103820001c0340e0b40316129041c80c3c140c1401c585c250104285074084203c904101024908001803c10241181c2040b50015092a140d004010380b59000394002d990407184941c000c401038004440351000c10300300a40540240d404400d01c80a1211060411004d41004034100045000c044140d40c0200c10b9480001c0c0340100a005920303018080c140d400c40010014015544821010410710310000d043c04074650000000105610b202d0600300b5008007580c01600d4080d40c0b0000001c2c058070050314031007014020b0300000743e214034000b4007030000c0380d07407040306000742c1865601c1c0c08035030151031400c2c950449004d022a104d2000d051000b000550320500c1c4c4146641003440510022081c0c0d5000075480c0c074080040c0c0c2c00035070365030160941c0c000076510b03000c2c0c0d8503010784042040042001c80c004094004155080c10a1840031480c4000e41c1c4081c2d82d000c50342140d816aa081510040080a41d90303800c5801041c0d06520980040c0305248c02445c5c018401d29421b00c0038504110405c05c260b50001170f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 559606124 1250 559604874 559604879
    0x515040302210712080405090a0b0406050a301e06050c0a120f020d1401090b01020610090506011815031a030d030f1b020f0105160c02010e0a090e0304 66
    0x28040003050084181c5112208280d00810030b50340d560b83c890080e80340501440500004102503030040b17502400c800340005c240e13401c05400764000360005960483c03041e420080b020999050401c0d1401c01c99102110160040d040704140c0c0b49540c040c404494105a800da0b00d02001c9546010200200b540e0a00020080260703030800c0c2080310b80240c00c80024400421189024950040c00e0310300602c1004000182c103100691040024880e40003040059410b104980302c1e546001d00450f41229640c46c003d1000c698928012a20703007001300c81c2103500700075405060004d0180b80d030040d5030102060510440c824800103261012180366030148003070740c0f50f07501001540c580c03602403010b10701407411840010164550001e5164100d000c0f03000304241e0790b07840c13803906504507400100d070a0400c0106869020134015000b074880407941305242c0c4560030030003c01e94000c69000303222032074202c4d9564459000700780d40c01129080d42100b00e55520416880b0081515121032180c080300d41c164000031a0348a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 559607374 1250 559606124 559606129
    0x10082e0f1b0801080606130e1501090c09300f020301110d0c090e181009031806080405070302061803071403101112040c170607080f0405120903070515040302 69
    0x91058000c03103440d42040040c404103071108041c07440022a030403404141008141c0b0328503e27100711283c0c021002040b010001501d0801035000c0b03001c030786280ea02ca03d40c1a488409000c1c44101c0601c902840e030440f040324036a1700d1500390120700c0a6201e002c0c2407000e1661900000d00351414040c514200700700005a07220455841d00c42c00200c2683c9041052465251944c3d880304050300920071908080d0807400c0700e801c6079061200d581d05030400c4600308020f14140c10020030310384240c05107074250301c100c0c500420014018020389202e00e62010042c030509085900b40613650301712000a1485800b104556001683d045c090300c400b83c10b14181360820703000c1c18810140b070600e01005200700c5518003500071456040b501c08031032501c540034545213115143c5180007005030000c2d43c0b00da1582c45044c003010344058004500240512120340d1800c400b074841201c0306800800540d0f0041881d40181c0d280a01204a040541044030300202502c80c055034680c007140083d51020618141101e0006040c800c61 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 559608624 1250 559607374 559607387
    0x302031005270702070e040807052803030b06041815171b011103030705030a1a010507020108180706030203040605090d230417030310082e0f1b 63
    0x1d040455100c21100902e81e0714106042001c2040300031100e00340c00240e030207402008010004d010b10f070720f03031205860107040c1544ca603041160304403124050000700c07200213003400090214402c0103402a40c1041c841c1d40d0158001c082d0380582e140c00c4034080c03100103420b105582c2d0610310300c1020240480c4405002d20002005074642d0810005030781c540c0c00c1d4048103180043c0e5121a85541e44100003409900c6006880700d41c0c0803a0b14100c0c5110000412100300d1f8800007550241801c1751060080b8603a9540c00180d01c900c1b6001c8500003041072003040d01543c811030301039401a85800314180c80c440484070303090411003940c10020103e500007082c007041192904c80c80f5404100300c0090241ea00c512540107103600c0210525660480740351000340000c682d600111170041c098004501d01c0e052210150503182d130400c66100c03103602e0305007100194018004c148940c0b0030700c1c008140502400c0c0c06a0340d8210b4080320040301e001c56580c0c8540c1646254030720425851401c0c001c1c074040c90410103074008015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 559609874 1250 559608624 559608629
    0x4031e02010b04061a1206281d0103020105121902040b0406090e0f01060c050c04020d0b0f090c09121e06060a090905030f0a11070311101b17040b0a03020310 69
    0x1074542e007082c91102080d103001761010000007054401c80307911036500180741060310741c10112103a050001882030074026060b2203003c461508103510009d80c8512018908040c0910003c2d0104400300200440c901c0c0b1008419807200b1224480d0f160000800090380c02c903000b0b500b02022840000400f8041d0340d070030425102c01060f58002e00c41051410020101c0111030600c00c200600c2041000b41c000c022060203080f1012101810840d12403070394048240c0506a54040a8000c0481c100526810709045204500c24402c030b407a00f52034490074005008000485003000503007070040440344030000b4071742e4003402d03030140700400113120b141442001c001821f266175000c00301d5186014070400000c0d1000c81a1a4120303c0c045441e43ca401a0038002d4445400070300000c5101d00034514040308101804080851000098455100c460340402c0291402c007044641389064035090728080c00001c400355035070040e0540e06c2482909260340c07030103000410f412005150010a4003c420024002d6504422400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 559611124 1250 559609874 559609889
    0x5031918032109020604120804121b08010b0f09090a0812010905060604080601030f0602070b070906030507020118020d0302030c03030a090510050c07200a06050c07080f1504031e02010b0406 83
    0x20342443d43c00280c1610540c85a02c40381c03c01c91f2114814058508159001000e00c204054052a004e2814255110a070303503120085114011001ca1007120500c40d148a6550141140552924035002c111a1020040117054503200345d00554002607040c001400b021b2402c3d0080050350350400340c031001611401402c090160506220410243c40001405411640c1040702d00400c0c45980c14003501921403003102070000071490090202e6541d0103805c007012207850356410401c83c1c403a604100d0070390f450302d45204a09840103600c40050705c2c0c060340c00c00c0c265220b4011207192810361000c0034115002121a440f8842e40c80d251719092010601c242040c07440354000800c40c610f000480401280181038001e4100010130200b1410301c0040d001c8000d0445008084080140e5201e030b000742070341e0007005110028042d4250028408000150a512545800018060b10030035030200c0c420180b4000e006908008441d0b10414444a999a10824824269001003510000c10003808103039012540b1052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 559612374 1250 559611124 559611131
    0x601020a02010503010b13030618060501090614040b1f0f0210050708070807110106290901020706270308030f090705090718260f0d050319180321 64
    0x40c0140c0e03000341101c1c10b461003014801e449140004041604000369080141120318001000820007000c0507005101803060009103d56030b260000d1038180c0b4030303501c00c1c0501c1c94074650b00c0700e81d185499000754001e140058201c5040d40407540c0c4201e030120707414083d60301041048140340030042e4144082c91410794000000e001c1800c0ca000c00600e01d490050a0004100d101d6011807101889044200407a229140084c04580e8079825a4560001a074407100315004c155615460040302c802d06503046030394141c000d01401481d2000a4400344c00040e0482d400103402c00d0707000000f0071041c035410061401803501a8803480c0c0103c0c0551140380280002503680e001150401c4190f07070b01002d042d4080c2507498103840d80071070340400715440391654002c0900403641c50800c1c000d51841085c42c142c484401130403140b422183c010825220b81940ca6264001003040000400202e901d05030f00d4221010a040010901050f08085448804900c01140028a01d14403440040b17081d404800300010385d040d080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 559613624 1250 559612374 559612393
    0xc0602100e030304030e03031c050a06230d0311010507030516021603140708030c0105100b0a0206010524070b07020c040c08011203110f010b042702040b030c1503040605060102 77
    0x70307556408010401020070400905842e850344052054841c00c180543c1102240034111b10f81c2005888225002000a840c02800261a560304e144014424004c06804035606041e40103200c1e07003100e940000e8040c001c108403840b00c0c54100f44643c074403c02d41681c0001da1418101e6080d441705500c01c48290441d402902c41c0450780348440a24012030b03a03c0060326501003200d02460f803c0800c40d5000501d80e003c0415540c10300c520640140348038218113102481d03015101c90022101d03020f01c032443e10040cad03c07450043c00682045c0302003285004d40243c0d48a034000c80d18541da072442d07005100840c3c2c281801c0307051080e01501000100030311041120b00780010036216600400e5040d052040340380342e00101c0500c138103041c01283d0707550012400c1c0064071119010000d07150b001e07154040251740540c0c13500d00b400f1000030001584080c10654807a1641c00c034040e6800b000b001e46001031665916000f401140b0b8000c3d41c41c0c0c18294641e840581038142c03030f4541402d15008072440105018195048610349 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 559614874 1250 559613624 559613651
    0x20307030f0b01060e0f240a0e0a08120f07050a12050a12050c0d1104050a08030301060908010507080a0905070e1305060604020a1e02070b0a03091b081c02010f090c060210 75
    0x6a640754420380b010110b09026444000030440c15050f1003e0003540003c04902c030941c080d0340108801d6003994ac079404981d031004130f603603114888401c0400840060081d0f42036040d14900800701540104200c4d10605140e0b15515006c07900194000d010690010b6080d5000b070b0483c090700069000004108114a40680107002501c901ca1748140c000c0d954088444641c07460f041601c02400340582108070850b124107042e0380e240c2c028010320300400d0300e40340700043d4032205000340d0b0300c82d02550340c4105054a5110072403000e014031080c21900f82c0160040031558550204140c0d10580c1c20741899072400b203150130701d9030910300003810050003240104520300c1d00d00c1d0410704a5040d4049149615155800d1031012410300c000c2c0e0b00b080e0000d4600080407a00194190414003040c0c0c01904180c420700880070200e428a0520301c61080c03190041c0300c081c1c081c54030180c880a14109075000200385150040c40b514202c03042c0c084100c48100c443d0707a0070700640d80c2c1000f009500c5000d01f20104091805000e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 559616124 1250 559614874 559614889
    0x90609070311151201080d02100b151c0f0f110c2116050309090105011707030e010b0a09020d050f010308070809040b1207061d010504030b090109020307030f0b01060e 73
    0x15014002c3c2c0c04a6034040540c200001180d0500300940140d02c1c003035840300402a00d400b0564104001803140d050507034058a0700784104144150010711450a449852400a80d260005101c64000300310000189c154604280507003002c003251041c0000d82041c10701c0c6403804451000d4460890314005120f40c6a01044c00039244031070881801c2e9040d81c0045a44000c0c1d8039114110312004000e41c3e12a10340c0410070000003600c442c0000300da4042c001d0780c0b50f400444000b02c2c0c2e0f0ba0403031606190f200100700400d010342c1c0300d510190100700004c940c00082d88017107241c004544c1d1080006550004410039400d20602c80c5030341044000040c9a080e514540394008075002d040d10180504200103075002036035907079900000c8071142c00381903880c2c41c01c0c050104a460320840d00c101e1011030810b045c0c01d103030030781c1a090306e44488030140c45c2e013801c140c1036849911010784002d0a21748959a1644007d026940402280000314441c0b02c41c28242c0a403880e040d40d400c14180e02031002c0c0300201362200c1095940c9078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 559617374 1250 559616124 559616153
    0x2d0905041110030606030b2205040203012301050a0603150614070b240604060215040c0b270108060a0302040c0e0a150806030c182d0906090703 63
    0x1404659034549041812107401545811640014041e02411505802d60451401c90b046078404100c241540810320405000800a40201044143e4241c900e101980e204c0d5400c280090000101d00f4407013000d00c02940c1086001074503401b140f1004205a24052a441e0041c1046140c140102c2d101c0c0d11100120f450303240228810b01c01011505042042800e0035030704039507000f44410720b490410408030300d00c0842c448511054a81495404000c5003400003c0301d044900e00c5c4c1c000c04018540a0b60000c80010213801200d039500c1201e00011140410006003201d40006c42903500030765818001191411800041b85040c001c1d1042040025995140400c007240c0e0161404164188250301c08c41e003442d0b40014860740309903075107030200309080103031a10988007405071a80d001d2620707400704051b89d41034200e24055100300ca4141e50208002c4842c2c943d604112015010310064001c01410722860702521040e80295044404100e81100d08014860b0450000c001401c500344c116141d406605c92880c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 559618624 1250 559617374 559617389
    0xc090708070c080a050a020c0d0b0112020607021008180d0212030a0212190621080a021e01020702100503072a061803200d0806010c0206030a05012d 65
    0x40001a000902030007445065a0b0311400e144e40da0b040c00d1901404a401c5081c2007801407041031801c40d00c130b040442c2c0a44e9002d811440c1200f103a813a1078458290440101c0c1c2c00c98000d50240b11748401600ca0744002107403c2c01c0350701d034400b0525040c6c0e10001f060140c0c5040a90700c0e800b45000358a001e80101d43d4490310301310300c150b00380d80e42e84802d0034070064482c4501e13001070844038a0403c0064461666421411260a00b0500040d56680b24640d06841900b1100748010040c03401103000403141002401d500480f070040e6a61941d208a864400100c442e50b10302c42a50005001c500b1403414006011002041e42015415403c1c641d200818200d104e500d80384a03401e10950390b00c41c44010610715820150b108009000b24500c10302c51200500001d142100881c4052a881c19a02c24400100321580e200500820744459040d01c00c84032200301501e19810300505d043d80302e0150b03c3d0400250700c81c101440c8003069951401b0006942c800e0302e900d10b89103002500d164050150760040003502201d400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 559619874 1250 559618624 559618637
    0x4080a0306080f0609010e0d1407140a060603021c0b0f0406200714010c170705040308160201081b220509041407050d08030f04060906020d0b120c0907 66
    0x10404180c00410a03600220780c203100d03a01c1c0c60414035800003800361044044000030300034031a031000e4940e50b07441c0c04040d1a0105410807060103001104001600019002381c11140d401280c085809082000e4201d096a880b41c88140500942c10001c0c3c10300d041442034080f10000b2940c948417108045406400310408554410202e010701aa45c1c00240780c2603000c125011540031246404e4980fa40000c100702d8614014440074070b8009030610820441d00c0990311481d140d0200c81c24a0030305458010510014003800b480b010020076205809008203140309604154609900d00015002940c010180394001889221421201003042d0540341c00051600c0c00b182c1c40c81d211003145180081c0303600000d0700280c0c99000c000502000c10040d0b0045202c075401d8a42030307900d4a080c00304000c00d00102034000041000890303459511880882da00130700031140020100b442c2e40d00c800030303640841da42c003240355122038241c1c4c0b281c506501004070f500203400082c04410b101d00045201508d0003000ca4007072204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 559621124 1250 559619874 559619887
    0x405070f14120c100309030909050105030607050f040905070e01031401050604090e071205060106081f140d0215030108100612480b03100b1c0509060403030b180408 72
    0xc110124982d040208113541000340f0710001001092203030000d40003c1c5160700c00050340319035403187c281640d5004c0d01601d1035540d041000e840d5036201c5d001c000140301c02000002083d006c21310400c3d004000594400031031043c0c40f000101541e1801d0181d510745540782004101c1e80c4da40c1800c40b01101e07800580461000c4900d4101030401d216644564001204440a1400c020f030108800341686d1007501d0744042030f1100190144034800d218a044011301e401c41092081d0020030912401d1038200030305444914085134017141c80115450a1110030010100042c81070a40a000003000302d1400e00007000000c3c500b801c1143c02c03011101001d0700f02d080502c614100d024500c0b01311840781030100d0203a001012400e4110007500d04c00e001011541c16115004949280d07000c048034010314030180040c22031400c0000018065001c402007000481501d110144130340300714090203100b030305ca04024090710700d45801c02030251000502000d21500f003000080342808a24040242c100750410002d42e291507 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 559622374 1250 559621124 559621159
    0x1a0d060c0e040203250f02250302100807090b0703090b0a26040203011d0c30100b010e03030d020f04050d0b07030b061608070503130e0405070f14 64
    0x440c08078090b0070900000420040581c0c007001120a50000d00b80244081c4041204998022401e100000160003607100b21206040042041201004500701005c80741c1c2c0e00d41c0060701109140d40081c001c40d2886007000842078000c90341d5802810000e601d00e2070300000e503a0061041059004141c5040b0303012a6450b0454072401c2ca0700c0d40c072a500c80423410004c0d0241041100d015048400700d10a40c20400900c0c08602080c0c190002e88120300c0003072409a0301081040a03010032200d040341c00150701d401c824031441d094294460f0460203400a41002034140a880c070a9444d46081070f81804000320790260720b03481c000107e821880c4074180c0140c50341514801b191082c8a180c1c01241d10000d240c0004091143c0300005a010b11180c2e102001920100da05202d80303405224500b850200a1040140c0440c9040b4001d0911610038015207140801a2514402950740c1e41c22180b00507603100308020400c13008100c1840076001c51181001c1d07403031400b941d981613002c41e1044140242c040f0b414202111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 559623624 1250 559622374 559622387
    0xf090a030c0618141006030312050a093503010e0403052d0306032505010c020f06040603060e0903040807170102130603051504050f06010318140307061a0d060c 70
    0xc00d6071081505200341810418400e81340072020340880d014400d4020071020041c030a01c0304895041d10713440c045400300700101e03000385001050220040e488080030000101012002d440381a1122002080c05040c040d40c90410400c90300f100544030030070001400b52081c80520998010b9051810540d07030b06c0719860180800f881605814000d001c5c805041c202c00315000c0195120b003406404580c1c060300400c02010110459080e01c801540307080c1d0083c400d07544a0807689500c140080e00b045001c1400c07001152160b40607503c10360001c0d0350340405002002c410340203d41c200351038800440c03c0074206884151102268030a08014103c42e00d0940700103902034041c0c402121010040c084805d42c0c50201402801d800c485403da01d000c2483c80c01000c1c0b90600c690341c000c0c101d03212440740e04c0e51181e00541c0104034154210b008011100d08a6000403103582c01c41c502008040095511030f00c01b46000f030151542c040a0340040d140310310805a8a84405040b0b080c076a030840000715200308205410341c0c55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 559624874 1250 559623624 559623641
    0x1202040e0a12050403060c0206071706040908130f0512060106081305011e15060203030f040c05060a260708130201050d24050105070c03060b04060f06020f060f090a030c06 75
    0x340d0040c04015030f9000300103402142d02640c1c052040c4c1c040d4101c08c0303868610885a0001081c82c032903454035081e000118480d8802009440003414050325110302c9090703004086c00c5144c6002501081c032a0714080f40c80e0f080205810341d54501c4a81c2081c0115407500414055041002802400140548481d001303c05285400c40020001c60350000b508010f1800c10803d80c010041c18100c410034004007414040f400c489907903010b1070a646070074803c8070100001900544000f105801c01007103a80c0c40c40e00400460800d0344680300c4070714550101500300c0303024012000041c0a0f95003000340140e00300c204550321200c10601040c007256207100585117402412540762546140600c03590014014440e072041000d0b1506029000c295100700451b42440313800740003408080317515020000180c580d0082c00e03038a000248080750302e03a2aa00c8800410302c540d4400b1006034080412180a0402405240c0d001003542c0c00c100d07054640880102d40d29004028000c0800280441600511081d54007a008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 559626124 1250 559624874 559624883
    0x301060e04150b12030a0e0a090e2401030f0803090a061b110a08040e04080f03040b040318050120010212040807020a09020c0606061b1f0c03061202040e0a 68
    0xc6a0400742008620103002d44003075400c0600e8802c0c401c001e460150504050907010000030351406075510001c0716000f6840200d00d4200f07075299008500075038a406200c290581403001404041e07100219008440388400304020042180801030000c00d6041d0742d285c01150b080150b19550f6152800100e25005d2252005000c184c41e0030049504040c0403400c1c480b00c2d18140e981c800d03006100c84805030300c0720074901c80180b00707500412081003a003a8560032160300501441c441820a910214403d00c0f562089130129000500901000205600541d02e21100001c65a00340d401c0b0f0700300740001e0822030480c00f016a1040442640030070100c4250100c80e043c000d03801c1c400d070b95802c0c185400c4480d40c20a40040740b041080e41c90101d6071401c0e91003a10304141e8007400808503030312007000740640c0b0f03440b010170100c0c0f450489031060300341c1008103c8030b96000c001039100d4035106420800c6200b220124808903003094203120701002030141d99840310b0a5650100d6001843d001000700d128503000302c0d01d80060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 559627374 1250 559626124 559626149
    0x10e0405010b03070906020c100f05130e071214010504020d021b011406031c0c140f0703021f080a020c071503090203060a0b21071e031a040b0c0702030106 68
    0x4929842e540594080e60741c64644010705512080240e840c0c000d29034040e0f4001041b181d50145c40341c4205040c0308284a6410701625200c031080255440580940001801003010343c203100300180d01001c4d8001c00074600c4401c00820749000003c0380c1044c4103200702c9200c1da802281d00f0801c00311a50440d8800080d40780300d41000e992102d50b050180c507111403d600302c0940c01c2c00182442c100424040d608403080303800100040f49200041c2d6000c00b0b080425503200d0460450642003850800201940044050007000c06528500c108082210150300300ea401c492980e0a540d06250403c2c003007508113140800c0540c40c0c0040300495440c0030950342c051000c50300d04600b2030529039019840310030954003e80070f940583d503030b94440070183e6014150050300321a109008180155501d04140c141c000d035401a81c01a664691142a11500e41300040c3c82413035071701d6000c0081250307042d140c0282285020001d8603616060720f480812040060805c0307180000006c102e81155402c0d80304030041c140101400c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 559628624 1250 559627374 559627379
    0x1202070513050a05060111060106030f0b060a0305090607050c07091109042301090603020a0b091915020609010c05070f1e060e060a0506030c1309152901120209010e040501 75
    0x1540544015030f10510050300e03020204446510800030403405c5040700b0000e080d1a4603040045000702404c17402c004074281d48501d0404a135440c4c1d0000d100002e1542da0100d1a41022036051781094006003802e4140700040000f00406d1001050030790850b2990000055856548440385040d48544031603550311610706115140440008020b40000214940c00040c03642e8880344503808640341800007030f51085078035604201103207401000340144036005d41001c0d072028081c3d07003030b21900600d90800007600c0d1540381d040c0e64040d0704104280d071005100d00240b00070104054080c0c0a0303c5061001b414018809500005100b9182a06500c501040151a42210721400e004004082c2c00704591204d01400d0701103100a45240141405654010041c040034120942044101d0400603002443c0176110b4002c00041045050311003045854204082542e10000f030704460250000d543d2262450742c1140c40242590303000d2f000c849000070b28a40183c2c0c410380c40006a4120301c000340c486a2150500001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 559629874 1250 559628624 559628659
    0xf020703062429030c0919140a0302091f03120206163914030d0b15220503010e0d0e2e091e0302010813050a12020705 52
    0x3618501d5001142e00140192a14090080042c0741c0111407032418645503540c407020780c09070056401455a00380c8515004d480300118515005001d800984134400c424100004035070f1010703240b444c150445441c0781281c21540040c14519015181c0d059100701e05044200c1c120110340414003840c0c00c006104825844640c0c000d40e1034000301d603505540992485400303a060b0040b215103284002d0b180c001001c2041c1110010388080c04c3c0e1103481c3c02240c0603014040801d5030302036828403000c1340782c000c1e41e80e030f0246a88035030503944002c900d240070303490351000c80e07082060440a485041c45211019508103c024505d044080c29503040160315502e080700c44040c0c0f0b440020f400740d145026031280204001c5541c10840030640d0a06030700060008090601c1d81c01a1011041107a041c550400f01d402c5c0351618810710071000007508450f00012841d90910035580c0004080e0760007401d8030100c6041c8030480e40d03403945070144844003c0130150805d0480d10001c0c020701290001c0e0501070060701110420030704 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 559631124 1250 559629874 559629911
    0x30e0a0f05120304081206040204050a060c06050c040e01090509011416030e07050f15070f0b0a050604180f020a03050f010f0b0405010506090909030d0906020c010c1e0f02070306 78
    0x400722214420085a8401090440c00b50b070300c616042814036050115098804a20790740060100c0d0340280c0c200004901c5941d4582d4000240c5150307503c410100304549418001c403040178181ca840244e00388030402c0030700b01142c040e0341034a0342c206010409440d01242d46000d84980c014040c4c140d080d020411240a0f0010001c058000341550140310092603070140588659450040da80c105130121030400c058245500070062207451151820700e070000940321605d82082c543c800300c2e031a00402c070600192103018012550000001c070350410008111400d09004410842e1000b46081c0721080300764103664483d60088000e507080000d941c2c40c8000350340c0300c0d8020890301d0001d1000910305460300e800c43c10144070f2207042c1c0d400984424030b0114400100400503000420000080c402004140708040f440d0060f80c149030300ca90009600e403d18880700e107080d604183c80d89003c03c0070300c5007150441107042400071000c0101d410702c2141903401d88d10072402c10180d500054212824903150408212140e00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 559632374 1250 559631124 559631153
    0x1005070b040b061305070233090717060601050901030b030102090a06030f0606030e15040804090c050d050c03040b0402150702030f0c1f050409050c07140114010b130306020a030e0a 79
    0x450700c0c051552130a041008450702562000e0050f4403032510f803845401e400248184131038a040c00c9515581840c41c8846c05000110340c9503400b900180c8040108000707020b070301d005000035440500400e142200008215000b04021181055100c0e000030060f905c0a504503440900e0140080c00c9094403450041c000c0d100c60320420420b50310741880003800521911425201c000008060402060050204002103802600c00e5980c03a4082000050010251007038007080714080e00d0703654642c0e44c1c0c45088402c44d107000740700b108507940400c204800203402d403008645c4554112080060181418070f100c40034001c3e01c4009401d4400c003885203249400000d00040804c8080351885550a90b40079005003070307591105000040b90007800240a550f00c1030b00001d600c1030040b48003d0a1450640f92280c0032021303080c070855540d41d12008260440b021111440c00b521414036414608400403168031003a900900c0040c00280e40440c0f85040c4070321a4106040b000c1c0150115020b54000742014000c1000d510f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 559633624 1250 559632374 559632379
    0x150d0506010e061608030a02040e0717070e01080414210d0c09051e1f0521010602121e03090607080112150b0d0219060212090a051005070b040b06 64
    0x200c500c1c1056290800484102d50701404c80d024074aa22503031800c1d080d42014040010042d000e104c00700e40ca482c82c00441c3d1040320141d881220002012350140c0e4141c84c003801d180d04205500000100c5a41c00004003a00541d00c200c085900012640308242400c030106010289042e0050007001d0400c088005441035185901c401c0204504484003503030590200e10520303400c071088078010714904000b80f1003107030713005400b4046210084844002d0010720f2101c4014102203000491440022484101100d03280206141821141e504005020f9560417543c8100207484000040c0100d00c001035407409544181d1580403d500c038102424002d840b040108d070143c00040c4018000100100d80c0707003540c0001a040501402100080c0e8100c0016000c02600303190030010460002c00140c079580c0100f4501e454016040b8503a606080c002820103c461006200c031400038003140c9003e6590309208000c4130801c94403841aa280c01d041610b144c010060003810400c100c50800c000c1c40020a269132248408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 559634874 1250 559633624 559633637
    0x20105102c0a0906110c07031707050312040b06040902061b01060b030109020702010f090e0c070311340b0f030601020709020f070c0611060c0f070c081b01020f0c040506150d050601 79
    0x5441c2108814001e10f06d110049038010f11080000c1000802d284056806100d00c8601d05440b5484107480c1d98483c41c0340d40c00c84850301c01040240102e10500700c1d00000c0840b42407001005039000078481d40102201c4c021064055684040c205601354444002428981c0c8115100d69456032400001d4000841c241d004c00d094000710010980f280340042d0543e00410150203482d01c2c2d10030032a049400801c411003d100000d410a8030840081105512103401500701030551103031010b0f040c0e4200d4207160080726280c00c150007032040b0140340b001d4403189802ea0006a0301d81e620600109d14000e4240e0003006001d100240e11409890600c0042841e2030141c0035500f1080d41e1114100d902c100011042c04a58016102203002c00e00180002d00803502c8114049040c4012a200d004100065a00a00e0594811590301d4a0035042441d00e200070b501c240090410381008003a826211118540d00901c9203980e071001681b150f880307522403420b00640203c1c044d1074070040c150b007a0003040240c1f405404990f0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 559636124 1250 559634874 559634891
    0xd0b13020a0e0115050a0e1e0a050301020f070f1a0f040c0b0c0316030509041410090e15041505070302030601110705060d02030a0204030b09150601020105102c0a0906 73
    0x71000340d541d040380e0307000500c13a104181c00315003240c854001d003d0200405c802041945440d0740c8503980301c500c4544900a14941e020804e04001650b84660b10042c0240d00512041c0c00c40c0c0001c80c2500c0c48541c00c0801c02641c0c055a1804110b401c40e5441c144500c88c0e190301c140000d414602c0f00080c0701e640f0429400f0300c17880d110b0120b0005402645521442c5034003c01014404019400d202c2d101c0922a00300241011504000641500c2c42078080140c20000c5408100100301c0c10400c0f10700800800303034200100c401c41b0480640f500102150000f22031540c40c0490100800d2041003248580d100c1000c0202d41402c1c0302c02030280d4000e445140c0041c0c2082001c0308411804600711040b40d00062009240024445030321001e504000d108000701a82030000001140fa404101842504420003030240d000202038549074031a40500340c40e045a00d048100100140300c0c0c612602501c16440c168100e1002070f1202c1c001c2014000440c0c210b0151035400d0041490070ba8003c5051544141c000b0b004168 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 559637374 1250 559636124 559636139
    0xf0403030c230c0c120c0f040b06040b1c09060e16060210180c03030504050315040c0b1b07030606080708061e1008190309080a02010c110d0b13020a 65
    0x20b018585098086819502c00a00700c8400c00080003e9030005058603244840c40c1c002404613420503003080b0b156045401d0b41c840034500300314011801c21044404104003034504000c01d075207000d54001e803810804c00245401030080700a1140d1490042000240174000b440e141231030140a44102640c9180314080d01072041007106400101501c0382d507401809050031a104c0d6a025004075114070100032110740280700440c1c010000040034500035207501c0d607524500b80070b151520300d194001c0c4a440400300c05000010306a102860110780b00744400340d489810034051250080b0000070248014070400000004000706a003082d811038008074203a41c54295a200025100c0c1001c44480700050781a46020402d03401260031507801a00c006400b1b00a140c42d130304410701d00016500d8858104000d0380c1410700b0103506c4200080034101c0f400140051020a50010b07282246100c00204032103c00840d082d02921821b03008080150030005200140c10610302c3c0d0381e0442c0c0544010390140031902004280034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 559638624 1250 559637374 559637387
    0xa1a040b1012090519030e01110705040506131d010501050f011e0e06040b120709080c090a0b0a062606010c03120f0204060e01021005010605180307030501050f0403030c 74
    0x11100a070a07900c9041c800e03034080310b101d00300e48081625030782c3c0c0300d07450f40114004000c010301c108100c48100100b0396040c00d010300300e50440040c0c1410002129104040c0400106400d001c481080e00c0214140d20b80100061b0500120800b10048616000102d002d402c03442680c07150691031040204001d98944082c0144540d280c240e242c08134200f6904100703200024482000c07060118a4032100c81605000081d105500c19072103030200c007030301180500c101641220744642100b20f41c28410982440c06001a44480f40f001d1554850320660307001810b110005e0b08008003600e001862204119102c16010f40b00c600300d140c40400c1e08110030122400d05c00000480750042c0016140c0c1ca04068044c0d908482507880380d481c2c1c20713600d82c03544415030740d400c8a4000340010701000e803115074990b000340c000203140c107005010036a1094140340040043d40d8000d812103101c1d800f00c000c0c91400440328000300f0724004560348010076948c0b800007040380c015611240c09000300e100f0356090003003420f03014048484 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 559639874 1250 559638624 559638641
    0x120207151805060a171503030c030403030225150c0618030206061503060607060e060a05070e0a060503180106030c06020120040e010e0423070f06080c0706090f0501050a1a04 76
    0x8510b031040c0c0e9441d061000c0d2170403944103005c4070071401d040c0e407820b020a0464001c00350034080d95001013000d204042e01031044072007100c8020234603014110503c0101208012038420158460008480c68005601c2850301c42042508444240140d24214010000e0095055002d600600889001c21105c2c45e01c000003030304244030fa00d059410754584404100140d030249508540607036803075412103074022041c000544107403208000014a403801070741c064041c540c1a048144103645d460014000d5a800a094940129190802401c0545c140b2036007401803070190030142c90035090150014885505402071030748902e40940384181c2507040403015105000b24007410700c03640c040e0703001030044102103817001e83e1050180c0e140503c16142a038040d0740001c081078000f481e9401c80b4800f40107940c0c9000385800241410310b01103070145040c3c1840005070181110051409071102c511400380000c1e225a11360143c1c20000070060b070b04103040024001d000c42c240d50011880d030f054500b46585818801c11a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 559641124 1250 559639874 559639877
    0x607030e0106120308100905091005130b041e1406010f120302060a02030606040b0d05090f190b0406022b060b0f0a0305101203030b1201050405030403120207151805060a 74
    0x1152840f030b40e0152101d5400601081d249040004005580703545402107c0c004d401000c01b51030b40095001e45201910340041c0341945580d100d211000c0005c102c594a035a01c540c00c80042c03c0740d400250090240340e490200c001d40010205500d904280078042507190484c0c903102429940e040d950360011f0310000e400c18014001d42c01850000e0708004a5030000e55105000503d02490f00c0c1d101c954955880c1c0000c07040c08641ca50364810042d0800c0100580540c1072070110040480480401240c0c1c3e84070200a00145160890380c017007000c02a583e015529000c508103810f203c02c00814070303507250441d10210a04200c80c24010006005e6283c03404440e0000c0041c2816458100c0e140400e03006420f024105201456642d54002010090800401c40d454440c0e40c001c02c00b00080380c20406900381084000c070760340c0d2600c4140400130340004203c5084950041180307003100442d400036070400584e580420496518081c00300d40d010b5201103000c1011754100b41304183c8a48881c00e1006d540601c003000340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 559642374 1250 559641124 559641149
    0x904180515061906030207020f090603030d1a100f08060105030c090f01230711190e09030c1b011106070806120a060903320f09041506020607030e0106 66
    0x1508079992081c07036075101c100500340e44040034a01040d0f840303000c82036000703000113580480e001d0210300d0404038002c52080210741c4075000703092040000c4d0f03da03c100c1e214072704403503501c90751b007140420481c40c006410100100306a40ca142000009000d460b00315100e0000038100500049072503000d4803c0c3d9000718445032045081840d500107101e10f1603a01d0050309e051103104c18801c0b4108540030f512040c5210050f41254a51070710b4078000708501c0402d40e40354401c0c0d6101b80c055803d25203406041040f10040d504810950f00d030724a8040c1948940c09011900d0302419052085611070a001913407201000c0e61404000380c1c4489085407603040640302c2600160198020032503514080d441f00d18131541c4074003922041b10450b51038004440441504401103070887e0700142c000b200c0c0c1e00e600010300b000c410b00c4494410042648062511400780c14003410340b0041503a400740c0d1107562100c7c9a03003501c1c10351114400e4980c40040d5440c50101d030443d0000e42080e81e0551002c0d030602900f02160314007058171 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 559643624 1250 559642374 559642393
    0x110303070806120c0d05010e0f07030503092e0815090f060105030a0f0e060105030d08040809061c0f1d0703020d06410a05074109041805 60
    0x110100f181c1c82d2501952095010301155a030701d010030480518440c00002400a5020342c4c8507081c0005042003641c80e4208c0c207420070120304080210760004208445054a0f00000c60207051004400703c003250b10411102c0500000350780095459000d021400309100c00810b88108002e4030150455004a510101102140095001c0e001031604020500d4010403162100b643c290f049443c91894a2080d50014004103c64201401440f06104142c0f4080003149000d48a042d274510401c28418010b0000003102150303401c0c40511510504402001070160303104025999002d041d610040200d141601d1001e9050b15400103580d00c11240e002d00690390030207207600c90741c0c000c050720034a000320544a00070503040000c610342000703a1807950716004440c1d032961842c11484160010081c41302c1c1443c0c44284104d468014a280e8910441a141d08141c0840103400180c103200e07807016040f1600009004004451a55000d07102d006403c0c2c80400c150728100c1106103e14440b424090314981010510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 559644874 1250 559643624 559643629
    0xd080a0e0112090b1005042f090a0803033301030f060e190f0b0d08091306090212060901030305091908120c060708060303041e0509090d110303070806 66
    0xc05100d6441410a10150603429900d98141c51581000711180c520300c00c20040c10000c2c0c0182400134000599040190b1040c000c9018104a1a148a0b82c2c000a4213414001c101c3c1c0c001c0103e500444001c0e109010456651100c9503036170708141d07110780b80300e1000194410140759101017403c003644414103070500903021070300550007803550059240c49035880d05d0340480e11442008407e4010f1891080d00080c0c4030302a03c1c2071045a2001508040c1c00d400d007488101140d5506001c5140103400c00c2d0074030343c1d41c5089400122101e440e00c21040055081c014000360710740e495400741010101502d03000300590303a15010094042c0c806d020007404290103205090860a0841401a4aa91000007424016114400145003142ca0040000e0016000a000031007207014043d0503004291400c018a03e03007054030000782c42e80564018278680a0301121036403218141411640010000070304000350340e09200300c00945681004042c00c01040c0c0a0101000d12900007040f41e201d022603a581c03061648440c0f04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 559646124 1250 559644874 559644887
    0x6020a031b0c021e0a09020a08011503020c1f1410050f0307080a0b0c04080303090d17070c02101403101403160b031005220b01020d021c030e1b010206060d080a 70
    0x140c071601310300c2c2c85c0780c0410406590310081c4544001c03034a4003d0598074180142000524140c1d640d01014014012041c400e44001341c41c036403641200140c3c000006010040d50000e0015601c805110a40f00003400f103240d428901070f60a07030b1401d5074000d0740d00000d00141591a420780c4211030480c0c1c8204940d9005c6103029481941040480a60a28041e078400c030003451a04280d0b180c00c659080001200c0c00a901701520740580d941140310050039281602c8050026103161074064003405501607040c016078450012001502e1401c101c6035140d04181d101003104c00c245000b803030301c92108068031706650300e0001788961009404030207882c0004d0604001c444140c1024102560070030003844003081d42d5841c03954451080003003910801036100070300003505c2a5485a10800e05542000100b1019290301061503500e1000141d044060764118400440041030140401082400b8011401009052440300c007030314480242e0850310b15880c1c210401c074070311000c644c000784022410807030101640d000d0074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 559647374 1250 559646124 559646179
    0xe0d050a02100e090f01030b04030c0201091a03060307080606240909070309060c0905060d0e0a050a0312060807120b0709050a08010b12010203040506060111070306020a031b0c02 78
    0x28161a2400c0059001c24207401c601038150740828203c00c03030302143c0e041c10568241c0c80400910002c41551564603507407441c40c1c0150010b02004032124209080d640100a008003c0842450282305001e04e2003d6403100c0c1c2040d20001d120b40100000094006000928a40a154000c05040c520750200d050403070340f50105840750b4103001003800921200ea8850321071611914140d1000f00c0c40e0070403450488121581e10b204041400b040e55000c0c040b50300c0d07150030b507614014040030018011031030140d424944104082c0041180c410088041c00b05640800001d40d5180381d01d409000b1030b0f8a420302c03d07841d19424011014542269035204010800c0d0480ca0780d000300f52401c12403140b50f05c810100b061080940c00040760b5039103a80001d05039041c03a4102e80c031801415802181141050340d15282c440c0f4024054034100000c00da1080e18440041c0b00000086030b02074011561007102f4100500070f000c068030700000c8a00d49116043c485406080581e01c25039000307094000048440084005111030705 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 559648624 1250 559647374 559647383
    0xb010509090a170a260705090f0a06030b120715031a040c020d181202060708041205101a0306010b0307050d020d05090706260c070602030a150501030c0e0d 68
    0x21440400410394440ca100c0c810078042c2c03e469628020801c0140c200c0081440d10300d04c1c1d0400701d26201401c1d0509103000e4019280e442c10310fa0300c0005800007001e284400f070005610070085180007900580591241c51000c0068503007122000b0402c00c91500c0d20303158890940c0c41001503202d2900c3d644641c1c40615000715250700071154144081c01f040840c3c911001000240e4031001c2d1807d03c254000200142060f10901418015420094000085603070890028000c0c0c40204090f0100824002031720003516200c07d08030340011007420040d507258000040b0000071441c20301046139034400d50170300003001840134000307100c01c0e46070054031036561740020000e42c100881404541d840e000c50740018040d03801c1d17a40c0041031311304101034868127192f69580b000c02801a00c08a0030b501a80c5441d03e9500c065600303076161030340c0e5a541c07118019845000b5005250038800410008180c04541c0b03c05640711031211410b401e5511a0015802c988601d0030200208a61034940b001c00d10b440000680103a214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 559649874 1250 559648624 559648633
    0x30c0b072402190c051006050a05191d06040c0309081b1e010f0506060309120c010b0a09091103010b01020c0f0a0503010203040803090d0f0c060209011106010f08190b01050909 77
    0x903d20014a00d0301c2c10144080043c8110220205228040100b43d455500410b02045168a8800040e03034929581c4600c9000d5940d02e45884807100010b02e90000030010488010140c1d035405000d4800c4040441d0140d21581c030b8105a0f8040b41d100b4441d0a41040d071000f506407521800d5040904406030390030180704c8501c00e031460300e40d0400010000c0102e0380c0b018170010604c101810300000135108000c00c010b00800c014001c03c0b280c1e8100080240e030b038800001d11a9a24026040b001e400b506200710038a8000401c0b0400107183c3d09903911a0b4201400b034020b06200c603950300c0c01c00d401d075190034078158010380c04807950000310314146c1080d5116103001000403000c29074801c0440e081e41c100301c1d01902c00da1b034080200702d9a4a42440203481003003c80c075000c800e10032092406055190307001c2d80508480e502258901c00c40c2d000e14640c0c0101d01c80c0c281100c04943e034410480d01d001032a4043c2a03118011030741070700d014544000301288101d61060321f1505680c01c1c14107004048900900036001c902c035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 559651124 1250 559649874 559649887
    0x50105160c0308040b2808130c08010207030e090a0524040b04090302160b07050601030b0c09123306120a0813051807020d03020a0302090a0f030c0b072402 68
    0x41c030038003c10003400302c101c42581b070390840000801c407140a4900e0801c0c04042800007000140c3c00103a10342c1c800b00b51072142c460a40141407201e00000690000c82040d8400030b0f0107c00e140d040160140d000c071048441c09550341e26801c40c101a40d03001d840c060380e1010307200014440da03288802d114a001e4000303403001a44d581c15030000707000c2d42c044131070560150f000b00250100d00e00c1c0d000c1d4500040c054000886241c40540e545941c2c0d281014407000d00550301910101e0b403103041440440c2c036600c6d0000c00c0e0440349601ca040c0992202130035152041e80e2000a02600c583c4a5642e03409058045a03000d401007640c5c0d02c13024440d080380c01c0385070500b480c022420002c00241d51100500100754045903038914050400040c400d05002c400032001a1081540401100941c0010307aa07a5480c2c65260160b11a005480290042e028001000780d1240001d800894071421400c0e440040340d018404441040747d840301c0c0e5600074480c07003102409450340040d070498050381d8007041c0022602c070810300614010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 559652374 1250 559651124 559651133
    0x5070f320d050a05010f080a06180b070908060a15050609151801031107120c0c0f08030c0d03090b0109051302060304060506090c190e030f1509070f050105160c03 71
    0xd100705104002180e44809020044409103d854050030140c074103148802d061a4405588801c0c00e400144026164003102c01554598641c05080e994850000806401c18a201904115490103080b80c1441500002180c02132a80200e9844804515400704642d00341002e000c490b82c06000801c1c2c002c985d60341030b003e6002200d8020000d8112409003080400d010000040644443c644000e41c2604140f2600700490310125501300950910304044820760350f00e142940a084040c4e101c000b0b280d03002d40c0300141d1303004040300600f03c07414548190f4258034008482503040f64594800a46440ca21000500c01c540e420390241d0340011805800c0302c60410240c4c00500d0a40c0100c40454644e034444d0306000d01400e0460409400100504045040c0200107400600d24602c070b000e04000c02000c42807840c2a038405201803c00c001c401d000340c600e9201100700904441005076a1002c81d8800d443c1c001a200c0c00075000c003000d640c016900e07980303002207c403070b01070080b51300d0b0100b40c0c0d050000100c0040000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 559653624 1250 559652374 559652377
    0x5070e06070204270f031d0f0d020f06031602010e1219020307150c030f060513091703100302100908030301181b2309090a09052e05070f32 61
    0x5215103008003c21905e0702d4010070030101c10710480ca1884041c0102192980ca4403105007000034103035409002903480307000185400c0c604809581c1c200400105005001c4555000c1100c00f0704a90024410340300b05840482c1da62080c40d01e1400701c071100344000c4860307072200b44e21601041c0f8981b045a08090883d01d441c00b41090106110503501d07926115007601030307050301071140701d451540000c02c1000d14141c0800c0380303195152800e0b9141c50351141400104158500c818200c0346045180b079449180510b0224404034a82c041030b44500c0c0c000d00c85800c0c451151034010280d401140285041d40d107018010300000e068a135409000c01d0b1075580c110070000c420b2200005510542c4e403902c4404203040302181180024030b0500c00b007180c0801c003000254461605890300f2107889400007551300d0260401c2c6060615001c081495500c0d080c2c243d03501e500300d42000017002d811080c02000152a04041580c03c082e5038006a07000c90000c0c4a000d0b008240401003441c2caa80070901002860000c0c4000a104d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 559654874 1250 559653624 559653701
    0x4050f180703021e12100212090d020c040b04020d0501090f05061905010305041707060f0507030e06011211090705090102010c030c0c0f02011e05041403030f1b15011805070e06070204 80
    0x106c070f40c08601490f000c038004601641080340c0801800c40014070200094443c009626801d024648924030300c0076544603541201d40c040b0a82c83c2c20031095850b1185c2301e003e4800b04a9513001282018082340c05460b010146082c002601c080b5590424901030041d001760500410613101900000100710074000c03840000d000080c40b46000240309001b22500604440cc098401d20400d443c0030305507103102c4400a452410765035888c11030344d8441180e14100010921840800da082030444003400680ca4112001d04040740d0260020320003d072101c44110308032a040240c2c21300003504034081d40041a101240c0448880c018504030381d500c10b0030194450034110240c00c1200282c03002904103c0c9a111800d8640c8034142280a1854800c556800041c14025601c03e1800c03c0559000c00c40e00c0c140400000b01c455107140351458081da035945400362a184a4801c6c80500e034100400103039121310444020500034030013040c19003818503580920008104580014000a1048265001c0d9020f40800100c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 559656124 1250 559654874 559654903
    0x60712020c04140f0c040b0d0e1002070804080c0d110d030e0a080a0311150c181509190e1f030c1415092b0204050f180703021e12 57
    0x282c2c0d06000d030a0035460440281a000390032410b206c02e002c0c0103090421146408101ca41c08103400701c0030034040f0301b0007520035528440e40c0e1001034038404100c640c2d005001118800c406842101c0300303040c24000c4051909030700400c01c1680f5502c080c2145021080c880d4840d00a1503c805501c0b07503134000c031b50400282e0300840c0c3c20350f00c4a1b16920070144d0008582240c00c1084021f00a01030007415070030882c000c0030701603c0080300049490b40b20014207500418a042c001488101d0051003e6403040150340074900060090111021071408103200e02c080c81d04039003013150a071496642d000210703004d400c0e510f03d0700c103218041c4c0440003002c1401d44510f440908400d410034030040b1901010403054034007010004181000600c815020b80c0d07a5041d22855030407441201082e5515000000b030b50034692120001c0d03009107010203200e211880c403410607114400e65850141e03506030710a201540d6856a10000354042520540c550712100341d1114900d0240e80a82012480007900c100c0908181690380b4120 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 559657374 1250 559656124 559656161
    0x1e03030a0c020c10110a05070b1321020609040f11191b0209130b16120209060405040905030403050a05010c0801092a0207050d0c05030c040506060712020c04 69
    0x3640540e600c10321282101c94002050084205008950f451250810b50014407800454400e4070342402e00c104002c895102054404007603c071403c1d189190400030b285000c1e4034401c400815980d86115107400b080c40000480c900340a82503081014036031011846981280c1c464042c0607065016000d5060b12865071819507403603072400000b444100440c05a01c508001c0100105448000340360142690650150340c014281e81d50020700d0f0204602c3d20070002d01c009400780c00c016031006d100d07880100d09540e030340d610704002c0400c10b2440300341d004240c0c60a074010000c104c100824074042d44244203551040041d41d09060b540e40b50355080100200c2e041d0780507510f0301c00d0701010700d6112120310f0240204220403c06120079583c1007078041e41e00c800a0180d905071f441c1d00d030800390081090030000c1c030000b40ba12124007081c1c40d01d280c55003101d118407406803080010680292510380203044c400c21005d08140d0410309a030300c0389891035800b0100d140c20760145082240302c9488034060615035651003080302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 559658624 1250 559657374 559657381
    0x150d050c040b06071703091203071e1110022a070330050309010b0a0602030d1104080325050d0e030c0109182004080a03171501030e1e0303 61
    0x1035400d4442d109100e00c0e001c120b4a40050800016190701403140310601c2d44a5403002406460440e41440a05080001000300082e29074800400014488001042d94041c00e00c0501911a400c440c4080c0d03403a9001019440c954400039400707810784226051102003840051549800c000394503101141c0560000f40c4148180420425066441d05940c0c0e40078040401001110b400300c6070b429103850400400002144023030724250014151214005d1007849100d5880d89c0181d0750794040c050303c0c0099410702007803040f04210306051b18203c0b81c0640c00741d4600818003c6512500c0700708140b0701000408800c1010200d2406c000f00000b101c450303283c00e5014102c41c0304152a000402d40010f0401c890074005001545040d10741c20303508a410200851050f8490904014002c21036680020056000c0303000200380d40d0015002c11440d003e034440080c40404c085152200c0d0308201d4030161240402000d030880c035482984000614508072003680d6241d0b031552000418490480f540c9100ea90012051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 559659874 1250 559658624 559658629
    0x901030b0906160c03030b2e021b180417031f080a200310090f0309050901030c0501050a03111908010501030c0909020309071208120c071a150d050c 65
    0x201d500300211102000f41503405100052006a074103030300030101070301c480081d0b85503110360b0f01003007901807100d404411600e94908828913260043c032240c00181314400a016580b0307030a10544500180181c5150704040c000303102c414507580d020b04216141031a0143c5c2c0680d801412014500440e20300301c240020b0016001e00d02d0121013260858a000d402000819001806820110001503141010800c01030f010400003401c02c3c00723801c150020541011000d034108110b5074254810b05100c0c3c1c070365218076a10b07142804207485c001d0000421555020b80f003800307598000c00c041c0c0700c800e5861034040740405107400d0806031600302444405440751101044030609030400401070160400780ba040000c01d041c80c0008011351101c0c414034265035800004034407003075800d00c000d0707001e012101e040c60106a107a01d003017512a4046110071481d040300e00d0111304081d240104540440c1d801880c00c04d62100c095600e2841d440300a400050700c24444098211035407100700c1c0782840540560040d1007054580c005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 559661124 1250 559659874 559659883
    0x5010609051005090103051801020a02030d061502061b070c0e060414070c080d020d2301060503070804330606020705030c0a03030c110409111807021009020f0901030b09 74
    0x5403007035488000b00896954060709841c0c2c80340c1c003460f011609480b5004090740711f4194601c80382d80d95000240503c4200e030000002d185980320301800700400e6030b442c0b045804588200c0c0d1104016000840414042042c0040d1060102c0250380304915018599031400c400c1c84c01c0f54000b07021482d00300200700103890184078540c00402444070042407460301080080a668030148001d01c0c1b40c0012407200e112200b0f550643c0e00c04511407404100d40d05600182d2007802041c0307001c020003d03014900202e801c9100c0c50540703028440d43c1d25044800d8071540d840b45060320140250140d4070000987c007048489502c3c1c09408280e06601d00011a030381804402820b200301d6801c068003e90148121490903124402070b07000f22501454240701c0a0641d02d0702514034051808141c0e0701034200300410b400d00c43c960b44488a1100100c40c006d100c0e400380803064400c00030441380c1c4000b41e0002c02c1441d080c2000f0380c008034000ea03c0184000e6a880c01c50001450714602a002541c9503c5124208940201e0402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 559662374 1250 559661124 559661129
    0xa2601050306061206061201060b03010b04050324040308061f0e0a06091d09030f0409020409051303230c01020d0c020d021203150d060227010905030307020402071b0303020105010609 80
    0x290101e1091041c0100035580d1766005d00014084c0c41c51501140c9410001e44c403940c040d001d03200800da5207507500c4c1001d40064015014503446806115100c0400c6440c50010440c140c480703130714401c0c4a41e1181c030280d03001c1c18010403068120f240c81402080304002c039440e4059600a44d1101012030700c0c01c3e01803000d041203d40140042c492180401d00100d0b146d650001815221214034500c0c66449035080d5085000781d9802840062000c100030a81d141590081d0040e5440101c00700003039603440010080a000c50030b0041d01041074220301d0f0b035848a2a81300340b120381c14441b044c1403903c8080207075642240c0c40400008002a60b900a1446841d8103005410303111126100808201184405000151001900c0e5540314a0b10a0804405840b00c0d0b2802403c00c2c1c03c030b0021901d0308201e07103944414501038501c035021028100e40c101140d6008200b56825203e000c2c0c004c5003801140c1d03090000039031095505850003942d40020b9600144040c41400142d8072950000c540e035490004040d205841c1da4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 559663624 1250 559662374 559662379
    0xa110303070201090314160b090313030c03020915060313020103021303031205071e0c170c15060319020f0402070f080a0305060d02100c0201180605120603120702060a260105030606 79
    0xc100c0c405555800380480b09000303821074281000e58a0310a005440c501c0352f0b0040c01880007080000000380484841c0e0f04084074002e544241142d50f9508440b01110040c25070301e03500800a00215080120071021000300900c103040040c5002c4046084888000c059842100000c15144801d100da0207a405850742084107800c2c032480e034010408440d046543c003d44c18508010034440c0c1501401440120081302d001e8803c1d0705a5144084178001b61501351800701c507900010a40702003049801c000890180000b0008499071044031180d0030007007001d04003c0403e51054084c0205030101c0d10280e654110188680101c599655500501406544000700340f035108034403060030b60000d40c8480b009075507003202c04d16014102c46018401618280f151f00c801c14074203488400d01040c02074005008046054001d4160800350780d60404060b51030b030b0f40100c0c1d00400e0000307101040041c1018005058880d0450401c0000d280c3c0c03195200c0c01150303034911640040d4101000401041c1020700444d078021006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 559664874 1250 559663624 559663627
    0x24020d1a1c0b0c0d0603030c03020d0e010909020a050c01061401080f06090a051305060f0604060e1009020f04090213142d010509190806060102160b0a110303070201090314 75
    0x10703442082810074807040007400b8410000001050f142c940300c00ca4860040d040c4c010810786440b030400518002d00424114094840c42071644801030107680c003484981c2050703443d905064105144180a90024102c8100303000c0c0911155081d40002e0040303e01418a607022042c44035111000100a8032018009554041c102414030186440380c0b0102e80c0e0140d400ca101160a444880d2048050451094080c0c85406983c003401642040f903030106001e00360444090051989a20310300c1c059840644054020781484001042205c030540c01900c8103550140286040594074142e040c241c1c0d0040309050710704010441c1c10300c00d442450b00000603000094a0311002817010703400441c40420f41403004400b06e503040000c07681d5a882201140c13207061020304001c0740c21040d109041040c0c4940c0c02131841030b0003030100161480d480010301d454203420f51000c01c40c1c542e152aa0b043d855034007282c0030004100c84031a85820409040000b180551600d60000a0042c1c003805e0040102400c1070558961820 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 559666124 1250 559664874 559664899
    0x1b0106080d090f0e0403300b030f0f060415090f03090306061208090f031212160309021e01050f28090b09060d09050604240606090324020d1a 62
    0x301c0030752a48298542031003151001002207c85d44400004860f1020644002d098090010785802850104005904a6a000085414031501c4440c0d801500380c070341d800040000c0200d0f1002031121610b5008000009040c20691102c11824a00c0c44040c5d000ca80c40d40070410804c101403040c800100032208044400c41e86981d201c03070940c400c004810f4450500c0c004407201d203603428007206148001d228042075542605144051410b001180c0c05502580000d030004442d40c068011410141d80c006d00601c8007203c080300c0b0030407032040084503904001d803e010881c0301c058101c0c000c1034901001141e0790300b001002030342d01d00030811042c0c410f81000180c5004000040f440426501c0710081203502540700c060a00041c0c3c010600c901c0060080c0c0303c4c080500082c40100c002241c00c100da10115800300300c07286040c0c40b0548050b4840e0344000b0303460110410104925440ca8000201d01a035951100c1c20901b880b03038180d810200003030168507a1a01c21030b02e0800e418140a00101c1c058420003403010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 559667374 1250 559666124 559666139
    0xb0a0b06090405070e120a0506100b1b0a0206070c03350c030c03041202030d0305130201081f06020705013009030c0c080d03050a0b0d081b0106080d090f 67
    0x2602201800b8944900102c2c80e054001d90015146030b80c05468080d408000300005507452100f1041a240d038041c0f4404200113452001c46542640c2003102c4061034030090341c8101c000c5580c0c0312181d040360300801000c400103940f524000d2a174103020715400080b0900b1402c000105540c52103900303103020b100c0703180d2004040000b0603c2100300c406070b00d40b80c0c64299090034581140b1032046c0e99043e07400001004142c40030440c035403a169900940c120341c41d8040304d008c2030b42201c4041da100d8003d8444120304000542c8640261a0b100c0ca20245010652040301290746107201241c001002603042035806111a580c0103142d0f2011000c00900801000417000300040c0c2a050b0032a04052241c881007940281400740c03c0070040f442e408104000710307564596245d501c1e0710824041000007400c0c800070402c0c08a00380154041180c000b00a041c2861541e030790034000f544108081c0241c41005464004980c000303110f0303000142012405012208c00e0440d0041c80141250041d00843d04050300910180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 559668624 1250 559667374 559667377
    0x8010911090901060f0b0a0207060207121101050d02070b1501050a0504090c090803030108070807050a0b030718050d06050406050c030412140d110703110309010c0b0406270b0a0b06 79
    0xe0001c1d1503900c502d4880d507003501d01400003900489502001d101000603140368680040c90342a8540e0b003038480301e544074034040b81c4540051059440303248a80c3e44500200d11503000b01031300024141030081c900f000c0380d09800143d8021503011703268a07c0340401c0000b80b04a545c01c0d404000750034030744185018400c400180c01400b5500800a010f42d480d078114500c03902400441024000e414200e941701c0d030391000183e035112918068100c044c0220140003a0754100641c0e880e0907661f46411440c1140c4e80c0c0c0d241114846401e104225090300b030700e080020a0b0310354080200070240104000704040c500786c2070000c1960307005450a003d100e401c10812020610412114840007070034500a01803070f080b05160340c0540190501424078a15009200d40021016401000168820b0321038984190340c2c00e00c159140d008006100740407034400e1200d04002020040c0c2554040d101c0c46001604150030000c8044a42c119282c000b202c0900708003080500840c81c841d61751201a90b64184a9041c4000208106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 559669874 1250 559668624 559668653
    0xe070801180b0408090d150b030a030507081305040c0e0f09040503090d110a060c0308090a0302030f090103060b0415090e19050a3306050306030d0c0201020321010e01080109 76
    0x8030740303040b0003180400103d002140c0c51101d0050686002c01c0480c28114180d8103100d00c070307461043c42c0031a030001c03904020502c000d149825854107418000b598036004d4956228940d059001c1c00c000d440842e0b65581d603c9251055492551241d0b00c01c41e4080600c0083e400d034009440c4510008001c200002c0e500000f11061354600b41c9903218003110301c1c40e140c00b07002174074003503190700500942001c140b844d4802e203030b208414020740d1383c0c02e0251107919100b616000440d0001c1c0040c0c004001d1100164480f0005284005041c50000358155540f07109010540083c1c01c01140708603040d01400c0500ea00400340c00180040c2e400030303801810704885446050b07051102e8804070b1500c80c0000b030000040c07039102d01e4000c20364510180484545072104401c034440d1022280d040500b081c408183c083c0705e1300c29a44545e1018005010120201c01e0a840400c8400812411880204160659001c55402c4240d020640d400d00c4145541400851408038505030051801a80b51803040001b00b5020022a00b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 559671124 1250 559669874 559669883
    0xc01060806040f140a08072001050c070e100906080705040e030f0409050403050702060310051017061c0c060c031d03030d0b040b041415010c02030a141c030e07080118 73
    0x1141c5850410392428400126000b0384018030101d0408103004c904a032000c01c0c0580c8c8080001447e910a00554203409051001d1486078080b440c1402001400c1e05820380090b460840b10182941c0c0f001400280c840a40040403250000c500402039400d05003e1280310918901c00745042c03007071701c002d10b5081c9d0045204442101342c032803011500741802a07045030000d64000d0700c050323502e10f007940322912014072a120b482d008000c0f504514102512800c0610781c2101c101c0c0c20400541c0b20481000f801c4041a15001c040740d50303002c0f20000241c0e06030103103401040b0f11340b24145480513504010700614004184a01480c6140f0701c0740103155408412580f43e480c41120014003010002c000c1802000034403815a0401e01d012440603600141102441c85859103502c040c4081c0f802030300460740d012400f5030094155200000c0400040d1203090341c004200c00ca0400c4800124010215603400c403018111035001c00c0c3d8a95040700004400c0c807003540a010345178024041c800850020114480252901a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 559672374 1250 559671124 559671143
    0xf0b1804200114070303150f5f040504171e030c04050406080f0c1c0f0b07020105150105031501030906060906170c13020a0c0510020c01060806040f 65
    0x81030303003c0c50302035100c01403000041d5220807043c030340500200304880408a2107102c40c200003500c41030210405041d038611000c00d030203c11100e4021041d2003e1405d001c0003a000d0049071002004d44141d4030100042400742c0485000c114655000c80c03040b0406610f800b89041030200000305007044140000e1100e400321940c0d9425240358008010340300c20701e503424480c0340007041c440842c4991024005035001141c00300301c5030f036907959856038500000440d0380c0b141c3c0050f9a052840c0c40c0c600818480e039001c0402c103c2c0e2138038103a40c5003a501c00102c11300302c07070303541e0358a09006095909204540d440041038800841c4490300d038001901c00d0100514050f0131100c580000701d0244d21079000482d1003035120006004103178440400e0000380246015905406032440301c0c80081700070000381d02200b400d000e40f910181c1287d400411019603c079200c04004d000d203844141002400421034000301500301d510060b254407620042c00c0c2942c203a0780c0022503960000f0203000105050042c549200703503214001c3e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 559673624 1250 559672374 559672433
    0xd091703131211011407030e07050d02010f180e151c02120304090501080109020420030403030b1f02010e1605010917120f04060e090c09040e010204090f0b1804 70
    0x407580b00140032500c8410b03509002171040010b411a8407203003c0c803e01e403401d001c524101e9241c981d4a509900c90594409010040603002d940500c1000441260a140050925003c81c1c00d170440740c0d619904c480f1000c5500c2040002d41034148802640040701214148009040e00c40d001d5482c054200d006880750074508094021780104200301c400030080e5402c28480740d07039518900b9001701b40c00300d8141d000764145030342240341601c0c4030f11000001d1584001d0600710345071624120001c05100c03101a400c01542040e8011000d00d5161141d9000384582c004102e0305010b4519a01740105e441c41482e0780507015800340700603070b00400f101d81a1102c509420321585020f844203450000f800d880e0a400c00c00000f40c0314000c800d10401001926026155041700c00180e00601414030801c480c2116054402c0c48241058605a0416012442000009810b16484000c20021540a5600301e40c1485c4d89610080650905140ba42c160800070a070300308143c43c26440325821340444104800071201c031001c40303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 559674874 1250 559673624 559673627
    0x3050615041b020a0b0a0507020d030e011805030d0e012003090102070c320a1701090b01140909010903080712140c0a020f06160e0301110d0917031312 66
    0x1c1c2d80c00701d94039900c010b2501e1150203500c40d1a502c030242c85a0400c60b0002d034460b0a5030180070300558407580204154a41d801c0214000c20428001810759520340c50031105140010540300e003028002c00c0556030b1a40c0c0305403040e040300c00b490030304607a60341001034641000c01e00c0040da0030700e5030b401a80b059695a031103014600a10602c000207100d00d02d1180040345419008611080580503010300e02c0c42440030814100390b021029070f01d00e030701141c5884c0c03e1014014001c0921a01c4900d60004039401049540e0303540484000d0b00f241e000f6006400f00c0c0007461030080da505400c01210f5008010100458500800031780004143c40180a440144e02085441e964000c0030301481000c050001360030300154503030030790340025284001071056030503502810b8004070300d083c00b0b0100d0000700145001e03c01011f070f81102001003030542c59582c1e0004401d0011804c8004e140800000780002428000c034501240da035403200c1c070b001100384c1041c4100301d03805001c2c85190000b250030880480c41a40348000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 559676124 1250 559674874 559674881
    0x2120702150c01060e0a0b0306040206070204020c120a2703030c020a0803030903090109062d050f0417121206040f0e0a050607030b2709010605030708070f0506040305061504 76
    0x180404070781c0058800c902207010342c805410b440c2080311036802e84c1c40342051802602c0038424007952541001d03010500600d410b034000c0801034405000581000c052072181e030f04060302107551801c10000080e8020f030565000f251850700400346045000d1240e46d480103020b840c1c2460000600340020300c20002c1c00c4d940e4a10012000300b0320303001165074924081c10815141c0d00070300400303400300c0d17030b003103404a0744070700a030f61504244001d6509020740b01910320780551600410030303d00040c401c041040300c031382103142d000400c0503120300b18840480050035400b6030302d000b0402c170300255511414800c0e0104150340c003c07903541040c402c690201d40705100c4468840140300d2030440d510244100c01c211400c000022454912074601600e0800100305440d0501a0540e00043c0074500108181d80c4003100c041950910f98200c40318400001c0c0c4943ca60000c00c0c80c241170740d04103040540c0020320400c07100c0c03040415030014010070b94040e8285031840d502c80743e0340c10014055100010090b40740b0b0005441d29403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 559677374 1250 559676124 559676149
    0x30a020c030c030706061211041109040c0c02030f01020a0503010306090512210105060301080a030c0f05061315060302010c060506030a290901020a1707120f0c0810050102120702 78
    0x40c00e4903552000424001c0d92603024200403108103041040016282e916540120945900b00c0daa034801015010100802040c50600d10080403200703100000e4540c039580b00395089034429842d1000c4d020098010140307040d03514032207001c41c6c2c0e00400c400c40c1010340c0701069904480e8000b1000c908100342d890107504081e1b01c902a50400c890200b52461b1090b00e58004459070070003440c0030010359880c2c10030b002031844240038041c1da50784000d660740000713031050858210203030050314006414100c0b5550241401c100355190314040c80d409030340405000707a440c03c02580c0107081c0010041a869940081c03c0c801d099080034140d19034500000740291420300118600790b510003480ea11400b280c1811b000741b01040321002c4a2185920000b900820052080326850f40041d01d42440c0b03003041c60303610111500d00406c04d00c10419071500e10400e5071198013904802d1046071802251203041b8600040c42500001c0840d8072941400e036040140d07176000700320150740c640c54140702076641d04240040b550100c50070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 559678624 1250 559677374 559677397
    0x3020c0114070b0c03060f04090b1b09060c06090f060103121412070201021923210406020414100801030308130f05011a0108040c050108061305072f070b030a02 70
    0x10081e004e4445801944202400c49510305000382d05d2080c1300440340300c101d0003131408003518049040d81100c4000c4a081c1d01c1440c854600e0040150042035080d000346403070441d554406401e0003094001440034991540d56180200050340c034640b64810701401c031560741010301050000c980c1120911508491801c100b11000070124100460001c1c003e5004d140009090a07080107600036140c40303400202d80c10780940c400000303c140c192510a01d141d001c5901d00012480103110145030f138844001e202e00c01d40c0140d2006846628000c20700071500424002d50780b10b0072040d80345030155134101c5145070542e0b415180100c202c1c1c4d6070030680156811104409449440e8280d0440200b000541080c42d03c0c1410685503054012201c0064a5a00b4107450040c050954100c042c081940f0441303a066002c40000e0180380f55240000c0c41000710341c41030f11101c000403000c003c400036414490031541c00a43c1101544000c00340a69982a00e03001a4010725281d0750001021990400e8190140e84004054 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 559679874 1250 559678624 559678643
    0xe090a12210c09081011040306020d180b1614070b040201090b13090e030906040605090d02040f0e010e060709030609020f09070504062d08130c06090501080c0703020c011407 76
    0xb0a01400128440c85010a94404d1103550300c4001e025002c1c1030300c40c080c0070304100e081504643e2184003a4124180d00307185150f40303071a025000404140e01080d0b0900844101c14241001c03081c1700c440300000400032040c081c00c0020f05202c4400c107011140d1490304400c1209807901c941c0300407134a844060b8018008507102140c20b00b0603002d400c03d800708503070205a040081d02020303000c1984a0140c840c00660218080c8410010107000304010107950000500e0060100c06980c0003d0845034140020001595510280c811612092040103001c2d0380f80b800401403840c1ca0400140ba400d0355010040510b601d81480c0c408644940558010601008202006518005c0740050a5801611a0740001080f0381c00c3e45200c211a1121280020301c0b48140c014114555031044d101c17a2000750508980c000c2400c038040100b4a511080e07000b0b09119079858400030b2505000410004020b040d0a001100401184002a0300000d0740b0008100c28240101c0810320f201986030f00e03001e2848054900300c0b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 559681124 1250 559679874 559679891
    0xf0a021308010c18051203070f1a041a07090515090102011808130b03010501140a0c0c081006060503090d0813210f03050f010b03100b0f040e090a1221 66
    0x2000249a8051025011044c2e6129a80e0003000410403041b25440e8441d00204042c00101d82c0d0950b00580450050019603101600d00b40e107074040c1c850848003900c4400358224075000f40c1414405050b0022640d20701400e1440c1060000740f040704500c81c0c00f1108440000740c01e40d00764000e40084165401980c0840404200c0b4140011079501414181a80511010f80130400750050815203041e0340040c1d4500060255046071840b20b035010900041c00c1c41440d011000008041d02051005031840101409038102002456810740380350b03411038001d009042c810401f01010010310118003400d50704e41500c1a4403140714070240820045400b07040404903103d500c40d0080070b8450a51041200e90307030800c101101d420110708a4405a030902e00a01d40300d4010411200171102031504002c000303034103103003190741ca044103922580300752440e844011002c90100300030000c5030304280c2d100700d130400a400d60125580e074001d6a0703035945c904034003441040100c8120030703d21000301c5031000180301c508002120 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 559682374 1250 559681124 559681127
    0x20c07051801050f0303030415020a030618060906060e0114070309031703160302030c12060a05030a0309181b030f110c010902030c03010c1b0609050d08040302010e060f0a021308010c 80
    0x24024040d81340070303e1400e461004141400411688160741010324808039101c1e07220500c0103507014201044c1056240c0d880440c001e00c1101089204103c210000100da91070100d200c3c0941303513a5404003050103c840c4603540d16907000f14486110301e142c030500e640e0703445a52030141c544c114160400307444501c10019031651903840314000c0d80200040f100c400301f10703038910604a09a100031030325100203003414081c20110b0b492003084240c00541c003c1c02d800c449034581001c40e10b003150840701500010301d009410884c2490701502c103c031074816039500340480b055400036082020301c9540240c00305660350306440b8240e400b580c000c051200f07070011206e03a142c07aa0700c221406441311100c2a4401d0140300e40340140b510301486540d00103011303074550882515280380a045030f030503004400e484054652a4140000e4428408044150301c2a03d90b8015414241002030840700f07805100c02441c0c0c00001402411a10b20740707040d030b1050003510056a40c42c03040c1c42c844400720007603100c00c40e2076007440e90490303032903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 559683624 1250 559682374 559682419
    0x5030421020a06110f090909120309010b010818031207050903190b070e1e030c060a0f0f022116050a030e0f03010501050a0905040807050a0c0302100e0a09020c0705 72
    0x200e001d01801e010364401e0880b1000136100d40d001c07028011004000d80140e034200480515800213940098588000c2003030000f01c1181d004540900581e5942c2c070312003681e90b0700180241d400012940c0040c80b000c145010260740ca01c9090032410284441c0300010b41020312580c2201c01100025055a840307445641c03503c0101c500c1000111521030690000800070b91144659420003600245007090404040c0905c0d40d00c0c00c2c1c10b1102a400d801034211600c1c05494001c001d101c1411030347d58907204840318200003000d5205541c3c030502150081080310300c01c0000340502104046840140c0780d5201c14001c50003486c0719103410000c1050140030155070501d40c0081210340c5038901070740c041004070441d00405080310401d01800744d010038400000c1c40510b1159028a0748548940500d078075180c42c0303403101031a02c05030f0242166a169402014001c505002011480450f960b00b071807a01102d0000003c1d60f58144e501039071000a5020800300b0200c041040700d03400400000d000c0304600a01100c5403003a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 559684874 1250 559683624 559683643
    0x11d2e0617091b131e050705030c180105091011060105060703021b0f030307060b0117040b073002030105120f060106110709180b060108160503042102 66
    0x101d001003400010300440c030030009214010100c081d1002109401694418103204120b0030b8000d8000040700188241c5031080488495038010383c0c0501d03400b5100d0f00410390f50300078181c1d82044001e005000d13200e01d2400689004007503d9a90319401d40254004035401c0c09800c9101d0b07807042c4256540d00c1c500d504810041010a1a5000e440580c4e881d00140a89072003030b1440100180d00600c50504011480f10310360515000041c50003a041c80c0b110002440c0d9004200151442e6954043c013402d1580c015801859417140e2210a10340c628080c1ca8540c0303100001092001401005d04004011040c0c28123000c442e040000002d102810100800600a4209004150003200c0030380c00006c4120000170351000e40004079009000c2682420000c0740e403403280300e4010820388112800460314002c02c1c054124002507580010b0390902d0745080c000100400640000d043c0700c40e24040c80441e140004000e4411646070500d9a500c0c1c0300c0e49082c4850240d80c1e410012220b140c585200e90099011854005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 559686124 1250 559684874 559684877
    0x9050705040612080a031139030a05220803030703060504050f0c160206041d011205121c021207081302030c040911090414070e010b090409020301090203060a020408010c08011d2e06 79
    0x40080b0041d59419440c488c185006645900c14003039441220310600080c001550201e800d14050002ca4a03141c11001041d0022180c039000442000501070341441240d00500c81101c05002a0801150094400001401d172001c1d90f0400214101000c54418404801e241e01419a60b902c0ba036842c82501c0c03400c1c41c01110642200c0003000001c00d500b84095840429411002502c4444951a09403140e50b10880340030000352000050364400790102d01c054002030002c60364a021525061000400040e001440c2c068031440140060025841c0081c481480080035100040d111596041c00c00020444c5075100394440155000c03c8100030b044900d002c0100f26401c11035803000d44030751001403000c20034012203241c080103020f81010340c038254000c0041300d80050000201c0e20001c1e004030382400e00449004000d5600010200000740003403140800544107071a00d202e4030350606400305000f800203049071499807101d801090900c001040810360115030f40d0713102c0041380400d0070f001c841c006c1c20344107070720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 559687374 1250 559686124 559686187
    0x30e030c0a0e06011d091302180106020c040605100e100c050604050a12080103030c08030a02120a060f050d20061303050c090a0902010507030f111009050705040612080a0311 76
    0x102c120546116005d80c41000505110b540d1340d0360700001c54124481c42060780d1041240804121b0345d441242c1c0c1e24040e0250340d0150550012500c18403099813180d0703004c070740610010405501003541c00000700c402c05404444000e01c04501401c00c691258812070050701e217004201c1800200f08002615010540c801c0260306400d40d0400c006a0310031000b440042c010640311024800001c04040c001c681c0031800f04801820089940c3c08160307170500494000100c103954a4081c0038800c81c1c107140c0d800400741150780c404402c41640d00c1c11010000c0903440d05201ca90158136030843d0343c0c2c2106888120540710302601e180e90703590900031394480003100100c2c000c221b50b102041c80c0401034091080340c0354040e1103231442c4c68499501101e906444200e418100058540c010111060a00070400c0303c4c2e105030701c0828100c09a00b0254103103031840c0c1c2b0041c03040e4900710f0304008010780050341c10003d1b81c03c14240303521007410f04000d60190006201c4620307980c0c400a80c9071100540424454041641c80c0a5070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 559688624 1250 559687374 559687397
    0x1a030607080108100c03110d0c021203091506060c030f1b0a02010f0c0219060c0606140a050d11150705010f0b15250302060f070c0f030e030c0a0e0601 66
    0x140d4520100b030182115942003404c849060081940003800c10800c1c0d131400103010745850344004450f40103040c90364203980d22645070100c000e50400c9141101030102c8900c5180d420304408150740c818941c0c101c41c400751403c074001a000c1c0d0307580b4141c3e202100904c055903900d415205280b602e55120f10810800c000304e00700213180302c2400050388403070543e041e1511395003e0f40203c0c0685002d0b000060807a8444d01810901800c016000b890200805045e00c071012005c40a1600100f5140103411103040100d15801c01e182c0303a03881e880644101e54007911200440c030854108000011500d254140c1c10002c19801c0314a410040c030018041203019100800152140340c88040aa071041c9000c1544110140c007085d0510b04490018a10b4940708402c08031254036400d500fa0961003e801c0a2b0003507001501000700510400b0402e0b640101d0b5850000b1040c0155614031500d20444030014041044400269919171410802048981c10040c00030100c0c07503440100100d40c51044441500040d4150a02c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 559689874 1250 559688624 559688627
    0x705010507080a0908042310110f0a05120f0408071412010506010819020d0603080711030703080301061817100608190605060f060a0e01020114090a150f1a030607 71
    0xf04130105902900c07091800d8a00007012402405120f0204001c070070f0300081d90081d6640000038498400562101f440c8030302e4450b0104d08144003000c480c0c0b020f400c0301c1040720001b54003140403203203110180d44054884494020110041c095900a00b40500c24014041032035420004024064001215903002c020f0482c8540e60070307510b0079a01140841e200320302050400707481c000d400c011920159801800d014194001401b0f4030341b50750080d60005000591b030f00501101a01002402e10207138010014140f8542d941c5555120500c583c00030800d45521031503040c42c5445103003008101044581250034444880340303071034001400700140711130702d001d03000a2002008914908180148154040003060315280e15014140c01484207501c42860312102280d07a440d140580300401c0d4a0359400b05d90710414001a0031036806020a41c01120204100003950200050300d0b45c40961000400030707248400d0320540064081001e02040180c1413286440130b0b8441001c5051140700d0071421500d058840600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 559691124 1250 559689874 559689881
    0x90c2102130b03100c051222110f0a06090e04020402190513080118022b0b0118060e071101090b07020f060604020403080a050715140601030e28030c06020705010507080a 74
    0x40c1c217010030014006040c6600f0061311081d400700009901081c001d41140c85000300c3d0700ca011003101c0d42140e280317203040701d4113100303011142400c005d2710f001c0c1d40c841c00c00c01d000e0428040d81c810056080b88143c0001c08640b250380607a5200c4442105030800c03031001c05406802c0342c01107040781c0b80d110300c0c00e0300006001784140a8003d068040d00350075040c8040315028000e207002c00040103160300e4000c0648000e030101d0068581c0300f0900958a60b00039504048510000301c0407c00e074460402e041050a020f100810b030354141d000388241c01c140c540c1081903030615014061000340230b00a0040302003001308644d008a19a9035108211040d17403c01d5031614200b104034006d40c000a0829501480304110b230901500050003410301541c0180704240c10b181101d403e4420304402d40c80c0e511645070502000b942c05010f1061a41c509801410901740481c40d0b201121015800d4240c101000345408800d040c002d02c2e4008880da00103409640c0c500003414114080d000139070b298400100300030005141c0311054032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 559692374 1250 559691124 559691141
    0x5030d03150b0906041a0c100203090615030c0916200303070528030903090e1311210703050601061b083613090c2102130b0310 56
    0x30030071120b8241041c695182d00408030f0640c12610401c000710340414011448003400c0c140c3c03e41c0c95a1510301c071500500380000100410401e41c01841800110340e000314902d42e120f4802a21200880741e071000080c5441b50003d0202e0704420880140019042d504034103440a55881c1c032440029a07401c0100320401103d107805c416580c00510224616510510003003400140c0141c905c014510901124004d00e280c8142c150040b83d0754440c0c200c10140c1011007030004041400c440303c1d081c5051a01003428082c5903034020202e040318080d090742a41c8a03d10b0302e0003a0b10b4102417446e865030000c0500d559a43c9030005039240d00c5101d00001e406849902c605e0700c490405658585101c01c2941c51100541055998101a081030305109220382d20720556058071001082c00107921030702c00400c0c001e0080c0035030103404c2e041d2704040120b008242505984400c860701e4906900398640849482c401e0b840d00d12800035480f413200705031484094682d810010b40701c0c2c001c0302034035503219150603040200c40604 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 559693624 1250 559692374 559692401
    0xe1201050a0509120405060a03060510020a020405070f020a0210050408011103040512070206120411090708040c0602031809060d020d0807061b0f030b01020a06021306030e0a081c0608100605030d03 86
    0x41200b4420790420801420100013981004102b06845600244241c201010000b0042e40501110000d52034a030082e150020070380c1c10041404504920002c0d103486542c01c0107402114a001e0502c0c0c03c0744500106c500800000008000001007080f01000070b61065505903150711908585041030580d000847d02e92603801406a0303c0c010340c0c481901684a00280299101d0b01607072800758843e2900d07840144985905d503180701e850b15180c908055407540701c0e0468400c6503c01e0045c2c0100c00311001d0700d500fa1181c21075420b070007035480790300003442154030303440003900042c900508508200c180d5001d40b01d00c51082d071003030202c03500d012a9005890100c5004400041e00640e000e404a030081c1d00200c54030700306205403400d140c82601ca074400daa03c18016a0380c00364076400204106c0b541752064410b5203000001800a4400301e8968280c0c6024500c40c802c140fa0546c14201c1a4414a50080d03009041003000c0c1c906040300c0a01c0e88004140912030240a80a034132600152a8440c1c46580340000c0b00d03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 559694874 1250 559693624 559693627
    0xc150b190509190e030f0a11010608100e0c030a21051e0c0114070815010c0b0a1113090203070e0108090d0305060409060203040b041211030f0702010e1201050a050912 73
    0x31105010454000c4078074890f40a569007080d00c00b0040140002c12503030190a000303990b070303803d2050010a000300e0624544160b034035110040c0543d075808035411511064201010504042811120303007400c080e400803a601d48244001d0714104044d00c1584002a812641c0d820002510a1800e0b07601c0d10408254041400441024401c03602e142e002404041d00f4101c000980c40c0382040a21218102c282ca20300e02050b40d110070800c20b1580204138482111003841d003002601e406917210001e030b54015190318020760304c4000c030303280403900e010903141c01020300b0072100003103540c07224014025401558404000380e40310750200c10b1540140c1c400c5004a010600400294401c083c0032402044050311855001d6101d10105020807054009107008500034182c2c0e0045081900c5c00900c5501c910b4003070014407900c40d0020f024100c020095400d00c0c080f84403150345c1e0784918801200d40c2415542860ba0013403100903209440001540100e204400058040200e9152406501d654260220b44941034280 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 559696124 1250 559694874 559694881
    0xb0307092105100b130608060c180d06021905030903070f0303180b1e0712050415060e06010206071d04020d0204050406060f08071b0803070c150b190509 67
    0x5840c00c152080000020008150603180d070b9910781000700c0e500c842c080e0203445510842091030f109100b581e544070324610400c400b501d8184520780718000105208408800801c0c020040800d074101660307110401000301401d000503181c1039009400a403c2c031076207821000c9203445654041d0040701c3c040c00e00c02000b1401d10840341e40c6c01ba00c0c2501003000302c082603114004001031003148000c0d000154818850745081c0d20b8002c1c0328055000c0800c4081009c050f0140500605503000b00144004000750b030360101746e55455041101488980d000c4943e450740c901040054104005d2000c01d002d82e03826800e13500c01d031b1a000d0048030107200c2044009400c20070002281c1d02c0f4509640201038545c4841e2025041c140c1d54000582111510f51146010820f400711440b60280d0088009a1055460405000011507a81444c62103a41c404004006210010200c0d54841c002c880000c1078540c08444046940c401c40360300c501501ea40e465041c0603002012086246814101c0bd0400f95500a407201c070b503982c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 559697374 1250 559696124 559696139
    0x1206020307020f0609031e0304030e09041a1303032f0901110a0803010f090204030506010612021612090503010509031801120906060f15020a060b030f061009060b030709 74
    0x500141c90001075229101003455804410301c4101d00c00c9050001540c0c8038110f52042114000302c0a1910000c07440401c10000003a4020311000d0560380d0648818030540c2e2035140c103400280f11580c030914a802890100844d128000c0241c4180c20700c01c0d40c09110201c21401050010744155255840140c20101260401c4080101411491105241482c0c014001c9500d203810300000d6031050300e58441c00030051000b0740000760b0507001042241821860700386103440711610741c0c8041c09018100000c550b41510081e42c00e805450f02c8420f00c06ca00c4802d010646411501018480e10590104821403c00113a80c5811300c202d900c41c1c0ba404024500d414214002280c4003260b070051a418880b400e03198005841c018400d4400c411f100d82400100c0700d0414102c0c1c000e903078450b4850320003009054440c81d07000350b0120340508029440240400d000003200c0000b03050040d10110741030b0301c1c41042704201c0d05041c9044ca00f0120356015804005658513440c641c10180b20442e110f00100311070250400c01034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 559698624 1250 559697374 559697377
    0xb0a020a150b13090b060625030c150b1318020d052a01021605061804020d14040605060a030c0b0c16060507021e01020c060306030106090203240406120602 68
    0x810700c0d907000a115080b1600051100345008459000556101180e0382044543e80000d50029011911141000042581300024103605040c0800c02c070410103405041500623058460074a034007400c2d900303542040d000104014409507040d02c1c801c3e414081190440c0034940b1803050907a4241408502125540e000d100d400c80e0300c042c1c02c85d1603202d0008107003100712007208610031034401b0790701500910a03444002450101840884803c00542540030085952840c040b035015070186a03030321281000d0b0702c0000d002402104500169242001c001c80c05810039111030603c02c1740b00304020040740e16204e050003180100c50100820314940e0b540140b00c0120f0034005007035440352940880e941c5042405c241c8403284040d500140200c0c901040c010114603103242114a071058510b45400302c110301100007503071100704c50522800703282c000001c01e41c1900c00b03401510203400031b007400355507070b081a2501d141da003020840031010218440402000505d0517008120455258010440b00b214a940381d00009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 559699874 1250 559698624 559698653
    0x603060f0f0307090c09060f140d0c09150e0315040c0b03041e0c0e0721020708120108161505030403030f14010b030106120203090a0305070816080706060b0a020a 71
    0x500c02d002000544a03070a000301c40346621720360742c2e140c1141d14024000d0300c166013550800c0140880c0e441c961000c0014001a41c0200380000d034040394580508409a03000d48245c0c0144488603844d80c4c84d0303407226400646a9000b25401d07011591130031421400c240c01004140c03030007460a51004020041036011801558000b03001d00f1180e002c2c1482020030110901d1400012a5141d600303202c20003510f9007103030303c6a512500364141884450002c1210400481070850301e00710302036020521005001410083c0e80740781603060303032051065031203200c0c50341c0d1755500001014100409000c04209c0e41120320342d00d6055101a101c09056480c0c550303054014000304050200c1d01d075030380c00100340960307084607620703000700740e2406401d51b00e50503c3c000500c1c0f8404481c01f81c0089004109100790001c00044042c002c030b4052a01940719001403400364941d2045005844442031005c4814042c00180402081401e200340380800ca15950340a0020040c059140386002582201a125010580c5880030162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 559701124 1250 559699874 559699879
    0x6250c0507060f0909020d061a09090a0507020a0f0b01260c0906040e0607231806031815010906060c02010e192c010f05102109061a0603060f0f 63
    0x22110b80751751100007241c01038000800711948401c001c03c00b6440c08100c21040000040c1240c0c6404542800714000361400707012281c40d5a510310000384041d02c00d2144813100c9030300021030844104942440000002c080c0030f10b20058404a0f014030305450f1078840908050000b00240400802c100d04224080f4001042070303820a841d08141c4250000c18130566110f01e001e07848090340c0f40d4100c2c0300d80740e0101160a500040c6001084561002503490750340c8169200e003107032496540d50b50721202007080c41190001c41d40502c11894079014080088508905079042101d0800050342d6a180c01c171131959112002a0120f0190800100c40d0305001621501d240c101c0348018a410f03644042c2c0ca480031071046029100d0601340c2c03c4111908101d13140860050040c0c401903414141020300113890000160300305414421500c03031480c030446440024070840c1002e010100040301803070626201414084a096003000c4280f07256501d989010400c3da0701a0300c0141c40b00107482060014803074034200580b12181e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 559702374 1250 559701124 559701137
    0x60d060c050918150f130506030a0605100617010608150102070506160b0c04030804050603090a0b0403050c0607030c020705130b0d0f02100e03060f130506250c0507060f 74
    0xa42ca0f100e58000780420a010883c01d100762910585a55640b0300c1604294030a0100000c290010ba82e40030882d0500c461030380c00015203072183d0002a2400f5500c03000103000e02d0801041002c940e0300e8495070000c4400540350481c2c3c00d144d081d01c0c03c902420034012880458080c0000c15625070880d580c504454030f040c01101c03002502c500000340700350405107150902c035100d000380400b04504402900d0704400014091403c260541d951110ba03801a80540c43c041c40d404000150041400c001c406480e80d0420301e07140d001d0405050081041d400f190780b50b4a1071041c00041a4018843c0c890490342c0c40655003e09481404c0104011061000c0d40b40140c000ea100c0c44403500c01c2e9a03001c100e031a40352041800b802da0a0551050001d0702003c244c121082c4491a400c2072000d44002c60403650040c0c030300e18105060f6a441c000d450720910002d80c0548144940300030030200910511030070541d019440300001919190520440703aa41c80440d005050350003420040041078041c860101c420840b508000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 559703624 1250 559702374 559702387
    0x60705010905010510061125170a1e051b01050c1b01170c0406030506120f010902010e030f0a0b2220040b180a0b0d03030615020303060d060c05 63
    0xa50075208401001d0303403141d55500a02042e401c1100b072060060240c4d0400a403840e09030290192140d40030200300c0c0c3c80300d03403042c2071b410300142c0c28107140003604200303c1c4001201040010f0b559100500302048482c0ea8206007480c1c0749015061022800c0d0781c1c010024264884007071900c1c4617101e20782c2030313150510000f4042c11a11078028801c0e24000390300ca119120340c40b042040010318900705c142050403000075080602c10115032420444040e1070040c140814640c41c1c2201041c104001c1102d013012501130400d446050744010740140340024001da8031282262407803409c05885010340c600d11802940b18104240c00943c48201680d0300c080f043d005c0d0941c1000400b615a4250740e0703a4000c0314011010300b41c920f40c00048039200c06001000740c4041281e180264042030035122640300c1c02102c4a00d060000e1403134002d41e080404024001741541039142d08621f80030380035018500030a40540b00301114003038254400011303248550f500070560074158090b900e40350000c194112411041100400c84c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 559704874 1250 559703624 559703633
    0x6011110020c011a191703071a060906040c120b04020409060e01090c02060f06010507060f0c0c02041b1b030e031e1b10051c061409070c030f0c020607 66
    0x5821070ba90520008140041c4042d607034400035404001c15445011006a0301a100701d441078150199050b464505020211010301d1070b146000f000402003002c5000070040e1000105034100c64013458050b01d000c9819281c0c0b104000039245000454800503a1a031120000d15625401854007904064001443d09440b2011201606c2c2c85400840304154007000410101c6000c0c460180913000c00d1000c2c25140c2440000030700c1114000d81202d042240200e40b1000b070190692094800380000c40302040b1003501840003400350f2002c0c500a0f841280ba01000001030b42d81c00313009d0018050716603110400d511a107070741c15620030b01e551003d404119000384510303640d0b101040311004448600c0d200287ca01c010610300c034030340609503007003c811681c2145030700802d44591160048294031810650344030220002401d0051410701c00c13071014213007440700000d51040000c2311601000c1c41503541c0c6989a4801c08141d60210301a18010001030039080c00002d024440c1c0c0001d849140700034003580c500f0159848 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 559706124 1250 559704874 559704877
    0x30d1109100509010f020c011d0102150702010c17040512070807080304081305041812020f010614030c0a1a03060a08150a0b03070503120f04031205030402010f0905090601111002 78
    0xc0300c40c0801c800041c1d03d0740c00d60f0003140790001d1801500c0140852540c14000801c2c00100c003d01b801102510039410410343c0c000d12291004e20341e51020100d440c60089002406841144c0c2c416003c41c0000b0748450b83c980704161128819038200004141d00500007500c81c01607806488182c4400c6800c1c000400001d90b0340c80214050f5004022841c0c5a00000900d5041c0b007019a0109106d28901a01142c441060b0038044101030340081e00640c0b24a403100081c2d0800d048500d0b155055407134a0b40c0801d03c80001d006143e0b03003c4095007112540102a01070001084050160280d8070b02c41106800e040c2c005c1400455012401502c80300b4070a03503d5034541d00d403154155503400e840e80884200005160b2034410341c3e4007504114001c1942d68030f44070209444200f03940780107081d20b0000501c0400e40d4201000c60b4011640806841441802000c000707181c0e40080c0d8040340025030352680200c0d002d2041e0301e00000d0301c200400d0041d6589844c001962440e80d0340184039201e010b04d4042c04001c0c132a510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 559707374 1250 559706124 559706149
    0x1902010b0a0b030a0501050d030e0d03090504110706060e130f030504030b07030203090f030f090418020d081206030111040e04050a151e05250e13141305030d1109 71
    0x1c4102e526428003610080603240142c0101d03004a49004030030010a6014411108591061b0f441c50346040c0d180c1011144601c85802040d001410000042040300030203004050f400c0c045c3d5800c109903506d40b0003e803c01002074422045448280804c03401080e401d4070684041d0303200e81000b034071b02940d940c2c9004143e2012107102022035400320410034610418003003110100d1040340078501e0f10043c2c000442190040e4513445014603501c003029000560520640342180c0d80080c00031010000c24038092800317500928104c89100402c0012a074107090501507088454240d1341680d0500e41080220a540100180180c0c0c0c54420300342e04401140080000303406800802901280100c0072800c101c48246080c81c003161440d241c0307010894282c01145441c242041c40f80140300d01045003d104540b00c3c00d00c8405079902004010041c1c040c846264440000c0b02c45d2458040465990b0b4040380e0307004140c201024110350410007101c1c1c8100465031120000c807400e9603880d81810034106c0401c0d54100c3d1071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 559708624 1250 559707374 559707389
    0x604140708190c0801060e0102070b1b010e0a05010518160312030f060303030b030714060f07031403102c0426040305010504051515060904021209011e02040b1902010b0a 74
    0x100010f00c200c0347d108003440040d240c00c4c0001c1140c0d83c03034070fa0b0b901c200d841984064051807083d5983d24074000001c4d00003414043c0868100c60f40c03079002d4101940201307030603501082000c0441c0080004100042a60b82145501c044107402c05499031301c0d22141028000000410075a990412038204849841603401950080c1d900080300c00042c0e041c946000c180341c0200d8080d890710b01540c811039940800f142d035103184050141341c841140d45000d0360206441502c0c0745144101208001044900b0f807544400c031580b400060800150710b03a20103902c160151070180001503030400003004210300c4103507003610034a1508040b0200030b07031804803481d941103500129000d135101e105200a12908200a4000178054011103109003800c4c0640c078a00c0c441c4c1035070b0f14003542000c103048031a03586aa0654045807244035a51160b4030307080d094107008000c24043c0f0180c441612201d0b1913007040354800c1d107059960f003107000c0740703460b079060303101914081652a240c0840d03403201d18080319500c80d404c1190040c00078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 559709874 1250 559708624 559708637
    0x30c0b07080103060e15151f17010e0103030f0e01020c03070608090f0304050a120204020f040315110910030b120a030216060f0504030b070908010e0a02090604140708190c 75
    0x4614050054600000d0178040951120840313800d420040000c15402000341600941c03000b142d800441c0300328020000c0c3c04248000680c00c0b0342c425030054071382404a0080c4140c180c0703da032590011004008203002c0030300000da203050f2050045014803845564810140104e802a41c410340010749043da054002e00001401c0e0400d01642c00801c02c6500d00c2030000b100558102400c0c000407942101c014440d94400000c0c4841c07101c1991180e6040b40c1c009040e80030340b2a5100c0c0c03a2304100d4900548180403082842c03030320300001e001c03c6040040c0c60998400a15018800a000f00304034044c160b24043c05074405821107400030600c004002035041e0a00ca60050000e1041c4241503e8035410641c0c4070005100d00101403443d0315600c42d04480a40303520200400c19500c440000f1138041d9483d8003e00b00e02e6103400034102101038001075440a01d8421a07500c603442e5554014030080d10800409200c080d005c94011458490082501603440290170b84075084401171524800b0680b20312000701d9010034103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 559711124 1250 559709874 559709879
    0x1b02011d0703020609100504050a030305070312050403080615040503011802010906050a2f070e010f0f050901030f05030f1305010813230f241608040b04030c0b070801 73
    0x50940c4200000c440026001062454001ca1442d00c91890702034807401010203266a0903000f607041e5400380c68058038491405e505c4e440c000d8000d40c0021405d40100300030318181920716540c3d000e9588141e40c07503500c050003611903005006880c8904940f603038110009000c0820103481c01d20074071303482d075010340c030408101c00050002501408003600140c1c04c101d020403410352134681044d4603ca0701c140303003158401d0344000c0301c0780c680406103001a11105400760b400001121810640c000741a20090124168025651008000381c02c0d010312803141c01c00201001000130500c3c2410100d2941d000700c00b80d9282820055002449038080000170410322003540080c005541d000f0007103030f4403c0750b2660340705819205440e515403112405200303008041ca04128100c2d821028020800c40352482d00464281c07002e101002e4100110074070401920304032850008003502511500700d10301d4a480d480e419002c0e03d81d516082101a00200103030103006080c0c01d40f80014502141d00c3d0f202c1c0310f035550340219a50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 559712230 1106 559711124 559711151
    0x19050603070309150e1b0303130e07120b060711010203040801020f18040c08010605030705040302060301060f1202040515070606080f0307030905030a110609041b0201 73
    0x520210034444500d41582201444030f129484245851500060790012035031074480d08440b9a01c1120410810203908003801c03d41c882c043e050b00d1a100b00402d0500c1e60310300941c005071416441c5000c00140c1c9a0025102c040c05603652400e103d45200c20000a40b2400341139005400311081402c07040702a8020404c8400030100c180c020343d120714100000d00c01582260390701c0c82030000d40d08036054403894584180da001c1074403a02c0d2040541d08141044660343c02c01030803003081c0b05042102002584c0c489010318000c0146039682414180c128100071b00c0341e25209002d00006005000074446981c0d01c0c00781c442c0740c2d08031042558644010b424060041c100c80d510103807150090650301039102c0d00c0440189070701802900c4200c0380c240d582091540c3c0e01c40c424009850300c0f90680699020380352104c018403003400300a0012030303160505454001d031955000f0401c0091b0307665006010140 = true := by decide +kernel

theorem cover : BRFrame.Cov 559532374 559712230 := by
  have h0 := BRFrame.cov_init 559532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 559532374 ≤ n) (h2 : n < 559712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
