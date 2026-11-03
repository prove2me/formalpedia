-- Prove2me | solution 1 for BFVBound.bfv_cubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:49:26.598113+00:00
-- url     : https://prove2.me/submissions/071a4b0e-a827-473e-bdaa-66a4604d898a

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding

set_option autoImplicit false

/-!
# The BFV cubic bound on the product-state edge expectation

For `s ∈ [0,1]`, the BFV/GP product expectation `F s = (8/(3π)) s G(s²)` dominates the cubic
`0.8488 s + 0.08488 s³`. This is the per-edge product-side bound used in the 0.595 / 0.614
quantum max-cut analyses (`CubicMatching.lp24_strict_scalar`, ALMPS25 Eq. (17)).
-/

noncomputable section
open scoped BigOperators

namespace BFVBound

lemma poch_two_pos : ∀ n, 0 < poch 2 n := by
  intro n
  induction n with
  | zero => norm_num [poch]
  | succ n ih => rw [poch]; positivity

lemma poch_half_pos : ∀ n, 0 < poch (1 / 2) n := by
  intro n
  induction n with
  | zero => norm_num [poch]
  | succ n ih => rw [poch]; positivity

lemma poch_half_nonneg (n : ℕ) : 0 ≤ poch (1 / 2) n := (poch_half_pos n).le

lemma factorial_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  exact_mod_cast n.factorial_ne_zero

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  unfold coeff
  have h := poch_two_pos n
  have h2 := poch_half_nonneg n
  positivity

lemma coeff_zero : coeff 0 = 1 := by simp [coeff, poch]

lemma coeff_one : coeff 1 = 1 / 8 := by
  norm_num [coeff, poch, Nat.factorial]

/-- The recursion `a_{n+1} = a_n · (n+1/2)² / ((n+2)(n+1))`. -/
lemma coeff_succ (n : ℕ) :
    coeff (n + 1) = coeff n * ((n + 1 / 2) ^ 2 / ((n + 2) * (n + 1))) := by
  have h1 : poch (1 / 2) (n + 1) = poch (1 / 2) n * (n + 1 / 2) := by
    rw [poch]; ring
  have h2 : poch 2 (n + 1) = poch 2 n * (n + 2) := by
    rw [poch]; ring
  have hf : (((n + 1).factorial : ℕ) : ℝ) = (n.factorial : ℝ) * ((n : ℝ) + 1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hp : (poch 2 n : ℝ) ≠ 0 := ne_of_gt (poch_two_pos n)
  have hf' : (n.factorial : ℝ) ≠ 0 := factorial_ne_zero n
  unfold coeff
  rw [h1, h2, hf]
  field_simp

/-- Coefficient bound `a_n ≤ 2/((n+1)(n+2))`, in `ℝ`-cast form. -/
private lemma coeff_le' (n : ℕ) : coeff n ≤ 2 / (((n:ℝ)+1) * ((n:ℝ)+2)) := by
  induction n with
  | zero => rw [coeff_zero]; norm_num
  | succ n ih =>
    have hcoeff : coeff (n+1) =
        coeff n * (((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1))) := by
      rw [coeff_succ]
    rw [hcoeff]
    have hstep : ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) ≤ ((n:ℝ)+1) / ((n:ℝ)+3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((n:ℝ) + 1/2)]
    have hA : (0:ℝ) ≤ ((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have hB : (0:ℝ) ≤ 2 / (((n:ℝ)+1) * ((n:ℝ)+2)) := by positivity
    have hprod := mul_le_mul ih hstep hA hB
    have hgoal : (2 / (((n:ℝ)+1) * ((n:ℝ)+2))) * (((n:ℝ)+1) / ((n:ℝ)+3))
        = 2 / ((↑(n+1) + 1) * (↑(n+1) + 2)) := by
      push_cast
      field_simp
      ring
    calc coeff n * (((n:ℝ) + 1/2)^2 / (((n:ℝ)+2) * ((n:ℝ)+1)))
        ≤ (2 / (((n:ℝ)+1) * ((n:ℝ)+2))) * (((n:ℝ)+1) / ((n:ℝ)+3)) := hprod
      _ = 2 / ((↑(n+1) + 1) * (↑(n+1) + 2)) := hgoal

lemma coeff_le (n : ℕ) : coeff n ≤ 2 / ((n + 1) * (n + 2)) := by
  have h := coeff_le' n
  exact h

lemma summable_telescope : Summable (fun n : ℕ => (2:ℝ) / ((n + 1) * (n + 2))) := by
  refine summable_of_sum_range_le (f := fun n : ℕ => (2:ℝ) / ((n + 1) * (n + 2))) (c := 2) (fun n => by positivity) (fun n => ?_)
  have h : (∑ i ∈ Finset.range n, (2:ℝ) / ((i + 1) * (i + 2))) = 2 - 2 / ((n:ℝ) + 1) := by
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring
  rw [h]
  have hpos : (0:ℝ) ≤ 2 / ((n:ℝ) + 1) := by positivity
  linarith

lemma summable_coeff_mul (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Summable (fun n : ℕ => coeff n * x ^ n) := by
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (coeff_nonneg n) (pow_nonneg hx0 n)) (fun n => ?_) summable_telescope
  have h1 : x ^ n ≤ 1 := by
    calc x ^ n ≤ 1 ^ n := pow_le_pow_left₀ hx0 hx1 n
      _ = 1 := one_pow n
  calc coeff n * x ^ n ≤ (2 / ((n+1)*(n+2))) * 1 := by
        apply mul_le_mul (coeff_le n) h1 (by positivity) (by positivity)
    _ = 2 / ((n+1)*(n+2)) := mul_one _

/-- `G x ≥ 1 + x/8` for `x ∈ [0,1]`: the first two series terms plus nonnegativity. -/
lemma G_ge (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 1 + x / 8 ≤ G x := by
  have hs := summable_coeff_mul x hx
  have h2 : (∑ n ∈ Finset.range 2, coeff n * x ^ n) ≤ G x :=
    hs.sum_le_tsum (Finset.range 2) (fun n _ => mul_nonneg (coeff_nonneg n) (pow_nonneg hx.1 n))
  have hval : (∑ n ∈ Finset.range 2, coeff n * x ^ n) = 1 + x / 8 := by
    simp [Finset.sum_range_succ, coeff_zero, coeff_one]
    ring
  linarith [hval ▸ h2]

/-- `c = 8/(3π) ≥ 0.8488`. -/
lemma c_ge : (0.8488 : ℝ) ≤ 8 / (3 * Real.pi) := by
  rw [le_div_iff₀ (by positivity)]
  have hpi : Real.pi ≤ 3.141593 := le_of_lt (lt_trans Real.pi_lt_d20 (by norm_num))
  nlinarith [Real.pi_gt_three]

end BFVBound

open BFVBound

/-- **The BFV cubic bound**: for `s ∈ [0,1]`, `F s ≥ 0.8488 s + 0.08488 s³`. -/
theorem solution (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    (0.8488 : ℝ) * s + 0.08488 * s ^ 3 ≤ BFVBound.F s := by
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hx : s ^ 2 ∈ Set.Icc (0:ℝ) 1 := ⟨by positivity, by nlinarith⟩
  have hG := G_ge (s ^ 2) hx
  have hc := c_ge
  have hcpos : (0:ℝ) < 8 / (3 * Real.pi) := by positivity
  unfold F
  have hsnn : 0 ≤ s := hs0
  have h1 : (8 / (3 * Real.pi)) * s * (1 + s ^ 2 / 8) ≤ (8 / (3 * Real.pi)) * s * G (s ^ 2) := by
    apply mul_le_mul_of_nonneg_left hG
    positivity
  have h2 : (0.8488 : ℝ) * s + 0.08488 * s ^ 3 ≤ (8 / (3 * Real.pi)) * s * (1 + s ^ 2 / 8) := by
    have hc1 : (0.8488 : ℝ) ≤ 8 / (3 * Real.pi) := hc
    have hc2 : (0.08488 : ℝ) ≤ (8 / (3 * Real.pi)) / 8 := by
      linarith [hc1]
    have h3 : s ^ 3 = s * s ^ 2 := by ring
    nlinarith [mul_nonneg hs0 (sq_nonneg s), mul_nonneg hs0 hs0]
  linarith


#print axioms solution
