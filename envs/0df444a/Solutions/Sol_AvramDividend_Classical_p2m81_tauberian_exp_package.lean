-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_tauberian_exp_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:47:00.834808+00:00
-- url     : https://prove2.me/submissions/5c42dd74-2b74-486e-9e06-a6a646433440

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section
theorem solution (β : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => Real.exp (-(β * x))) (Ioi (0 : ℝ)) ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x))) = 1 / β ∧
    ∀ (a K β0 : ℝ), 0 < a → Tendsto (fun b : ℝ => b * Real.exp (-(b - β0) * a) * K) atTop (𝓝 0) := by
  have hI : IntegrableOn (fun x : ℝ => Real.exp (-(β * x))) (Ioi (0 : ℝ)) := by
    have h1 := exp_neg_integrableOn_Ioi 0 hβ
    have hEq : (fun x : ℝ => Real.exp ((-β) * x)) = fun x : ℝ => Real.exp (-(β * x)) := by
      funext x; congr 1; ring
    rw [hEq] at h1; exact h1
  have hV : (∫ x in Ioi (0 : ℝ), Real.exp (-(β * x))) = 1 / β := by
    have hNeg : -β < 0 := neg_lt_zero.mpr hβ
    have hEq : (∫ x in Ioi (0 : ℝ), Real.exp ((-β) * x)) = -Real.exp ((-β) * 0) / (-β) :=
      integral_exp_mul_Ioi hNeg 0
    have hEqF : (fun x : ℝ => Real.exp (-(β * x))) = fun x : ℝ => Real.exp ((-β) * x) := by
      funext x; congr 1; ring
    rw [hEqF, hEq]; simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  have hTail : ∀ (a K β0 : ℝ), 0 < a →
      Tendsto (fun b : ℝ => b * Real.exp (-(b - β0) * a) * K) atTop (𝓝 0) := by
    intro a K β0 ha
    have hMid : Tendsto (fun b : ℝ => b * Real.exp (-(a * b))) atTop (𝓝 0) := by
      have hC := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (Tendsto.const_mul_atTop ha tendsto_id)
      have hS : Tendsto (fun b : ℝ => (1 / a) * ((a * b) ^ 1 * Real.exp (-(a * b)))) atTop (𝓝 ((1 / a) * 0)) := tendsto_const_nhds.mul hC
      rw [mul_zero] at hS
      have hEq : (fun b : ℝ => (1 / a) * ((a * b) ^ 1 * Real.exp (-(a * b)))) =ᶠ[atTop] (fun b : ℝ => b * Real.exp (-(a * b))) :=
        Eventually.of_forall fun b => by simp only [pow_one]; field_simp [ne_of_gt ha]
      exact Tendsto.congr' hEq hS
    have hS : Tendsto (fun b : ℝ => K * (Real.exp (β0 * a) * (b * Real.exp (-(a * b))))) atTop (𝓝 (K * (Real.exp (β0 * a) * 0))) := tendsto_const_nhds.mul (tendsto_const_nhds.mul hMid)
    rw [mul_zero, mul_zero] at hS
    have hEq2 : (fun b : ℝ => K * (Real.exp (β0 * a) * (b * Real.exp (-(a * b))))) =ᶠ[atTop] (fun b : ℝ => b * Real.exp (-(b - β0) * a) * K) :=
      Eventually.of_forall fun b => by
        have hE : Real.exp (-(b - β0) * a) = Real.exp (-(a * b)) * Real.exp (β0 * a) := by
          rw [show -(b - β0) * a = -(a * b) + β0 * a from by ring, Real.exp_add]
        simp only [hE]; ring
    exact Tendsto.congr' hEq2 hS
  exact ⟨hI, hV, hTail⟩
