-- Prove2me | solution 1 for AvramDividend.Classical.positive_tilted_of_laplace_cumulative_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T09:34:01.553259+00:00
-- url     : https://prove2.me/submissions/34ce90fb-e502-4635-95cd-d1bc08bb396d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Theorems.Thm_AvramDividend_Classical_positive_tilted_of_exponential_cumulative_measure

open MeasureTheory Filter Set Topology
open scoped ENNReal
open AvramDividend.Classical

theorem solution
    (β : Measure ℝ) (φ b : ℝ) (hφ : 0 < φ)
    (hfin : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (hatom : 0 < β {0})
    (W : ℝ → ℝ)
    (htiltcont : ContinuousOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (htiltnonneg : ∀ x : ℝ, 0 < x →
      0 ≤ Real.exp (-φ * x) * W x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn
        (fun x : ℝ =>
          Real.exp (-θ * x) * (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
      IntegrableOn
        (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ),
          Real.exp (-θ * x) * (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ),
          Real.exp (-θ * x) * (β (Iic x)).toReal) :
    (∀ x : ℝ, 0 < x → 0 < W x) ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by
  let g : ℝ → ℝ := fun x => (β (Iic x)).toReal
  have hgmono : Monotone g := by
    intro x y hxy
    dsimp [g]
    exact ENNReal.toReal_mono (hfin y)
      (measure_mono (Iic_subset_Iic.mpr hxy))
  have hgmeas : AEMeasurable g (volume.restrict (Ioi (0 : ℝ))) := by
    exact hgmono.measurable.aemeasurable
  have hgright :
      ∀ x : ℝ, 0 < x → ContinuousWithinAt g (Ici x) x := by
    intro x hx
    dsimp [g]
    exact rightContinuous_cumulative_toReal_of_finite β hfin x
  have hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x := by
    intro x hx
    exact ENNReal.toReal_nonneg
  have heq :
      ∀ x : ℝ, 0 < x →
        Real.exp (-φ * x) * W x = g x := by
    exact continuous_rightContinuous_Ioi_eq_of_laplace_eq
      (fun x : ℝ => Real.exp (-φ * x) * W x) g b
      htiltcont hgright hgmeas htiltnonneg hgnonneg (by
        intro θ hθ
        simpa [g] using hlap θ hθ)
  have hrepr :
      ∀ x : ℝ, 0 < x →
        W x = Real.exp (φ * x) * (β (Iic x)).toReal := by
    intro x hx
    have h := heq x hx
    dsimp [g] at h
    have hmul := congrArg (fun z : ℝ => Real.exp (φ * x) * z) h
    have hcancel :
        Real.exp (φ * x) * Real.exp (-φ * x) = 1 := by
      rw [← Real.exp_add]
      have harg : φ * x + -φ * x = 0 := by ring
      rw [harg, Real.exp_zero]
    rw [← mul_assoc, hcancel, one_mul] at hmul
    exact hmul
  exact positive_tilted_of_exponential_cumulative_measure
    β φ hφ (fun x _ => hfin x) hatom W hrepr
