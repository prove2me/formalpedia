-- Prove2me | solution 1 for AvramDividend.Classical.chat04_scale_positive_shift_laplace_integrable_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:28:08.283759+00:00
-- url     : https://prove2.me/submissions/ec139503-1baf-46cf-9777-7069ffa861bf

import Mathlib.MeasureTheory.Group.Integral
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive spatial shifts preserve exponential Laplace integrability of a q-scale function. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ b : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hb : 0 ≤ b) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * W (x + b))
      (Ioi (0 : ℝ)) := by
  have hBase : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)) := by
    simpa using (scaleFunction_shiftedLaplace_integrable X q W hW θ 0 hθ hqθ (le_refl (0 : ℝ)))
  have hWhole : Integrable
      (fun x : ℝ => (Ioi (0 : ℝ)).indicator
        (fun z : ℝ => Real.exp (-(θ * z)) * W z) x) volume :=
    hBase.integrable_indicator measurableSet_Ioi
  have hMoved : IntegrableOn
      (fun x : ℝ => (Ioi (0 : ℝ)).indicator
        (fun z : ℝ => Real.exp (-(θ * z)) * W z) (x + b))
      (Ioi (0 : ℝ)) :=
    (hWhole.comp_add_right b).integrableOn
  have hScaled : IntegrableOn
      (fun x : ℝ => Real.exp (θ * b) *
        (Ioi (0 : ℝ)).indicator
          (fun z : ℝ => Real.exp (-(θ * z)) * W z) (x + b))
      (Ioi (0 : ℝ)) := hMoved.const_mul (Real.exp (θ * b))
  apply MeasureTheory.IntegrableOn.congr_fun hScaled ?_ measurableSet_Ioi
  intro x hx
  have hpos : 0 < x + b := by
    change 0 < x at hx
    linarith
  have hmem : x + b ∈ Ioi (0 : ℝ) := hpos
  change Real.exp (θ * b) *
      (Ioi (0 : ℝ)).indicator (fun z : ℝ => Real.exp (-(θ * z)) * W z) (x + b) =
        Real.exp (-(θ * x)) * W (x + b)
  rw [Set.indicator_of_mem hmem]
  calc
    Real.exp (θ * b) * (Real.exp (-(θ * (x + b))) * W (x + b)) =
        (Real.exp (θ * b) * Real.exp (-(θ * (x + b)))) * W (x + b) := by ring
    _ = Real.exp (-(θ * x)) * W (x + b) := by
      rw [← Real.exp_add]
      congr 1
      ring
