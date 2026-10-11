-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:37:51.882143+00:00
-- url     : https://prove2.me/submissions/5f565758-4823-437b-960d-229c8698f103

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.integral_deriv_eq_zero_of_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {u : ℝ → ℂ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) : ∫ t : ℝ, deriv u t = 0 := by

  have hcd : Continuous (deriv u) := hu.continuous_deriv le_rfl
  have hint : Integrable (deriv u) :=
    hcd.integrable_of_hasCompactSupport (huc.deriv)
  have h1 : ∫ x in Iic (0 : ℝ), deriv u x = u 0 :=
    HasCompactSupport.integral_Iic_deriv_eq hu huc 0
  have h2 : ∫ x in Ioi (0 : ℝ), deriv u x = -u 0 :=
    HasCompactSupport.integral_Ioi_deriv_eq hu huc 0
  have h3 := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (f := deriv u) (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn
  rw [h1, h2] at h3
  simpa using h3.symm
