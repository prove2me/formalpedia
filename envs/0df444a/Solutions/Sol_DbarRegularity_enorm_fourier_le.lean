-- Prove2me | solution 1 for DbarRegularity.enorm_fourier_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:22:52.075234+00:00
-- url     : https://prove2.me/submissions/69e3b1dd-6e58-4154-a3d0-e1bbb5ca81ed

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

/-- `‖𝓕 f‖_∞ ≤ ‖f‖₁`, pointwise. -/
theorem enorm_fourier_le {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Integrable f volume)
    (ξ : EuclideanSpace ℝ (Fin d)) : ‖𝓕 f ξ‖ₑ ≤ eLpNorm f 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hf,
    ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _)

end DbarRegularity

open DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

theorem solution {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Integrable f volume)
    (ξ : EuclideanSpace ℝ (Fin d)) : ‖𝓕 f ξ‖ₑ ≤ eLpNorm f 1 volume :=
  enorm_fourier_le f hf ξ
