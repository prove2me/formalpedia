-- Prove2me | solution 1 for DbarRegularity.eLpNorm_fourier_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T15:27:06.152404+00:00
-- url     : https://prove2.me/submissions/b89b9965-4a3d-4db7-b3c5-fcbe54406a5b

import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_fourierTransformL2_ae_eq_fourier



namespace DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

/-- Plancherel on `L¹ ∩ L²` for the Fourier integral. -/
theorem eLpNorm_fourier_two_eq_aux {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) : eLpNorm (𝓕 g) 2 volume = eLpNorm g 2 volume := by
  rw [← eLpNorm_congr_ae (fourierTransformL2_ae_eq_fourier g hg1 hg2), ← Lp.enorm_def,
    enorm_eq_nnnorm, LinearIsometryEquiv.nnnorm_map, ← enorm_eq_nnnorm, Lp.enorm_def]
  exact eLpNorm_congr_ae hg2.coeFn_toLp

end DbarRegularity

open DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

theorem solution {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg1 : Integrable g volume)
    (hg2 : MemLp g 2 volume) : eLpNorm (𝓕 g) 2 volume = eLpNorm g 2 volume :=
  eLpNorm_fourier_two_eq_aux g hg1 hg2
