-- Prove2me | solution 1 for BookProof.HermiteBand.IsBand1.comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:26.023481+00:00
-- url     : https://prove2.me/submissions/c037111c-d584-4d95-acfd-f0d45c5b1145

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.IsBand1.comp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_Band_comp
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2

set_option maxHeartbeats 1000000 in
theorem solution {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBand1 U) (hT : IsBand1 T) : IsBand2 (U ∘ₗ T) := by

  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hU
  refine ⟨M₁ * M₂, 2 * M₁ * C₁ * C₂, ?_, Band.comp hC₁ hC₂ h₂ h₁⟩
  have : (0:ℝ) ≤ 2 * M₁ := by positivity
  exact mul_nonneg (mul_nonneg this hC₁) hC₂
