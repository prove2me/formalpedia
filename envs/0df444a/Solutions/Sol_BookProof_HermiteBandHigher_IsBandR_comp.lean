-- Prove2me | solution 1 for BookProof.HermiteBandHigher.IsBandR.comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:50:33.443703+00:00
-- url     : https://prove2.me/submissions/7abfc392-75e0-419a-a061-bbeca56dc452

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.IsBandR.comp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_Band_compGen
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteBand

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {r₁ r₂ m₁ m₂ : ℕ}
    {T U : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hU : IsBandR r₂ m₂ U) (hT : IsBandR r₁ m₁ T) :
    IsBandR (r₁ + r₂) (m₁ + m₂) (U ∘ₗ T) := by

  obtain ⟨M₁, C₁, hC₁, h₁⟩ := hT
  obtain ⟨M₂, C₂, hC₂, h₂⟩ := hU
  refine ⟨M₁ * M₂, M₁ * C₁ * C₂ * Real.sqrt ((r₁ : ℝ) + 1) ^ m₂, ?_,
    Band.compGen hC₁ hC₂ h₁ h₂⟩
  have h : (0:ℝ) ≤ Real.sqrt ((r₁ : ℝ) + 1) ^ m₂ := by positivity
  have h' : (0:ℝ) ≤ (M₁ : ℝ) * C₁ * C₂ := by positivity
  exact mul_nonneg h' h
