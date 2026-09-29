-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:03:53.3202+00:00
-- url     : https://prove2.me/submissions/d442bf5a-1e67-4537-b647-351fee8e2d60

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.ritzSet_finiteModeRestrict_eq
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    ritzSet (finiteModeRestrict A b) (finiteModeDomain b) =
      {t : ℝ | ∃ u : F, u ∈ finiteModeDomain b ∧ ‖u‖ = 1 ∧ t = (inner ℂ u (A u) : ℂ).re} := by

  ext t
  constructor
  · rintro ⟨x, -, hx1, rfl⟩
    exact ⟨(x : F), x.2, hx1, rfl⟩
  · rintro ⟨u, hu, hu1, rfl⟩
    exact ⟨⟨u, hu⟩, hu, hu1, rfl⟩
