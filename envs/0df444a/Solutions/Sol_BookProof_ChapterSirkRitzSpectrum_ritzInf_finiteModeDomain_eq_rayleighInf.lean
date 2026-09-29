-- Prove2me | solution 1 for BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:10:08.217498+00:00
-- url     : https://prove2.me/submissions/350ec980-0db3-4720-95f4-3676d4c38b06

-- Generated from ChapterSirkRitzSpectrum.lean — solution of BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf
import Mathlib
import Definitions.Def_ChapterSirkRitzSpectrum
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_nonempty
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_rayleighSet_bddBelow
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzSet_subset_rayleighSet
import Theorems.Thm_BookProof_ChapterSirkRitzSpectrum_ritzInf_finiteModeDomain_le
open BookProof.ChapterSirkRitzSpectrum
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit








noncomputable section


open Filter Topology RCLike ContinuousLinearMap ComplexOrder Pointwise

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial F] (A : F →L[ℂ] F)
    (b : HilbertBasis ℕ ℂ F) :
    ritzInf (finiteModeRestrict A b) (finiteModeDomain b) = rayleighInf A := by

  refine le_antisymm ?_ ?_
  · refine le_csInf (rayleighSet_nonempty A) ?_
    rintro t ⟨x, hx1, rfl⟩
    exact ritzInf_finiteModeDomain_le A b hx1
  · refine csInf_le_csInf (rayleighSet_bddBelow A) ?_ (ritzSet_subset_rayleighSet A b)
    exact ⟨(inner ℂ (b 0) (A (b 0)) : ℂ).re, ⟨⟨b 0, Submodule.subset_span ⟨0, rfl⟩⟩,
      Submodule.subset_span ⟨0, rfl⟩, b.orthonormal.1 0, rfl⟩⟩
