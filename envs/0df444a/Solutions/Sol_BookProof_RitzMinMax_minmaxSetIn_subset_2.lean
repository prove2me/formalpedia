-- Prove2me | solution 2 for BookProof.RitzMinMax.minmaxSetIn_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T18:27:19.630879+00:00
-- url     : https://prove2.me/submissions/e30395a2-d7a6-46a9-97e0-9dd6b1a25d60

-- Generated from ChapterSirkRitzMinMax.lean — solution of BookProof.RitzMinMax.minmaxSetIn_subset
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax










noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxSetIn T W k ⊆ minmaxSet T k := by

  rintro t ⟨S, _, hrank, rfl⟩
  exact ⟨S, hrank, rfl⟩
