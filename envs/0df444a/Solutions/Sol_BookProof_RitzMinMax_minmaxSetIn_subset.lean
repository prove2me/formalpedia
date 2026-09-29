-- Prove2me | solution 1 for BookProof.RitzMinMax.minmaxSetIn_subset
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:35:21.230716+00:00
-- url     : https://prove2.me/submissions/503e7cbf-d88f-49b0-80ac-0b8462dd5c02

-- Generated from ChapterSirkRitzMinMax.lean — theorem BookProof.RitzMinMax.minmaxSetIn_subset
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax









noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option autoImplicit false


theorem solution (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    minmaxSetIn T W k ⊆ minmaxSet T k := by
  rintro r ⟨S, hSW, hd, hr⟩
  exact ⟨S, hd, hr⟩

#print axioms solution
