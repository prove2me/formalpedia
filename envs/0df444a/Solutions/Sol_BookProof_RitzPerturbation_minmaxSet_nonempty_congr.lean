-- Prove2me | solution 1 for BookProof.RitzPerturbation.minmaxSet_nonempty_congr
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:33:16.741265+00:00
-- url     : https://prove2.me/submissions/53a1d146-6fda-48d1-ac11-28755ecbdc96

-- Generated from ChapterSirkRitzPerturbation.lean — theorem BookProof.RitzPerturbation.minmaxSet_nonempty_congr
import Definitions.Def_ChapterSirkRitzPerturbation
open BookProof.RitzPerturbation








noncomputable section


open BookProof.RitzMinMax BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option autoImplicit false


theorem solution (T T' : F →L[ℂ] F) {k : ℕ}
    (h : (minmaxSet T k).Nonempty) : (minmaxSet T' k).Nonempty := by
  obtain ⟨r, S, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hd, rfl⟩

#print axioms solution
