-- Prove2me | solution 1 for BookProof.ChapterH9.compress_compress
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:27:59.673393+00:00
-- url     : https://prove2.me/submissions/c40ff6bb-2458-4fb5-b4f1-865a9e594254

import Definitions.Def_ChapterH4

open BookProof.ChapterH4 ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem solution (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) :
    compress Vn X = compress J (compress Vm X) := by
  simp only [hJ, compress, adjoint_comp, comp_assoc]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
