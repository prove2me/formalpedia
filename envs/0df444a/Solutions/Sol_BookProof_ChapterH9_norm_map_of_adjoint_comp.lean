-- Prove2me | solution 1 for BookProof.ChapterH9.norm_map_of_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T00:54:57.005337+00:00
-- url     : https://prove2.me/submissions/de43c99f-28a7-43d3-9ed5-81774b092f5f

import Mathlib.Analysis.InnerProductSpace.Adjoint

/- The target is BookProof.ChapterH9.norm_map_of_adjoint_comp, from
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean.
Mathlib already characterizes norm-preserving operators by V*V = 1. -/
open ContinuousLinearMap

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {V : F →L[ℂ] E}
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (x : F) : ‖V x‖ = ‖x‖ := by
  exact V.norm_map_iff_adjoint_comp_self.mpr hV x

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
