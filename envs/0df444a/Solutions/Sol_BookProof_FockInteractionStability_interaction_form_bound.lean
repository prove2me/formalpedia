-- Prove2me | solution 1 for BookProof.FockInteractionStability.interaction_form_bound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:12:45.566435+00:00
-- url     : https://prove2.me/submissions/f78a08e9-d65d-49fb-8470-1f0ac355a1d2

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.interaction_form_bound
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
open BookProof.FockInteractionStability

variable {E : Type*} [NormedAddCommGroup E]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem solution [InnerProductSpace ℂ E] (V : E →L[ℂ] E) (x : E) :
    |(inner ℂ x (V x) : ℂ).re| ≤ ‖V‖ * ‖x‖ ^ 2 := by
  calc
    |(inner ℂ x (V x) : ℂ).re| ≤ ‖(inner ℂ x (V x) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖V x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖V‖ * ‖x‖) := mul_le_mul_of_nonneg_left (V.le_opNorm x) (norm_nonneg x)
    _ = ‖V‖ * ‖x‖ ^ 2 := by ring

#print axioms solution
