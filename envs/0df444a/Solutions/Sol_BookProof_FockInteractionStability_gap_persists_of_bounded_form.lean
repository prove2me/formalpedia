-- Prove2me | solution 1 for BookProof.FockInteractionStability.gap_persists_of_bounded_form
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:12:50.390344+00:00
-- url     : https://prove2.me/submissions/55fd1214-a881-4797-a519-90c19f632903

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.gap_persists_of_bounded_form
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

theorem solution
    {q v : E → ℝ} {S : Set E} {mu b : ℝ}
    (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x)
    (hv : ∀ x, |v x| ≤ b * ‖x‖ ^ 2) :
    ∀ x ∈ S, (mu - b) * ‖x‖ ^ 2 ≤ q x + v x := by
  intro x hx
  have hq' := hq x hx
  have hv' := (abs_le.mp (hv x)).1
  nlinarith

#print axioms solution
