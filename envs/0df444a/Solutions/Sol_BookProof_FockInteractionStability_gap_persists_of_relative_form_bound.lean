-- Prove2me | solution 1 for BookProof.FockInteractionStability.gap_persists_of_relative_form_bound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:12:49.122149+00:00
-- url     : https://prove2.me/submissions/388bebbb-fc3d-49e4-a9e9-b249fb2ff97e

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.gap_persists_of_relative_form_bound
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
    {q v : E → ℝ} {S : Set E} {mu a b : ℝ} (ha : a ≤ 1)
    (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x)
    (hv : ∀ x, |v x| ≤ a * q x + b * ‖x‖ ^ 2) :
    ∀ x ∈ S, ((1 - a) * mu - b) * ‖x‖ ^ 2 ≤ q x + v x := by
  intro x hx
  have hv' := (abs_le.mp (hv x)).1
  have hmul := mul_le_mul_of_nonneg_left (hq x hx) (sub_nonneg.mpr ha)
  nlinarith

#print axioms solution
