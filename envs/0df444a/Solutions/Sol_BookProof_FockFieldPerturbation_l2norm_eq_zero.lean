-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.l2norm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:00:32.431807+00:00
-- url     : https://prove2.me/submissions/623b5be6-43d1-4793-bd19-64b30f86b39f

import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.l2norm_eq_zero
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability


theorem solution {f : ℕ →₀ ℂ} (h : l2norm f = 0) : f = 0 := by
  unfold l2norm at h
  have hnn : ∀ j ∈ f.support, (0:ℝ) ≤ ‖f j‖ ^ 2 := fun j _ => by positivity
  have hs : ∑ j ∈ f.support, ‖f j‖ ^ 2 = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp h) (Finset.sum_nonneg hnn)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hs
  ext j
  by_contra hj
  have := hs j (Finsupp.mem_support_iff.mpr hj)
  simp_all

