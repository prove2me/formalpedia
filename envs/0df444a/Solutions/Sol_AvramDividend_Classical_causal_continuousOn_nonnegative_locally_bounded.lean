-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuousOn_nonnegative_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:15:19.243751+00:00
-- url     : https://prove2.me/submissions/51d76aaf-af10-4e2b-9ef4-91d859c23962

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set
open scoped Topology
theorem solution
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |g s| ≤ C := by
  intro R _
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn
    ((hg.mono Icc_subset_Ici_self).norm)).isBounded.bddAbove
  exact ⟨C, fun s hs => hC ⟨s, Ioc_subset_Icc_self hs, rfl⟩⟩
