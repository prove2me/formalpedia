-- Prove2me | solution 1 for DaiWeissFluid.FBFS.theorem4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T02:51:05.572343+00:00
-- url     : https://prove2.me/submissions/45f3b7a0-e726-4a83-9f97-8c7328e12491

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel
import Theorems.Thm_DaiWeissFluid_FBFS_emptying_time

open DaiWeissFluid.FBFS in
theorem solution {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) :
    DaiWeissFluid.ThreeBuffer.FluidStable (L.IsPrioritySolution (fbfs K)) := by
  refine ⟨max 1 L.fbfsEmptyingTime, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro Q T hsol hQ0 t ht k
  exact emptying_time L hm hρ Q T hsol hQ0 t (le_trans (le_max_right _ _) ht) k
