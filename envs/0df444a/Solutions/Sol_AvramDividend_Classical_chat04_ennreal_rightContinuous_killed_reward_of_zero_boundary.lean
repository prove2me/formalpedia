-- Prove2me | solution 1 for AvramDividend.Classical.chat04_ennreal_rightContinuous_killed_reward_of_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:52:53.349959+00:00
-- url     : https://prove2.me/submissions/24ca7e23-bcdd-451a-8183-1fd27b478f72

import Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

/-- Extend the killed real reward continuity to nonnegative Lebesgue payoffs. -/
theorem solution
    (g : NNReal → ℝ) (S : NNReal → Prop) [DecidablePred S] (t : NNReal)
    (hg : ContinuousWithinAt g (Set.Ici t) t)
    (hsafe : S t → g t ≠ 0 → ∀ᶠ s in 𝓝[Set.Ici t] t, S s)
    (hunsafe : ¬ S t → ∀ᶠ s in 𝓝[Set.Ici t] t, ¬ S s) :
    ContinuousWithinAt
      (fun s => ENNReal.ofReal (if S s then g s else 0))
      (Set.Ici t) t := by
  have hr : ContinuousWithinAt (fun s => if S s then g s else 0)
      (Set.Ici t) t :=
    AvramDividend.Classical.chat04_rightContinuous_masked_reward_of_zero_boundary
      g S t hg hsafe hunsafe
  have ht : Tendsto (fun s => if S s then g s else 0)
      (𝓝[Set.Ici t] t) (𝓝 (if S t then g t else 0)) := hr
  change Tendsto (fun s => ENNReal.ofReal (if S s then g s else 0))
    (𝓝[Set.Ici t] t) (𝓝 (ENNReal.ofReal (if S t then g t else 0)))
  exact (ENNReal.continuous_ofReal.tendsto _).comp ht
