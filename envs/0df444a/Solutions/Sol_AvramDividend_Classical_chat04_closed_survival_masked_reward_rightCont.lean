-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_survival_masked_reward_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:06:58.38275+00:00
-- url     : https://prove2.me/submissions/05ae96fc-afe4-4895-b283-d1e46a3e5579

import Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
import Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_locally_stable_of_rightCont_positive
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical AvramDividend.Classical Filter Set Topology

/-- The whole-history survival mask preserves a right-continuous payoff when
    the payoff vanishes at the zero-reserve boundary. -/
theorem solution
    (f g : NNReal → ℝ) (t : NNReal)
    (hfcont : ContinuousWithinAt f (Ici t) t)
    (hgcont : ContinuousWithinAt g (Ici t) t)
    (hzero : f t = 0 → g t = 0) :
    ContinuousWithinAt
      (fun u : NNReal => if (∀ s : NNReal, s ≤ u → 0 ≤ f s) then g u else 0)
      (Ici t) t := by
  classical
  refine chat04_rightContinuous_masked_reward_of_zero_boundary
    g (fun u : NNReal => ∀ s : NNReal, s ≤ u → 0 ≤ f s) t hgcont ?_ ?_
  · intro hsurv hnz
    have hft : 0 ≤ f t := hsurv t le_rfl
    have hpos : 0 < f t := by
      rcases lt_or_eq_of_le hft with hlt | heq
      · exact hlt
      · exact False.elim (hnz (hzero heq.symm))
    exact chat04_closed_survival_locally_stable_of_rightCont_positive
      f t hfcont hpos hsurv
  · intro hnot
    have hge : ∀ᶠ u in 𝓝[Ici t] t, t ≤ u := self_mem_nhdsWithin
    filter_upwards [hge] with u htu hu
    apply hnot
    intro s hst
    exact hu s (hst.trans htu)
