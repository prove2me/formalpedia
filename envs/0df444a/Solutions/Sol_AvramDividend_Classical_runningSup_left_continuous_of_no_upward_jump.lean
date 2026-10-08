-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_left_continuous_of_no_upward_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T07:29:15.446011+00:00
-- url     : https://prove2.me/submissions/e6c75337-2164-44d5-9485-d85fd6a253e8

import Mathlib

open Filter Set Topology
open scoped NNReal ENNReal

theorem solution (f M : ℝ≥0 → ℝ)
    (hM : Monotone M)
    (hdom : ∀ u, f u ≤ M u)
    (hrepr : ∀ t, M t =
      ⨆ u : Set.Icc (0 : ℝ≥0) t, f u.1)
    (t : ℝ≥0) (ht : 0 < t) (ℓ : ℝ)
    (hfLeft : Tendsto f (𝓝[<] t) (𝓝 ℓ))
    (hNoUp : f t ≤ ℓ) :
    ContinuousWithinAt M (Iio t) t := by
  classical
  haveI : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hlim : ℓ ≤ Function.leftLim M t := by
    apply isClosed_Iic.mem_of_tendsto hfLeft
    filter_upwards [@self_mem_nhdsWithin _ _ t (Iio t)] with u hu
    exact (hdom u).trans (hM.le_leftLim hu)
  have hbound : M t ≤ Function.leftLim M t := by
    rw [hrepr t]
    letI : Nonempty (Set.Icc (0 : ℝ≥0) t) :=
      ⟨⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ t)⟩⟩⟩
    refine ciSup_le (fun u => ?_)
    rcases eq_or_lt_of_le u.2.2 with heq | hlt
    · simpa only [heq] using hNoUp.trans hlim
    · exact (hdom u.1).trans (hM.le_leftLim hlt)
  have heq : Function.leftLim M t = M t :=
    le_antisymm (hM.leftLim_le le_rfl) hbound
  exact (hM.continuousWithinAt_Iio_iff_leftLim_eq).2 heq
