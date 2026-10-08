-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_right_continuous_of_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T09:42:18.516342+00:00
-- url     : https://prove2.me/submissions/9b6a1c33-caf4-46fb-8ac3-abcff1f6e841

import Mathlib

open Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    (f M : ℝ≥0 → ℝ)
    (hM : Monotone M)
    (hdom : ∀ u, f u ≤ M u)
    (hrepr : ∀ t, M t =
      ⨆ u : Set.Icc (0 : ℝ≥0) t, f u.1)
    (hfRight : ∀ t, Tendsto f (𝓝[≥] t) (𝓝 (f t)))
    (t : ℝ≥0) :
    ContinuousWithinAt M (Set.Ici t) t := by
  have hright : Tendsto M (𝓝[>] t) (𝓝 (M t)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [@self_mem_nhdsWithin _ _ t (Ioi t)] with s hs
      exact ha.trans_le (hM hs.le)
    · intro b hb
      let m : ℝ := (M t + b) / 2
      have htm : M t < m := by
        dsimp [m]
        linarith
      have hmb : m < b := by
        dsimp [m]
        linarith
      have hftm : f t < m := (hdom t).trans_lt htm
      have hev_ge : ∀ᶠ v in 𝓝[≥] t, f v < m :=
        (tendsto_order.1 (hfRight t)).2 m hftm
      have hev_gt : ∀ᶠ v in 𝓝[>] t, f v < m :=
        hev_ge.filter_mono (nhdsWithin_mono t Ioi_subset_Ici_self)
      rcases mem_nhdsGT_iff_exists_Ioo_subset.mp
          (show {v : ℝ≥0 | f v < m} ∈ 𝓝[>] t from hev_gt) with
        ⟨u, htu, hu⟩
      filter_upwards [Ioo_mem_nhdsGT htu] with s hs
      rw [hrepr s]
      letI : Nonempty (Icc (0 : ℝ≥0) s) :=
        ⟨⟨0, ⟨le_rfl, (zero_le : (0 : ℝ≥0) ≤ s)⟩⟩⟩
      refine (ciSup_le (fun v => ?_)).trans_lt hmb
      by_cases hvt : v.1 ≤ t
      · exact le_of_lt (((hdom v.1).trans (hM hvt)).trans_lt htm)
      · have htv : t < v.1 := lt_of_not_ge hvt
        have hvu : v.1 < u := v.2.2.trans_lt hs.2
        exact (hu ⟨htv, hvu⟩).le
  rw [← continuousWithinAt_Ioi_iff_Ici]
  exact hright
