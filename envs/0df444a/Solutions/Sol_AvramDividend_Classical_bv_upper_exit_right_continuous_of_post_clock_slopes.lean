-- Prove2me | solution 1 for AvramDividend.Classical.bv_upper_exit_right_continuous_of_post_clock_slopes
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T15:15:14.454225+00:00
-- url     : https://prove2.me/submissions/950b5927-f0cc-4c85-85b2-eba0eb3e43f6

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

set_option autoImplicit false

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) (τ : Ω → ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) - (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) /
          (δ n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      (∀ s : ℝ≥0, s < τ ω → X.X s ω ≤ X.X (τ ω) ω) →
      twoSidedExitUpTime X (X.X (τ ω) ω) ω = (τ ω : ℝ≥0∞) ∧
      Tendsto (fun b : ℝ => twoSidedExitUpTime X b ω)
        (𝓝[Ici (X.X (τ ω) ω)] (X.X (τ ω) ω)) (𝓝 (τ ω : ℝ≥0∞)) := by
  filter_upwards [
    p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public
      X q φ hq hφ hroot hBV τ δ hδpos hRatio hCover hSlope] with ω hGerm
  intro hPast
  let a := X.X (τ ω) ω
  obtain ⟨ε, hε, hPositive⟩ := hGerm
  have lowerBound {b : ℝ} (hab : a ≤ b) :
      (τ ω : ℝ≥0∞) ≤ twoSidedExitUpTime X b ω := by
    unfold twoSidedExitUpTime
    refine le_iInf fun s => le_iInf fun hs => ENNReal.coe_le_coe.mpr ?_
    exact le_of_not_gt fun hsτ => (not_lt_of_ge ((hPast s hsτ).trans hab)) hs
  have hLimit : Tendsto (fun b : ℝ => twoSidedExitUpTime X b ω)
      (𝓝[Ici a] a) (𝓝 (τ ω : ℝ≥0∞)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro c hc
      filter_upwards [eventually_mem_nhdsWithin] with b hb
      exact hc.trans_le (lowerBound hb)
    · intro c hc
      obtain ⟨u, hu, huc⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hc
      obtain ⟨r, hr, hrMin⟩ := exists_between (lt_min hε hu)
      have hrε : r < ε := hrMin.trans_le (min_le_left _ _)
      have hru : r < u := hrMin.trans_le (min_le_right _ _)
      have hCross : a < X.X (τ ω + r) ω := sub_pos.mp (hPositive r hr hrε)
      have hTime : ((τ ω + r : ℝ≥0) : ℝ≥0∞) < c := by
        rw [ENNReal.coe_add]
        exact (add_le_add_right (ENNReal.coe_le_coe.mpr hru.le) _).trans_lt huc
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hCross)]
        with b hb
      exact (iInf_le_of_le (τ ω + r) (iInf_le _ hb)).trans_lt hTime
  have hAt := hLimit.mono_left (pure_le_nhdsWithin (self_mem_Ici : a ∈ Ici a))
  exact ⟨tendsto_nhds_unique (tendsto_pure_nhds (fun b => twoSidedExitUpTime X b ω) a) hAt,
    hLimit⟩
