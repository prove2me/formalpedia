-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_global_leftlim_value_horizon_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:56:29.541567+00:00
-- url     : https://prove2.me/submissions/31354656-8dc2-4202-a25c-7cc7f8ae25bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_global_postpayment_upper_horizon_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original physical strict-left-limit state has bounded candidate value, even after ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        |w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)| ≤ K := by
  let H : ℝ := max (x + max ((T : ℝ) * X.drift) 0) 0
  have hsub : Icc (0 : ℝ) H ⊆ Ici (0 : ℝ) := by
    intro z hz
    exact hz.1
  have hcont : ContinuousOn w (Icc (0 : ℝ) H) := hw_cont.mono hsub
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max K₀ 0, le_max_right _ _, ?_⟩
  have hglobal :=
    avram_bv_residual9_original_global_postpayment_upper_horizon_strip
      X hBV x D hD T
  filter_upwards [hglobal] with ω hω
  intro t ht
  let f : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  have hbounded : ∀ s : ℝ≥0, s ≤ t → f s ∈ Iic H := by
    intro s hs
    exact (hω s (hs.trans ht)).trans (le_max_left _ _)
  have hmem : ∀ᶠ s in 𝓝[≤] t, f s ∈ Iic H := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbounded s hs
  have hz : f.leftLim t ≤ H :=
    isClosed_Iic.mem_of_mapClusterPt (mapClusterPt_leftLim f t) hmem
  change |w (f.leftLim t)| ≤ max K₀ 0
  by_cases hpos : 0 ≤ f.leftLim t
  · have hb : ‖w (f.leftLim t)‖ ≤ K₀ :=
      hK₀ _ ⟨hpos, hz⟩
    have habs : |w (f.leftLim t)| ≤ K₀ := by
      simpa only [Real.norm_eq_abs] using hb
    exact habs.trans (le_max_left _ _)
  · have hwzero : w (f.leftLim t) = 0 :=
      hw_neg _ (lt_of_not_ge hpos)
    simpa only [hwzero, abs_zero] using (le_max_right K₀ 0)
