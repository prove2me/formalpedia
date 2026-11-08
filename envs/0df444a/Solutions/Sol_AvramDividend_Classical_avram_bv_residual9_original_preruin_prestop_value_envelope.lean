-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_original_preruin_prestop_value_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:47:09.923929+00:00
-- url     : https://prove2.me/submissions/4cad6a94-055c-499d-9262-4597c677979d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original pre-ruin BV drift strip also uniformly bounds the literal pre-jump value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ≥0∞) < ruinTime X x D ω →
        |w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)| ≤ K := by
  let H : ℝ := max (x + (T : ℝ) * X.drift) 0
  have hsub : Icc (0 : ℝ) H ⊆ Ici (0 : ℝ) := by
    intro z hz
    exact hz.1
  have hcont : ContinuousOn w (Icc (0 : ℝ) H) := hw_cont.mono hsub
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max K₀ 0, le_max_right _ _, ?_⟩
  have hstrip :=
    avram_wave7_02_original_BV_full_preruin_postpayment_closed_physical_drift_strip
      X hX hBV x C hxc D hD T
  filter_upwards [hstrip] with ω hω
  intro t ht hpre
  let f : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  have hbounded : ∀ s : ℝ≥0, s ≤ t → f s ∈ Icc (0 : ℝ) H := by
    intro s hs
    have hsT : s ≤ T := hs.trans ht
    have hsruin : (s : ℝ≥0∞) < ruinTime X x D ω := by
      have hst : (s : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by exact_mod_cast hs
      exact lt_of_le_of_lt hst hpre
    obtain ⟨hlo, _, hhi⟩ := hω s hsT (Or.inr hsruin)
    exact ⟨hlo, hhi.trans (le_max_left _ _)⟩
  have hmem : ∀ᶠ s in 𝓝[≤] t, f s ∈ Icc (0 : ℝ) H := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbounded s hs
  have hz : f.leftLim t ∈ Icc (0 : ℝ) H :=
    isClosed_Icc.mem_of_mapClusterPt (mapClusterPt_leftLim f t) hmem
  have hb : ‖w (f.leftLim t)‖ ≤ K₀ := hK₀ _ hz
  have habs : |w (f.leftLim t)| ≤ K₀ := by
    simpa only [Real.norm_eq_abs] using hb
  exact habs.trans (le_max_left _ _)
