-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_localised_physical_C1_global_NX_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:45:20.783323+00:00
-- url     : https://prove2.me/submissions/a179570a-1442-47ce-8b64-7939c8e3722e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original BV compact C1 localisation supplies integrability
    of the physical source on the global original marked jump count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      let E : Set (ℝ≥0 × ℝ) :=
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NX : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
            (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NX := by
  obtain ⟨_, _, _, _, _, L, R, hL, hR, hLip, hWbound⟩ :=
    AvramDividend.Classical.avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
      X hBV x C D hD w hw_cont hw_neg hwC1 T a b ha hab hBand
  have hInt :=
    AvramDividend.Classical.avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
      X hBV x C D hD w hw_cont hw_neg q a b L R
        hq ha hab hL hR hLip hWbound
  filter_upwards [hInt] with ω hω
  exact hω T
