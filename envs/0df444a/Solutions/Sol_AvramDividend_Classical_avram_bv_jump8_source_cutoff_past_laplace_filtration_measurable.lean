-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_source_cutoff_past_laplace_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:41:20.965086+00:00
-- url     : https://prove2.me/submissions/ac9c418f-33d9-4638-92c3-0345c613763e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_frozen_prefix_weighted_cutoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The weighted cutoff depends measurably on the original past path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      Measurable[𝓕 (n : ℝ≥0)] (fun ω : Ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) := by
  intro n k
  let g : ℝ → ℝ≥0∞ := fun y =>
    if y < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-y) else 0
  have hg : Measurable g := by
    exact Measurable.ite
      (measurableSet_lt measurable_id measurable_const)
      (ENNReal.measurable_ofReal.comp measurable_neg)
      measurable_const
  obtain ⟨W, hW, hExact⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel
      (n : ℝ≥0) g hg
  have hFrozen : Measurable[𝓕 (n : ℝ≥0)]
      (fun ω : Ω => W (fun t : ℝ≥0 => X.X (min t (n : ℝ≥0)) ω)) :=
    hW.comp (avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
      X (n : ℝ≥0))
  have hEq : ∀ ω : Ω,
      W (fun t : ℝ≥0 => X.X (min t (n : ℝ≥0)) ω) =
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by
    intro ω
    obtain ⟨hRight, hLeft⟩ :=
      avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
        X ω (n : ℝ≥0)
    have hPath := hExact _ hRight hLeft
    rw [avram_bv_jump8_source_frozen_prefix_weighted_cutoff X ω n k]
    calc
      W (fun t : ℝ≥0 => X.X (min t (n : ℝ≥0)) ω) = _ := hPath
      _ = _ := by
        apply lintegral_congr_ae
        filter_upwards [] with p
        by_cases ht : 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0)
        · by_cases hm : p.2 < -(1 / ((k : ℝ) + 1))
          · simp [g, ht, hm, and_assoc]
          · simp [g, ht, hm, and_assoc]
        · have hNoTriple :
              ¬ (0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
                p.2 < -(1 / ((k : ℝ) + 1))) := by
            intro h
            exact ht ⟨h.1, h.2.1⟩
          simp only [if_neg ht, if_neg hNoTriple]
  have hExp : Measurable[𝓕 (n : ℝ≥0)]
      (fun ω : Ω => Real.exp (-(W
        (fun t : ℝ≥0 => X.X (min t (n : ℝ≥0)) ω)).toReal)) :=
    Real.measurable_exp.comp ((ENNReal.measurable_toReal.comp hFrozen).neg)
  convert hExp using 1
  funext ω
  rw [hEq ω]
