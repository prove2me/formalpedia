-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_source_frozen_prefix_weighted_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:23:59.569095+00:00
-- url     : https://prove2.me/submissions/ffb162d9-00e9-4e75-b746-f1d650c29eb6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_marked_rectangle
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n k : ℕ) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X (min u (n : ℝ≥0)) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X (min u (n : ℝ≥0)) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u))))  := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let ν : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X (min u (n : ℝ≥0)) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X (min u (n : ℝ≥0)) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u))
  let g : ℝ → ℝ≥0∞ :=
    fun z => if z < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-z) else 0
  have hg : Measurable g :=
    avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable k
  have hrect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 (n : ℝ≥0) ×ˢ B) =
        ν (Ioc 0 (0 + (n : ℝ≥0)) ×ˢ B) := by
    intro B hB
    simpa only [zero_add, μ, ν] using
      (avram_bv_jump8_original_frozen_prefix_marked_rectangle X ω n B hB)
  have hw := avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
    μ ν 0 (n : ℝ≥0) g hg hrect
  simpa [μ, ν, g, and_assoc, ite_and] using hw
