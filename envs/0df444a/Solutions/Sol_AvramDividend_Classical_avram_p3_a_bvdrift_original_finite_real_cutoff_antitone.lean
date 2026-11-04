-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_finite_real_cutoff_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:41:27.364976+00:00
-- url     : https://prove2.me/submissions/646889e7-9ead-4635-8382-4a77ea0047d3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On one original BV full event, all real-valued finite negative-jump
threshold sums decrease as the cutoff increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (ε₁ ε₂ : ℝ≥0∞), ε₁ ≤ ε₂ →
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ T ∧ ε₂ <
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal ≤
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ T ∧ ε₁ <
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal := by
  filter_upwards
    [avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top X hBV]
    with ω hω
  intro T ε₁ ε₂ hε
  let J (u : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
  let full : ℝ≥0∞ :=
    ∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then J u else 0
  let cut : ℝ≥0∞ → ℝ≥0∞ := fun ε =>
    ∑' u : ℝ≥0, if 0 < u ∧ u ≤ T ∧ ε < J u then J u else 0
  have hfull : full ≠ ⊤ :=
    ne_of_lt (hω 0 T (show (0 : ℝ≥0) ≤ T from zero_le))
  have hcut_le (ε : ℝ≥0∞) : cut ε ≤ full := by
    apply ENNReal.tsum_le_tsum
    intro u
    by_cases hu : 0 < u ∧ u ≤ T ∧ ε < J u
    · have hle : 0 < u ∧ u ≤ T := ⟨hu.1, hu.2.1⟩
      simp [hu, hle]
    · simp [hu]
  have hcut_fin : cut ε₁ ≠ ⊤ :=
    ne_top_of_le_ne_top hfull (hcut_le ε₁)
  have hmono : cut ε₂ ≤ cut ε₁ :=
    avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone
      X T ω ε₁ ε₂ hε
  change (cut ε₂).toReal ≤ (cut ε₁).toReal
  exact ENNReal.toReal_mono hcut_fin hmono
