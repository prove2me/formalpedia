-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_smallband_negative_finsum_card_le_total_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:23:33.604413+00:00
-- url     : https://prove2.me/submissions/80112e8b-bf58-4209-8874-cb22dd5fd8e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_smallband_finsum_card_le_total_count
import Theorems.Thm_AvramDividend_Classical_avram_ja19_finsum_of_negative_unit_marks_le_card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ T : ℝ≥0,
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))
      ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t : ℝ≥0, t ≤ T →
        ∃ F : Finset ℝ≥0,
          (∀ u : ℝ≥0, u ∈ F ↔
             0 < u ∧ u ≤ t ∧
             -1 < X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
             X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
               -(1 / ((k : ℝ) + 1))) ∧
          |∑ u ∈ F,
             (X.X u ω -
                Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)| ≤
            (N ω).toReal := by
  intro T
  have hcard :=
    avram_ja19_original_smallband_finsum_card_le_total_count X hFinite T
  filter_upwards [hcard] with ω hω
  intro k t ht
  obtain ⟨F, hF, hbound⟩ := hω k t ht
  refine ⟨F, hF, ?_⟩
  have hlow : ∀ u ∈ F,
      -1 ≤ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
    intro u hu
    have hu' := (hF u).mp hu
    linarith [hu'.2.2.1]
  have hhigh : ∀ u ∈ F,
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 := by
    intro u hu
    have hu' := (hF u).mp hu
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hneg : -(1 / ((k : ℝ) + 1)) ≤ 0 := by
      have : 0 ≤ (1 : ℝ) / ((k : ℝ) + 1) := le_of_lt (div_pos (by norm_num) hk)
      linarith
    exact hu'.2.2.2.trans hneg
  exact (avram_ja19_finsum_of_negative_unit_marks_le_card
    F (fun u => X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) hlow hhigh).trans hbound
