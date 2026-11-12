-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja20_original_pointwise_finite_total_count_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:14:38.584104+00:00
-- url     : https://prove2.me/submissions/aa767377-3b63-4e92-81ef-adac8dd31360

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18j_public_original_compensated_finsum
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
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
    (k : ℕ) (T : ℝ≥0) (ω : Ω)
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔
         0 < u ∧ u ≤ T ∧
         -1 < X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
         X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
           -(1 / ((k : ℝ) + 1))) ∧
      (F.card : ℝ) ≤
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by
  classical
  let N : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  obtain ⟨F, hF, _⟩ :=
    avram_ja18j_public_original_compensated_finsum X k T ω
  refine ⟨F, hF, ?_⟩
  let B : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((k : ℝ) + 1))}
  have hB : B.Finite :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω T k
  have hFB : F ⊆ hB.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset]
    have hu' := (hF u).mp hu
    exact ⟨hu'.1, hu'.2.1, hu'.2.2.2⟩
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hneg : -(1 / ((k : ℝ) + 1)) < 0 := by
    have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) :=
      div_pos (by norm_num) hk
    linarith
  have hbandLe :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1)))) ≤ N := by
    apply measure_mono
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    exact ⟨hu, lt_of_le_of_lt hz hneg⟩
  have hcount :=
    avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω T k
  rw [Set.ncard_eq_toFinset_card _ hB] at hcount
  have hcard : (F.card : ℝ≥0∞) ≤ N := by
    calc
      (F.card : ℝ≥0∞) ≤ (hB.toFinset.card : ℝ≥0∞) := by
        exact_mod_cast Finset.card_le_card hFB
      _ = _ := hcount.symm
      _ ≤ N := hbandLe
  have hNtop : N ≠ ⊤ := ne_of_lt (show N < ⊤ from hNfin)
  have hh := ENNReal.toReal_mono hNtop hcard
  simpa only [ENNReal.toReal_natCast] using hh
