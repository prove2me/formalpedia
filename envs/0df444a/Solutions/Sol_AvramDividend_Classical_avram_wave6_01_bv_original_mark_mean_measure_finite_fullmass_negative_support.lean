-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_bv_original_mark_mean_measure_finite_fullmass_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:11:30.259796+00:00
-- url     : https://prove2.me/submissions/f860d270-a523-4300-ba95-70c05d66e8b6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_jump_mark_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_total_jump_intensity_gridfree
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ ρ : Measure ℝ,
      ρ (Set.univ : Set ℝ) =
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) ∧
      ρ (Ici (0 : ℝ)) = 0 ∧
      ρ (Set.univ : Set ℝ) < ⊤ ∧
      ∀ B : Set ℝ, MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) := by
  classical
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hPast : MeasurableSet[𝓕 0] (Set.univ : Set Ω) :=
    MeasurableSet.univ
  obtain ⟨ρ, hρ⟩ :=
    avram_wave6_01_original_past_expected_jump_mark_measure_exists
      X 0 T (zero_le) Set.univ hPast
  have hρAll : ρ (Set.univ : Set ℝ) =
      ∫⁻ ω, N ω (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P := by
    have hh := hρ Set.univ MeasurableSet.univ
    change ρ Set.univ =
      ∫⁻ ω in Set.univ, N ω (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P at hh
    simpa using hh
  have hTotal :
      (∫⁻ ω, N ω (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) ∂P) =
        (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    exact avram_wave6_01_bv_original_total_jump_intensity_gridfree
      X hBV hFinite T hT
  have hZero : ρ (Ici (0 : ℝ)) = 0 := by
    have hh := hρ (Ici (0 : ℝ)) measurableSet_Ici
    change ρ (Ici (0 : ℝ)) =
      ∫⁻ ω in Set.univ, N ω (Ioc 0 T ×ˢ Ici (0 : ℝ)) ∂P at hh
    rw [hh]
    simp only [Measure.restrict_univ]
    have hPoint (ω : Ω) :
        N ω (Ioc 0 T ×ˢ Ici (0 : ℝ)) = 0 :=
      avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
        X ω 0 T
    simp only [hPoint]
    simp
  have hMass : ρ (Set.univ : Set ℝ) =
      (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) :=
    hρAll.trans hTotal
  have hMassFinite : ρ (Set.univ : Set ℝ) < ⊤ := by
    rw [hMass]
    exact ENNReal.mul_lt_top (by simp) hFinite
  refine ⟨ρ, hMass, hZero, hMassFinite, ?_⟩
  intro B hB
  have hh := hρ B hB
  change ρ B = ∫⁻ ω in Set.univ, N ω (Ioc 0 T ×ˢ B) ∂P at hh
  simpa using hh
