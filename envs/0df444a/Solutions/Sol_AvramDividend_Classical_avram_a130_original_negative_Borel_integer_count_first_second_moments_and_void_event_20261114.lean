-- Prove2me | solution 1 for AvramDividend.Classical.avram_a130_original_negative_Borel_integer_count_first_second_moments_and_void_event_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:46:39.814734+00:00
-- url     : https://prove2.me/submissions/379b6392-6def-4744-9dff-57cfd024a094
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_exact_raw_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_a128_original_finite_negative_Borel_count_zero_event_eq_nat_representative_probability_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let r : ℝ := (T : ℝ) * (X.ν B).toReal
    ∃ K : Ω → ℕ,
      Measurable K ∧
      Integrable (fun ω => (K ω : ℝ)) P ∧
      Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ∂P) = r ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) = r ^ 2 + r ∧
      P {ω : Ω | K ω = 0} =
        P {ω : Ω |
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) = 0} := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := (T : ℝ) * (X.ν B).toReal
  obtain ⟨K, hK, hEq⟩ :=
    avram_a20_original_negative_borel_nat_count_realisation
      X hFinite T B hB hNeg
  have hFirst :=
    avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite T B hB hNeg
  have hSecond :=
    avram_a20_original_negative_borel_exact_raw_second_moment
      X hFinite T B hB hNeg
  have hSqEq : (fun ω => (K ω : ℝ) ^ 2) =ᵐ[P]
      (fun ω => (N ω).toReal ^ 2) := by
    filter_upwards [hEq] with ω hω
    exact congrArg (fun z : ℝ => z ^ 2) hω
  have hEqSym : (fun ω => (N ω).toReal) =ᵐ[P]
      (fun ω => (K ω : ℝ)) := by
    filter_upwards [hEq] with ω hω
    exact hω.symm
  have hSqSym : (fun ω => (N ω).toReal ^ 2) =ᵐ[P]
      (fun ω => (K ω : ℝ) ^ 2) := by
    filter_upwards [hSqEq] with ω hω
    exact hω.symm
  have hI1 : Integrable (fun ω => (K ω : ℝ)) P :=
    hFirst.1.congr hEqSym
  have hI2 : Integrable (fun ω => (K ω : ℝ) ^ 2) P :=
    hSecond.1.congr hSqSym
  have hR : ((T : ℝ≥0∞) * X.ν B).toReal = r := by
    simp [r, ENNReal.toReal_mul]
  have hMean : (∫ ω, (K ω : ℝ) ∂P) = r := by
    rw [integral_congr_ae hEq, hFirst.2, hR]
  have hSqr : (∫ ω, (K ω : ℝ) ^ 2 ∂P) = r ^ 2 + r := by
    rw [integral_congr_ae hSqEq, hSecond.2, hR]
  have hVoid :=
    avram_a128_original_finite_negative_Borel_count_zero_event_eq_nat_representative_probability_20261114
      X hFinite T B hB hNeg K hK hEq
  exact ⟨K, hK, hI1, hI2, hMean, hSqr, hVoid.symm⟩
