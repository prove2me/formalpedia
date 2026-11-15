-- Prove2me | solution 1 for AvramDividend.Classical.avram_a101_original_negative_borel_physical_count_centered_l2_exact_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:51:21.187209+00:00
-- url     : https://prove2.me/submissions/73392186-7c75-4cd7-bb4c-653d517848e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_exact_raw_second_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P ∧
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r := by
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hFirst :
      Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) = r := by
    simpa only [N, r] using
      avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg
  have hSecond :
      Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) = r ^ 2 + r := by
    simpa only [N, r] using
      avram_a20_original_negative_borel_exact_raw_second_moment
        X hFinite T B hB hNeg
  have hEq : (fun ω => ((N ω).toReal - r) ^ 2) =
      (fun ω => (N ω).toReal ^ 2 - (2 * r) * (N ω).toReal + r ^ 2) := by
    funext ω
    ring
  have hI : Integrable (fun ω =>
      (N ω).toReal ^ 2 - (2 * r) * (N ω).toReal + r ^ 2) P :=
    (hSecond.1.sub (hFirst.1.const_mul (2 * r))).add (integrable_const _)
  have hSqI : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P := by
    rw [hEq]
    exact hI
  refine ⟨hSqI, ?_⟩
  have hIntegral :
      (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) =
      (∫ ω, (N ω).toReal ^ 2 ∂P) -
        (2 * r) * (∫ ω, (N ω).toReal ∂P) + r ^ 2 := by
    rw [hEq]
    have hSub : Integrable (fun ω =>
        (N ω).toReal ^ 2 - (2 * r) * (N ω).toReal) P :=
      hSecond.1.sub (hFirst.1.const_mul (2 * r))
    have hMult : Integrable (fun ω => (2 * r) * (N ω).toReal) P :=
      hFirst.1.const_mul (2 * r)
    have hC : Integrable (fun _ : Ω => (r ^ 2 : ℝ)) P :=
      integrable_const _
    rw [integral_add hSub hC,
      integral_sub hSecond.1 hMult,
      integral_const_mul, integral_const]
    simp
  rw [hIntegral, hSecond.2, hFirst.2]
  ring
