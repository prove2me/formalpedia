-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_Borel_occupied_grid_binomial_law_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:35:17.825067+00:00
-- url     : https://prove2.me/submissions/eb3331ef-491f-4050-8b16-2331cec8635b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_probability_void_complement_is_unitInterval_parameter_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_negative_Borel_grid_occupied_indicator_iid_20261116
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a27_same_source_ENNReal_occupied_Bernoulli_parameter_corrected_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_occupied_Borel_grid_indicator_zero_one_and_card_sum_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_binomial_law_transport_from_original_iid_sum_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    ∃ p : ℕ → unitInterval,
      (∀ n : ℕ, (p n : ℝ) =
        1 - (P {ω : Ω | NX ω (Ioc 0 (δ n) ×ˢ B) = 0}).toReal) ∧
      ∀ n : ℕ, P.map (Z n) = Bin(n, p n) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
  let Z : ℕ → Ω → ℕ := fun n ω =>
    ((Finset.range n).filter (fun i : ℕ =>
      NX ω (Ioc ((i : ℝ≥0) * δ n)
        (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
  let E : ℕ → Set Ω := fun n => {ω : Ω |
    NX ω (Ioc 0 (δ n) ×ˢ B) = 0}
  obtain ⟨p, hp⟩ :=
    avram_a26_probability_void_complement_is_unitInterval_parameter_20261116 P E
  refine ⟨p, ?_, ?_⟩
  · intro n
    simpa only [E, NX, δ] using hp n
  · intro n
    let Y : Fin n → Ω → ℕ := fun i ω =>
      if NX ω (Ioc ((i.val : ℝ≥0) * δ n)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) = 0
      then 0 else 1
    obtain ⟨hMeas, hIndep, hSame⟩ :=
      avram_a26_original_negative_Borel_grid_occupied_indicator_iid_20261116
        X hFinite T B hB hNeg n
    have hMeas' : ∀ i : Fin n, Measurable (Y i) := by
      simpa only [NX, δ, Y] using hMeas
    have hIndep' : iIndepFun Y P := by
      simpa only [NX, δ, Y] using hIndep
    have hBoth :=
      avram_a27_original_occupied_Borel_grid_indicator_zero_one_and_card_sum_20261116
        X T B n
    have h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1 := by
      simpa only [NX, δ, Y] using hBoth.1
    let C : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc 0 (δ n) ×ˢ B)
    have hC : Measurable C := by
      simpa only [C, NX] using
        (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
          X 0 (δ n) bot_le B hB)
    have hSame' : ∀ i : Fin n,
        P {ω : Ω | Y i ω = 1} = P {ω : Ω | C ω ≠ 0} := by
      simpa only [Y, C, NX, δ] using hSame
    have hp' : (p n : ℝ) = 1 - (P {ω : Ω | C ω = 0}).toReal := by
      simpa only [E, C] using hp n
    have hP :=
      avram_a27_same_source_ENNReal_occupied_Bernoulli_parameter_corrected_20261116
        P n Y C hC hSame' (p n) hp'
    have hZ : ∀ ω : Ω, Z n ω = ∑ i : Fin n, Y i ω := by
      simpa only [NX, δ, Z, Y] using hBoth.2
    exact avram_a27_binomial_law_transport_from_original_iid_sum_20261116
      P n Y hMeas' h01 hIndep' (p n) hP (Z n) hZ
