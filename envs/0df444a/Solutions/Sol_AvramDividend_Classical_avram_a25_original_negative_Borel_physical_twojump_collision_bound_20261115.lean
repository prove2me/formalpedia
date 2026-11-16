-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:12:20.398076+00:00
-- url     : https://prove2.me/submissions/bf07aa2e-d948-4e1f-aa74-a685e79555f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
import Theorems.Thm_AvramDividend_Classical_avram_ja36_original_negative_borel_cell_factorial_moment
import Theorems.Thm_AvramDividend_Classical_avram_a25_prob_twojump_le_half_second_factorial_mean_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A physical Borel marked source collision has quadratic intensity probability. -/
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
    (P {ω | (2 : ℝ) ≤ (N ω).toReal}).toReal ≤ r ^ 2 / 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  obtain ⟨K, hK, hEq⟩ :=
    avram_a20_original_negative_borel_nat_count_realisation
      X hFinite T B hB hNeg
  have hS : Integrable
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) =
        (((T : ℝ≥0∞) * X.ν B).toReal) ^ 2 :=
    avram_ja36_original_negative_borel_cell_factorial_moment
      X hFinite T B hB hNeg
  have hEqPoly :
      (fun ω : Ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) =ᵐ[P]
      (fun ω => (N ω).toReal * ((N ω).toReal - 1)) := by
    filter_upwards [hEq] with ω he
    exact congrArg (fun x : ℝ => x * (x - 1)) he
  have hKI : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P := by
    apply hS.1.congr
    filter_upwards [hEqPoly] with ω hc
    exact hc.symm
  have hBound :=
    avram_a25_prob_twojump_le_half_second_factorial_mean_20261115
      P K hK hKI
  have hEvt :
      {ω : Ω | 2 ≤ K ω} =ᵐ[P]
      {ω : Ω | (2 : ℝ) ≤ (N ω).toReal} := by
    filter_upwards [hEq] with ω he
    apply propext
    change (2 ≤ K ω) ↔ ((2 : ℝ) ≤ (N ω).toReal)
    constructor
    · intro hk
      have hkr : (2 : ℝ) ≤ (K ω : ℝ) := by exact_mod_cast hk
      rw [← he]
      exact hkr
    · intro hn
      have hkr : (2 : ℝ) ≤ (K ω : ℝ) := by
        rw [he]
        exact hn
      exact_mod_cast hkr
  have hP :
      (P {ω : Ω | (2 : ℝ) ≤ (N ω).toReal}).toReal =
      (P {ω : Ω | 2 ≤ K ω}).toReal :=
    congrArg ENNReal.toReal (measure_congr hEvt.symm)
  have hMean :
      (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) =
      (((T : ℝ≥0∞) * X.ν B).toReal) ^ 2 := by
    rw [integral_congr_ae hEqPoly]
    exact hS.2
  rw [← hP, hMean] at hBound
  exact hBound
