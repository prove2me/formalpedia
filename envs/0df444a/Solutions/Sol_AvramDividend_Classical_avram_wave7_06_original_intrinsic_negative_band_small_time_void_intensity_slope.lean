-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_small_time_void_intensity_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:47:17.468724+00:00
-- url     : https://prove2.me/submissions/60823cd5-0d1b-4d62-9cc2-7f520700c2b5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_nonvoid_second_order_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_occupied_cell_probability
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_bonferroni_void_rate_squeeze_atTop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (hT : 0 < T) :
    Filter.Tendsto (fun k : ℕ => (k : ℝ) *
      (1 - (P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (T / (k : ℝ≥0)) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}).toReal))
      Filter.atTop
      (nhds ((T : ℝ) * (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let J : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B)
  let K : ℝ≥0 → Ω → ℕ := fun t ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}.ncard
  have hJK (t : ℝ≥0) (ω : Ω) : J t ω = (K t ω : ℝ≥0∞) := avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card X ω t n
  have hProb (t : ℝ≥0) : 1 - (P {ω : Ω | J t ω = 0}).toReal =
      P.real {ω : Ω | K t ω ≠ 0} := by
    have hOcc := avram_wave7_06_original_negative_band_occupied_cell_probability X 0 t n
    simp only [zero_add] at hOcc
    change P {ω : Ω | J t ω ≠ 0} = 1 - P {ω : Ω | J t ω = 0} at hOcc
    have hLe : P {ω : Ω | J t ω = 0} ≤ 1 := by
      calc
        _ ≤ P Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hReal := congrArg ENNReal.toReal hOcc
    rw [ENNReal.toReal_sub_of_le hLe (by simp)] at hReal
    have hSet : {ω : Ω | J t ω ≠ 0} = {ω : Ω | K t ω ≠ 0} := by
      ext ω; simp [hJK t ω]
    rw [hSet] at hReal
    simpa [Measure.real] using hReal.symm
  let r : ℝ := (T : ℝ) * (X.ν B).toReal
  let p : ℕ → ℝ := fun k => 1 - (P {ω : Ω | J (T / (k : ℝ≥0)) ω = 0}).toReal
  have hLimit : Filter.Tendsto (fun k : ℕ => (k : ℝ) * p k) Filter.atTop (nhds r) := by
    apply avram_p4_f2_bonferroni_void_rate_squeeze_atTop r p
    intro k hk
    have hkPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hRate : (((T : ℝ≥0∞) / ((k : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) =
        r / (k : ℝ) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_div]
      have hkCast : ((k : ℝ≥0) : ℝ≥0∞) = (k : ℝ≥0∞) := by norm_cast
      rw [hkCast, ENNReal.toReal_natCast]
      norm_cast
      dsimp [r]; ring
    have hSource := avram_p4_f2_original_negative_band_nonvoid_second_order_bound X (T / (k : ℝ≥0)) n
    dsimp only at hSource
    have hkNN : (k : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    rw [ENNReal.coe_div hkNN] at hSource
    rw [hRate] at hSource
    have hp : p k = P.real {ω : Ω | K (T / (k : ℝ≥0)) ω ≠ 0} := hProb _
    rw [← hp] at hSource
    constructor
    · calc
        r - (r ^ 2 / 2) * (k : ℝ)⁻¹ =
          (k : ℝ) * (r / (k : ℝ) - (r / (k : ℝ)) ^ 2 / 2) := by
            field_simp [ne_of_gt hkPos] <;> ring
        _ ≤ (k : ℝ) * p k := mul_le_mul_of_nonneg_left hSource.1 hkPos.le
    · calc
        (k : ℝ) * p k ≤ (k : ℝ) * (r / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hSource.2 hkPos.le
        _ = r := by field_simp [ne_of_gt hkPos]
  simpa only [p, J, B, r] using hLimit
