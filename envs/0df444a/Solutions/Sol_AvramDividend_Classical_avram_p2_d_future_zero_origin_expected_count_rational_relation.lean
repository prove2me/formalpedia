-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_zero_origin_expected_count_rational_relation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:31:11.808978+00:00
-- url     : https://prove2.me/submissions/a5aee8c7-ee60-4fb2-87eb-5f087afdcf9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_scaling
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_multiple

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original rationally related time-horizon scaling in ENNReal, with
infinite mean handled by cancellation of a finite positive denominator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B : Set ℝ) (hB : MeasurableSet B)
    (t : ℝ≥0) (n d : ℕ) (hd : 0 < d)
    (hrel : (d : ℝ≥0) * t = (n : ℝ≥0)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ B) ∂P) =
      ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  let M : ℝ≥0 → ℝ≥0∞ := fun q => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 q ×ˢ B) ∂P)
  have hNat : M (n : ℝ≥0) = (n : ℝ≥0∞) * M 1 := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_nat_scaling X B hB n)
  have hMultiple : M ((d : ℝ≥0) * t) = (d : ℝ≥0∞) * M t := by
    simpa only [M] using
      (avram_p2_d_future_zero_origin_expected_count_nat_multiple X B hB t d)
  have hRate : (d : ℝ≥0∞) * M t = (n : ℝ≥0∞) * M 1 := by
    calc
      _ = M ((d : ℝ≥0) * t) := hMultiple.symm
      _ = M (n : ℝ≥0) := by rw [hrel]
      _ = (n : ℝ≥0∞) * M 1 := hNat
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  have hdTop : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hdUnit : (d : ℝ≥0∞)⁻¹ * (d : ℝ≥0∞) = 1 := by
    rw [mul_comm]
    exact ENNReal.mul_inv_cancel hd0 hdTop
  change M t = ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1
  calc
    M t = ((d : ℝ≥0∞)⁻¹ * (d : ℝ≥0∞)) * M t := by
      rw [hdUnit, one_mul]
    _ = (d : ℝ≥0∞)⁻¹ * ((d : ℝ≥0∞) * M t) := by
      rw [mul_assoc]
    _ = (d : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) * M 1) := by
      rw [hRate]
    _ = ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * M 1 := by
      rw [div_eq_mul_inv]
      ac_rfl