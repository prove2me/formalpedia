-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_nonbuyer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:40.669722+00:00
-- url     : https://prove2.me/submissions/3ee33de4-32b5-480f-b8c8-9213e3a5adf2

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory ProbabilityTheory
open CohenPriceFairness.LocalWelfare

theorem solution {b p : ℝ} (hb : 0 < b) (hp : 0 < p) (hpb : p ≤ b) :
    (if (uniformLaw b) (Set.Iio p) = 0 then 0
      else (∫ v in Set.Iio p, v ∂(uniformLaw b)) / ((uniformLaw b) (Set.Iio p)).toReal) = p / 2 := by
  have hset : Set.Iio p ∩ Set.Icc 0 b = Set.Ico 0 p := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]; constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  have hmeas : (uniformLaw b) (Set.Iio p) = (ENNReal.ofReal b)⁻¹ * ENNReal.ofReal p := by
    unfold uniformLaw
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iio, smul_eq_mul, hset,
      Real.volume_Ico, sub_zero]
  have hne : (uniformLaw b) (Set.Iio p) ≠ 0 := by
    rw [hmeas]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (by simpa using hp)
  rw [if_neg hne, hmeas, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hb.le,
    ENNReal.toReal_ofReal hp.le]
  have hint : ∫ v in Set.Iio p, v ∂(uniformLaw b) = b⁻¹ * (p ^ 2 / 2) := by
    unfold uniformLaw
    rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hb.le, Measure.restrict_restrict measurableSet_Iio, hset,
      integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hp.le, integral_id]
    simp [smul_eq_mul]
  rw [hint]
  field_simp
