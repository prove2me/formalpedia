-- Prove2me | solution 1 for AvramDividend.Classical.finite_positive_geometric_measure_sum_of_mass_powers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:45:03.844163+00:00
-- url     : https://prove2.me/submissions/03deaeb6-15e9-40c8-89fd-f1943413e02b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    (m : ℕ → Measure ℝ) (c r : ℝ≥0∞)
    (hc : 0 < c) (hcfinite : c ≠ ⊤)
    (hcr : c * r < 1)
    (hm : ∀ n : ℕ, m n Set.univ = r ^ n) :
    let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
    β Set.univ = c * (1 - c * r)⁻¹ ∧
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ := by
  let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
  have hmass : β Set.univ = c * (1 - c * r)⁻¹ := by
    calc
      β Set.univ =
          ∑' n : ℕ, (c * r) ^ n * c := by
        simp only [β, Measure.sum_apply _ MeasurableSet.univ,
          Measure.smul_apply, smul_eq_mul]
        congr 1
        funext n
        rw [hm n, pow_succ, mul_pow]
        ac_rfl
      _ = (∑' n : ℕ, (c * r) ^ n) * c := by
        rw [ENNReal.tsum_mul_right]
      _ = c * (1 - c * r)⁻¹ := by
        rw [ENNReal.tsum_geometric]
        ac_rfl
  have hden : 1 - c * r ≠ (0 : ℝ≥0∞) :=
    ne_of_gt (tsub_pos_iff_lt.mpr hcr)
  have hdenfinite : (1 - c * r)⁻¹ ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.inv_ne_top.mpr hden
  have hdenpos : 0 < (1 - c * r)⁻¹ := by
    exact ENNReal.inv_pos.mpr (by
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self))
  have hpositive : 0 < β Set.univ := by
    rw [hmass]
    exact ENNReal.mul_pos hc.ne' hdenpos.ne'
  have hfinite : β Set.univ ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top hcfinite hdenfinite
  exact ⟨hmass, hpositive, hfinite⟩
