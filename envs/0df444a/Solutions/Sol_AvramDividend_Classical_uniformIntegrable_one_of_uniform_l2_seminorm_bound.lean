-- Prove2me | solution 1 for AvramDividend.Classical.uniformIntegrable_one_of_uniform_l2_seminorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:54:49.819989+00:00
-- url     : https://prove2.me/submissions/c3a26f75-9ed2-4ea7-a3c2-70fb8a16810d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_indicator_l1_le_l2_sqrt_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (C : ℝ≥0)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hbound : ∀ n, eLpNorm (f n) (2 : ℝ≥0∞) μ ≤ C) :
    UniformIntegrable f (1 : ℝ≥0∞) μ := by
  refine ⟨hmeas, ?_, ⟨C, ?_⟩⟩
  · intro ε hε
    have hR : 0 < (C : ℝ) + 1 := by positivity
    have he : 0 < ε / ((C : ℝ) + 1) := div_pos hε hR
    let δ : ℝ := (ε / ((C : ℝ) + 1)) ^ 2
    have hδ : 0 < δ := sq_pos_of_pos he
    have hsqrt : (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (ε / ((C : ℝ) + 1)) := by
      dsimp [δ]
      rw [ENNReal.ofReal_pow he.le]
      simpa only [one_div, Nat.cast_ofNat] using
        (ENNReal.pow_rpow_inv_natCast (by decide : (2 : ℕ) ≠ 0)
          (ENNReal.ofReal (ε / ((C : ℝ) + 1))))
    have hfinal : (C : ℝ≥0∞) *
        ENNReal.ofReal (ε / ((C : ℝ) + 1)) ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
      apply ENNReal.ofReal_le_ofReal
      calc
        (C : ℝ) * (ε / ((C : ℝ) + 1)) ≤
            ((C : ℝ) + 1) * (ε / ((C : ℝ) + 1)) := by
              apply mul_le_mul_of_nonneg_right _ he.le
              linarith
        _ = ε := by field_simp [ne_of_gt hR]
    refine ⟨δ, hδ, ?_⟩
    intro n s hs hμs
    calc
      eLpNorm (s.indicator (f n)) (1 : ℝ≥0∞) μ ≤
          eLpNorm (f n) (2 : ℝ≥0∞) μ *
            (μ s) ^ (1 / 2 : ℝ) :=
        esscher_indicator_l1_le_l2_sqrt_measure μ (f n) s hs (hmeas n)
      _ ≤ (C : ℝ≥0∞) *
          (ENNReal.ofReal δ) ^ (1 / 2 : ℝ) := by
            gcongr
            · exact hbound n
      _ ≤ ENNReal.ofReal ε := by rw [hsqrt]; exact hfinal
  · intro n
    exact (eLpNorm_le_eLpNorm_of_exponent_le
      (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
      (by norm_num) (hmeas n)).trans (hbound n)
