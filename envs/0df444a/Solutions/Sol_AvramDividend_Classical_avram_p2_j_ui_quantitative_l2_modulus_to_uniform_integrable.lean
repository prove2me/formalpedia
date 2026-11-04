-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:44:03.44597+00:00
-- url     : https://prove2.me/submissions/9699bf65-316d-4c4c-a6d2-1f90eaeef7ca

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal

/-! A quantitative square-root restriction estimate gives uniform integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 1 P ≤ (B : ENNReal))
    (hlocal : ∀ n (s : Set Ω),
      eLpNorm (Y n) 1 (P.restrict s) ≤
        (B : ENNReal) * (P s) ^ (1 / 2 : ℝ)) :
    UniformIntegrable Y 1 P := by
  have hunif : UnifIntegrable Y 1 P := by
    intro ε hε
    have hEps : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    obtain ⟨c, hc, hmul⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt
        (a := (B : ENNReal)) (b := ENNReal.ofReal ε)
        (by simp) (ne_of_gt hEps)
    have hcoe : ENNReal.ofReal ((c : ℝ) ^ 2) = (c : ENNReal) ^ 2 := by
      simp
    have hpow :
        (ENNReal.ofReal ((c : ℝ) ^ 2)) ^ (1 / 2 : ℝ) = (c : ENNReal) := by
      rw [hcoe]
      simpa [ENNReal.rpow_two] using
        (ENNReal.rpow_mul (c : ENNReal) 2 (1 / 2 : ℝ)).symm
    refine ⟨(c : ℝ) ^ 2, by positivity, ?_⟩
    intro n s hs hμ
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    calc
      eLpNorm (Y n) 1 (P.restrict s) ≤
          (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := hlocal n s
      _ ≤ (B : ENNReal) *
          (ENNReal.ofReal ((c : ℝ) ^ 2)) ^ (1 / 2 : ℝ) := by
          gcongr <;> exact hμ
      _ = (B : ENNReal) * (c : ENNReal) := by rw [hpow]
      _ ≤ ENNReal.ofReal ε := by rw [mul_comm]; exact le_of_lt hmul
  exact ⟨hm, hunif, ⟨B, hB⟩⟩
