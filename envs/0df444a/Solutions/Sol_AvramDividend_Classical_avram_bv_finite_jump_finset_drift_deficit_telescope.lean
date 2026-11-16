-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_finite_jump_finset_drift_deficit_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:53:22.036313+00:00
-- url     : https://prove2.me/submissions/9f3b8977-d598-4396-931a-273caa39a67f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_finite_seam_leftcontinuous_residual_constant
import Theorems.Thm_AvramDividend_Classical_avram_bva_finite_jump_compensated_residual_left_continuous
import Theorems.Thm_AvramDividend_Classical_avram_bva_finite_jumpfree_compensated_residual_constant
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (h0 : f 0 = 0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t, f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    Finset.sum hFinite.toFinset
      (fun t => Function.leftLim f t - f t) =
      (T : ℝ) * drift - f T := by
  classical
  let S : Finset ℝ≥0 := hFinite.toFinset
  let g : ℝ≥0 → ℝ := fun t =>
    (t : ℝ) * drift - f t -
      Finset.sum S (fun v => if v ≤ t then
        Function.leftLim f v - f v else 0)
  have hTime : ∀ u ∈ S, 0 < u ∧ u ≤ T := by
    intro u hu
    have hm := hFinite.mem_toFinset.mp hu
    exact ⟨hm.1, hm.2.1⟩
  have hStep : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ S, ¬ (s < u ∧ u ≤ t)) → g t = g s := by
    intro s t hst ht hNo
    have hCover : ∀ u ∈ Ioc s t,
        f u - Function.leftLim f u ≠ 0 → u ∈ S := by
      intro u hu hne
      apply hFinite.mem_toFinset.mpr
      exact ⟨lt_of_le_of_lt zero_le hu.1,
        le_trans hu.2 ht, hne⟩
    have h := avram_bva_finite_jumpfree_compensated_residual_constant
      f drift S s t hst hCover hNo (hFlat s t hst ht)
    exact h
  have hLeft : ∀ u ∈ S, Function.leftLim g u = g u := by
    intro u hu
    exact avram_bva_finite_jump_compensated_residual_left_continuous
      f drift T hFinite hFlat u hu
  have hGlobal := avram_bva_finite_seam_leftcontinuous_residual_constant
    g S T hTime hStep hLeft
  have hSumT : Finset.sum S
      (fun u => if u ≤ T then Function.leftLim f u - f u else 0) =
      Finset.sum S (fun u => Function.leftLim f u - f u) := by
    apply Finset.sum_congr rfl
    intro u hu
    simp [(hTime u hu).2]
  have hSum0 : Finset.sum S
      (fun u => if u ≤ (0 : ℝ≥0) then Function.leftLim f u - f u else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [not_le_of_gt (hTime u hu).1]
  dsimp [g] at hGlobal
  rw [hSumT, hSum0] at hGlobal
  simp only [NNReal.coe_zero, zero_mul, h0, sub_zero] at hGlobal
  linarith
