-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:36:01.878205+00:00
-- url     : https://prove2.me/submissions/04c7ad7e-e3b1-4d7b-ba0c-e54078c582f5

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_closed_cap_continuous_kernel_mask_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original K mark rate is measurable using a locally equal measurable reserve proxy. -/
theorem solution
    (C τ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T) (n : ℕ)
    (U V : ℝ≥0 → ℝ) (hV : Measurable V)
    (hUV : ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T → U t = V t)
    (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ τ ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then Real.exp (-(q * (t : ℝ))) * ψ (U t)
      else 0) := by
  classical
  let A : Set ℝ≥0 := {t | 0 < t ∧
    (t : ℝ) < T - T / ((n : ℝ) + 2) ∧ (t : ℝ≥0∞) ≤ τ}
  have hR : Measurable (fun t : ℝ≥0 => (t : ℝ)) :=
    measurable_coe_nnreal_real
  have hEN : Measurable (fun t : ℝ≥0 => (t : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_Ioi.inter
      ((measurableSet_Iio.preimage hR).inter
        (measurableSet_Iic.preimage hEN))
  let F : ℝ≥0 → ℝ := fun t =>
    if 0 ≤ V t ∧ ENNReal.ofReal (V t) ≤ C then ψ (V t) else 0
  have hF : Measurable F :=
    avram_bva21_closed_cap_continuous_kernel_mask_measurable
      C ψ hψ V hV
  have hW : Measurable (fun t : ℝ≥0 =>
      Real.exp (-(q * (t : ℝ))) * F t) := by
    fun_prop
  have hPiece : Measurable (fun t : ℝ≥0 =>
      if t ∈ A then Real.exp (-(q * (t : ℝ))) * F t else 0) :=
    hW.ite hA measurable_const
  have hSmall (t : ℝ≥0)
      (ht : t ∈ A) : (t : ℝ) < T := by
    have hden : 0 ≤ ((n : ℝ) + 2) := by positivity
    have hfrac : 0 ≤ T / ((n : ℝ) + 2) := div_nonneg hT.le hden
    exact lt_of_lt_of_le ht.2.1 (sub_le_self T hfrac)
  have hEq :
      (fun t : ℝ≥0 =>
        if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
            (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
        then Real.exp (-(q * (t : ℝ))) * ψ (U t) else 0) =
      (fun t : ℝ≥0 =>
        if t ∈ A then Real.exp (-(q * (t : ℝ))) * F t else 0) := by
    funext t
    by_cases ht : t ∈ A
    · have hVU : U t = V t := hUV t ht.1 (hSmall t ht)
      simp [A, F, ht, ht.1, ht.2.1, ht.2.2, hVU]
    · have hFalse : ¬ (0 < t ∧
          (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ τ ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C) := by
        intro hg
        exact ht ⟨hg.1, hg.2.1, hg.2.2.1⟩
      simp only [if_neg hFalse, if_neg ht]
  rw [hEq]
  exact hPiece
