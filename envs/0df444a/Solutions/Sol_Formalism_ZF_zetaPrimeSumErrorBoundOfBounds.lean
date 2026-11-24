-- Prove2me | solution 1 for Formalism.ZF.zetaPrimeSumErrorBoundOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:19.248947+00:00
-- url     : https://prove2.me/submissions/2db9a0bc-340b-4863-93d9-d3c2912d819c

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfOneLe
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfLarge
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_GzPNTOf
import Theorems.Thm_Formalism_ZF_abs_zetaPrimeSumError_le_of_large
import Theorems.Thm_Formalism_ZF_abs_zetaPrimeSumError_le_of_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex
noncomputable section
namespace Formalism.ZF
private theorem abs_zetaPrimeSumError_le_of_sqrt_log_lt (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 2 ≤ y)
    (hs : Real.sqrt (Real.log y) < 8 / c) :
    |Formalism.Gz y| ≤
      ((Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1) * y *
        Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hsq : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hlogL : Real.log y ≤ (8 / c) ^ 2 := by
    calc Real.log y = Real.sqrt (Real.log y) ^ 2 := (Real.sq_sqrt hlog).symm
      _ ≤ (8 / c) ^ 2 := pow_le_pow_left₀ hsq hs.le 2
  have hyL : y ≤ Real.exp ((8 / c) ^ 2) := by
    calc y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
      _ ≤ Real.exp ((8 / c) ^ 2) := Real.exp_le_exp.mpr hlogL
  have hinner : y * Real.log y + Real.log y + 2 ≤
      Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 := by
    have := mul_le_mul hyL hlogL hlog (Real.exp_pos _).le
    linarith
  have hcs : (c / 8) * Real.sqrt (Real.log y) ≤ 1 := by
    calc (c / 8) * Real.sqrt (Real.log y) ≤ (c / 8) * (8 / c) :=
          mul_le_mul_of_nonneg_left hs.le (by positivity)
      _ = 1 := by field_simp
  have hexp : Real.exp (-1) ≤ Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    Real.exp_le_exp.mpr (by linarith)
  set M : ℝ := Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hMe : M = M * Real.exp 1 * Real.exp (-1) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  calc |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) :=
        abs_zetaPrimeSumError_le_of_one_le y (by linarith)
    _ ≤ y * M := mul_le_mul_of_nonneg_left hinner hy0.le
    _ = y * (M * Real.exp 1 * Real.exp (-1)) := by rw [← hMe]
    _ ≤ y * (M * Real.exp 1 * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by
        apply mul_le_mul_of_nonneg_left _ hy0.le
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = M * Real.exp 1 * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring
end Formalism.ZF
end
end

set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : GzPNTOf := by
  intro hZF hLD hRH hP hRS
  obtain ⟨c₀, hc₀, hZ⟩ := hZF
  obtain ⟨c₁, C₁, hc₁, hD⟩ := hLD
  obtain ⟨C₂, hC₂, hR⟩ := hRH
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max C₁ 0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hDdef ▸ le_max_right _ _
  have hD' : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ D * Real.log (|s.im| + 2) ^ 2 := by
    intro s hs hre
    exact (hD s hs hre).trans
      (mul_le_mul_of_nonneg_right (hDdef ▸ le_max_left _ _) (sq_nonneg _))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (min c₀ c₁) (1 / 2) := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ lt_min (lt_min hc₀ hc₁) (by norm_num)
  have hc2 : c ≤ 1 / 2 := hcdef ▸ min_le_right _ _
  have hcc₀ : c ≤ c₀ := hcdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hcc₁ : c ≤ c₁ := hcdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (D + 1) +
      4 * (D + 1)) * (6 * (8 / c) ^ 3) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B =
      (Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1 := ⟨_, rfl⟩
  refine ⟨c / 8, max A B, div_pos hc (by norm_num), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  have hyE : 0 ≤ y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    mul_nonneg hy0 (Real.exp_pos _).le
  have h8c : 16 ≤ 8 / c := by
    rw [le_div_iff₀ hc]; linarith
  by_cases hs : 8 / c ≤ Real.sqrt (Real.log y)
  · have hs1 : 1 ≤ Real.sqrt (Real.log y) := by linarith
    have h := abs_zetaPrimeSumError_le_of_large c₀ c₁ D C₂ hD0 hC₂ hZ hD' hR hP hRS
      c hc hc2 hcc₀ hcc₁ y hy hs hs1
    rw [← hA] at h
    calc |Formalism.Gz y| ≤ A * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = A * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring
  · rw [not_le] at hs
    have h := abs_zetaPrimeSumError_le_of_sqrt_log_lt c hc y hy hs
    rw [← hB] at h
    calc |Formalism.Gz y| ≤ B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring
end Formalism.ZF
