-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.recursivePaletteRamsey_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/d8e31fa1-a64c-499f-8c16-4330646dfd70

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleFree_lt_triangleRamseyNumber
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_factorial_exp_lower
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_recursivePaletteStage
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_palette_exp_loss_bound

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H a : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a)
    (hloga : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by
  obtain ⟨n, C, htriangle, _, hgrowth⟩ :=
    exists_recursivePaletteStage H a H hH ha le_rfl
  have hramsey := triangleFree_lt_triangleRamseyNumber C htriangle
  have hs : 0 < saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  have hden :
      0 < (saturatedMatrixRows H : ℝ) ^ H *
        (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
          (saturatedMatrixRows H * H) := by
    positivity
  have hsplit :
      a * saturatedMatrixRows H =
        (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
    calc
      a * saturatedMatrixRows H =
          ((a - 1) + 1) * saturatedMatrixRows H := by
        rw [Nat.sub_add_cancel (by omega)]
      _ = (a - 1) * saturatedMatrixRows H + saturatedMatrixRows H := by
        simp [Nat.add_mul]
  unfold PaletteGrowthBound at hgrowth
  nth_rewrite 1 [hsplit] at hgrowth
  rw [pow_add] at hgrowth
  have hfactor : 0 < (H.factorial : ℝ) ^ saturatedMatrixRows H := by
    positivity
  have hcancel :
      (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) ≤
        (triangleRamseyNumber (H * (a * saturatedMatrixRows H)) : ℝ) *
          (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) := by
    apply le_of_mul_le_mul_right ?_ hfactor
    calc
      (H.factorial : ℝ) ^ ((a - 1) * saturatedMatrixRows H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H ≤
        (n : ℝ) * (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H := hgrowth
      _ ≤ (triangleRamseyNumber
            (H * (a * saturatedMatrixRows H)) : ℝ) *
          (saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H) *
          (H.factorial : ℝ) ^ saturatedMatrixRows H := by
        gcongr
  calc
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      ((H : ℝ) / Real.exp 1) ^
          (H * ((a - 1) * saturatedMatrixRows H)) /
        ((saturatedMatrixRows H : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
            (saturatedMatrixRows H * H)) :=
      palette_exp_loss_bound H a (saturatedMatrixRows H)
        hH ha hs hloga
    _ ≤ (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by
      apply (div_le_iff₀ hden).mpr
      calc
        ((H : ℝ) / Real.exp 1) ^
            (H * ((a - 1) * saturatedMatrixRows H)) =
          (((H : ℝ) / Real.exp 1) ^ H) ^
            ((a - 1) * saturatedMatrixRows H) := by
          rw [pow_mul]
        _ ≤ (H.factorial : ℝ) ^
            ((a - 1) * saturatedMatrixRows H) := by
          gcongr
          exact factorial_exp_lower H (by omega)
        _ ≤ (triangleRamseyNumber
              (H * (a * saturatedMatrixRows H)) : ℝ) *
            ((saturatedMatrixRows H : ℝ) ^ H *
              (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^
                (saturatedMatrixRows H * H)) := by
          simpa [mul_assoc] using hcancel
end ErdosProblems.MulticolourTriangleRamsey
