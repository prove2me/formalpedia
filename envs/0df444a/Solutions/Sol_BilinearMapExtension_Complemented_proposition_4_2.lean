-- Prove2me | solution 1 for BilinearMapExtension.Complemented.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:53:12.685988+00:00
-- url     : https://prove2.me/submissions/7b0f9869-1083-4f4c-9745-fd9c8e7de7c3

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

theorem solution {𝕜 : Type*} [RCLike 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    (∀ f : X →ₗ[𝕜] Y →ₗ[𝕜] Z, (∃ C : ℝ, ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) →
      ∃! T : X →L[𝕜] Y →L[𝕜] Z, ∀ x y, T x y = f x y) ∧
    (∀ T : X →L[𝕜] Y →L[𝕜] Z, ‖T‖ = ⨆ (x : X) (y : Y), ‖T x y‖ / (‖x‖ * ‖y‖)) := by
  constructor
  · rintro f ⟨C, hC⟩
    refine ⟨f.mkContinuous₂ C hC, ?_, ?_⟩
    · intro x y
      rfl
    · intro T hT
      ext x y
      exact hT x y
  · intro T
    let R : X → Y → ℝ := fun x y => ‖T x y‖ / (‖x‖ * ‖y‖)
    have hR : ∀ x y, R x y ≤ ‖T‖ := by
      intro x y
      by_cases hx : x = 0
      · simp only [R, hx, norm_zero, zero_mul, div_zero]
        exact norm_nonneg T
      by_cases hy : y = 0
      · simp only [R, hy, norm_zero, mul_zero, div_zero]
        exact norm_nonneg T
      have hd : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
      exact (div_le_iff₀ hd).mpr (by simpa only [mul_assoc] using T.le_opNorm₂ x y)
    have hbY : ∀ x, BddAbove (Set.range (R x)) := by
      intro x
      exact ⟨‖T‖, by rintro _ ⟨y, rfl⟩; exact hR x y⟩
    have hbX : BddAbove (Set.range (fun x => ⨆ y, R x y)) := by
      refine ⟨‖T‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact ciSup_le (hR x)
    have hle : ∀ x y, R x y ≤ ⨆ x, ⨆ y, R x y := by
      intro x y
      exact (le_ciSup (hbY x) y).trans (le_ciSup hbX x)
    have hnonneg : 0 ≤ ⨆ x, ⨆ y, R x y := by
      simpa only [R, norm_zero, zero_mul, div_zero] using hle (0 : X) (0 : Y)
    apply le_antisymm
    · apply T.opNorm_le_bound₂ hnonneg
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      have hd : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
      simpa only [mul_assoc] using (div_le_iff₀ hd).mp (hle x y)
    · exact ciSup_le fun x => ciSup_le (hR x)
