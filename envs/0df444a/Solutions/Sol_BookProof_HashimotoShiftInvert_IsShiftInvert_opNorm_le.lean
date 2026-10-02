-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.IsShiftInvert.opNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:39:28.119475+00:00
-- url     : https://prove2.me/submissions/e8fafa9f-27f1-472f-8341-ca3a6cffff6f

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

universe u

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) :
    ‖R‖ ≤ γ⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hγ.le) ?_
  intro u
  obtain ⟨hm, hu⟩ := h.2 u
  set x : Dom := ⟨R u, hm⟩ with hxdef
  have hxF : (x : F) = R u := rfl
  have hsm : shiftMap A γ x = A x + (γ : ℂ) • (x : F) := by
    simp [shiftMap]
  have hkey : RCLike.re (inner ℂ (x : F) u) = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    rw [← hu, hsm, inner_add_right, inner_smul_right, map_add]
    have h1 : RCLike.re ((γ : ℂ) * inner ℂ (x : F) (x : F)) = γ * ‖(x : F)‖ ^ 2 := by
      show ((γ : ℂ) * inner ℂ (x : F) (x : F)).re = _
      rw [Complex.re_ofReal_mul]
      congr 1
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (x : F)
    rw [h1]
    rfl
  have hle : RCLike.re (inner ℂ (x : F) u) ≤ ‖(x : F)‖ * ‖u‖ := re_inner_le_norm _ _
  have hq := hpos x
  rw [← hxF]
  have hmain : γ * ‖(x : F)‖ ^ 2 ≤ ‖(x : F)‖ * ‖u‖ := by linarith
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | h0
  · rw [← h0]; positivity
  · have : γ * ‖(x : F)‖ ≤ ‖u‖ := by
      have := hmain
      nlinarith
    rw [inv_mul_eq_div, le_div_iff₀ hγ]
    linarith
