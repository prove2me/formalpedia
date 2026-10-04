-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.norm_shiftMap_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:59:42.356464+00:00
-- url     : https://prove2.me/submissions/adf79396-e697-448d-bc91-0636ebd00764

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
    {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (x : Dom) :
    γ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ := by
  have hre : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re = quadForm A x + γ * ‖(x : F)‖ ^ 2 := by
    have happ : shiftMap A γ x = A x + (γ : ℂ) • (x : F) := rfl
    rw [happ, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.add_re]
    simp [quadForm, ← Complex.ofReal_pow]
  have h2 : (inner ℂ (x : F) (shiftMap A γ x) : ℂ).re ≤ ‖(x : F)‖ * ‖shiftMap A γ x‖ :=
    le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
  rw [hre] at h2
  have hq := hpos x
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | hpx
  · rw [← h0]; simp
  · have : γ * ‖(x : F)‖ * ‖(x : F)‖ ≤ ‖shiftMap A γ x‖ * ‖(x : F)‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpx
