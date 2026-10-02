-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.IsShiftInvert.norm_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:36:26.073683+00:00
-- url     : https://prove2.me/submissions/67f27e58-7a3c-40b9-a9f0-4ceba79dd2d5

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterComplexShiftCore
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.HashimotoShiftInvert

set_option autoImplicit false


open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

open BookProof.ChapterAbelianDiagonalCountable BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {Dom : Submodule ℂ F} {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) (hpos : ∀ x : Dom, 0 ≤ quadForm A x) (hγ : 0 < γ) (u : F) :
    ‖R u‖ ≤ γ⁻¹ * ‖u‖ := by
  obtain ⟨hx, hu⟩ := h.2 u
  set x : Dom := ⟨R u, hx⟩ with hxdef
  have hRx : R u = (x : F) := rfl
  have hshift : A x + (γ : ℂ) • (x : F) = u := by
    rw [← hu]; simp [shiftMap]
  have hq := hpos x
  unfold quadForm at hq
  -- re ⟪x, u⟫ = re ⟪x, A x⟫ + γ ‖x‖²
  have key : (inner ℂ (x : F) u).re = (inner ℂ (x : F) (A x)).re + γ * ‖(x : F)‖ ^ 2 := by
    rw [← hshift, inner_add_right, inner_smul_right, Complex.add_re,
      inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    first | exact Or.inl rfl | (left; norm_cast) | (left; simp)
  have hcs : (inner ℂ (x : F) u).re ≤ ‖(x : F)‖ * ‖u‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : γ * ‖(x : F)‖ ^ 2 ≤ ‖(x : F)‖ * ‖u‖ := by linarith
  rw [hRx]
  rcases eq_or_lt_of_le (norm_nonneg (x : F)) with h0 | h0
  · rw [← h0]; positivity
  · rw [le_inv_mul_iff₀ hγ]
    nlinarith
