-- Prove2me | solution 2 for BookProof.HashimotoShiftInvert.shiftMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:59:33.650739+00:00
-- url     : https://prove2.me/submissions/61c19fb0-d0b6-4726-836c-626a26fdaaaa

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
theorem p2m_norm_shiftMap_ge {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
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

open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit BookProof.HermiteGalerkin Filter Topology in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
    {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) : Function.Injective (shiftMap A γ) := by
  intro x y hxy
  have h := p2m_norm_shiftMap_ge hpos (γ := γ) (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hx : ‖((x - y : Dom) : F)‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg ((x - y : Dom) : F)]) (norm_nonneg _)
  have hz : ((x - y : Dom) : F) = 0 := norm_eq_zero.mp hx
  have hz' : x - y = 0 := Subtype.ext (by simpa using hz)
  exact sub_eq_zero.mp hz'
