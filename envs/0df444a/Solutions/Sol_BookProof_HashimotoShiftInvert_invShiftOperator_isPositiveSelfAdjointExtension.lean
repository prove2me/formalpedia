-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.invShiftOperator_isPositiveSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:06:53.504527+00:00
-- url     : https://prove2.me/submissions/18212a38-b815-4144-b645-038c0763da8a

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

open BookProof.HashimotoShiftInvert in
theorem p2m_2886b99c_adj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hR : IsSelfAdjoint R) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by
  have hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y) := by
    intro x y
    have h1 : (ContinuousLinearMap.adjoint R) = R := hR
    rw [← ContinuousLinearMap.adjoint_inner_right, h1]
  have hpre : ∀ x : F, ∀ hx : R x ∈ LinearMap.range (R : F →ₗ[ℂ] F),
      preim R ⟨R x, hx⟩ = x := by
    intro x hx
    apply hinj
    rw [preim_spec]
  set z : F := w - (γ : ℂ) • R w - R u with hz
  have hkey : ∀ x : F, inner ℂ x z = 0 := by
    intro x
    have hx : R x ∈ LinearMap.range (R : F →ₗ[ℂ] F) := ⟨x, rfl⟩
    have h := hw ⟨R x, hx⟩
    have hT : invShiftOperator R hinj γ ⟨R x, hx⟩ = x - (γ : ℂ) • R x := by
      show preim R ⟨R x, hx⟩ - (γ : ℂ) • R x = x - (γ : ℂ) • R x
      rw [hpre]
    rw [hT] at h
    simp only at h
    rw [hz, inner_sub_right, inner_sub_right, inner_smul_right, ← hsym, ← hsym,
      ← h, inner_sub_left, inner_smul_left]
    simp [Complex.conj_ofReal]
  have hz0 : z = 0 := by
    have := hkey z
    exact inner_self_eq_zero.mp this
  have hwR : w = R ((γ : ℂ) • w + u) := by
    rw [map_add, map_smul]
    have : w - (γ : ℂ) • R w - R u = 0 := hz0
    rw [sub_sub, sub_eq_zero] at this
    exact this
  have hmem : w ∈ LinearMap.range (R : F →ₗ[ℂ] F) := ⟨(γ : ℂ) • w + u, hwR.symm⟩
  refine ⟨hmem, ?_⟩
  show preim R ⟨w, hmem⟩ - (γ : ℂ) • w = u
  have hp : preim R ⟨w, hmem⟩ = (γ : ℂ) • w + u := by
    apply hinj
    rw [preim_spec]
    exact hwR
  rw [hp]
  abel

open BookProof.QgOuterFockFL BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert BookProof.FarisLavine in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R : F →L[ℂ] F)
    (hinj : Function.Injective R) (γ : ℝ) (hR : IsSelfAdjoint R)
    (hposR : ∀ u : F, γ * ‖R u‖ ^ 2 ≤ (inner ℂ (R u) u : ℂ).re)
    {D : Submodule ℂ F} (hD : D ≤ LinearMap.range (R : F →ₗ[ℂ] F)) (H : D →ₗ[ℂ] F)
    (hH : ∀ x : D, H x = invShiftOperator R hinj γ ⟨(x : F), hD x.2⟩) :
    IsPositiveSelfAdjointExtension H (invShiftOperator R hinj γ) := by
  have hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y) := by
    intro x y
    have h1 : (ContinuousLinearMap.adjoint R) = R := hR
    rw [← ContinuousLinearMap.adjoint_inner_right, h1]
  have hT : ∀ y : LinearMap.range (R : F →ₗ[ℂ] F),
      invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := fun y => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨hD x.2, (hH x).symm⟩
  · intro y z
    rw [hT, hT, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    have e1 : (inner ℂ (preim R y) (z : F) : ℂ) = inner ℂ (y : F) (preim R z) := by
      conv_lhs => rw [← preim_spec R z]
      rw [← hsym, preim_spec]
    rw [e1]
    simp [Complex.conj_ofReal]
  · intro y
    show 0 ≤ (inner ℂ (y : F) (invShiftOperator R hinj γ y) : ℂ).re
    rw [hT, inner_sub_right, inner_smul_right]
    have h := hposR (preim R y)
    rw [preim_spec] at h
    have e : (inner ℂ (y : F) (preim R y) : ℂ).re = (inner ℂ (R (preim R y)) (preim R y) : ℂ).re := by
      rw [preim_spec]
    have e2 : (inner ℂ (y : F) (y : F) : ℂ) = ((‖(y : F)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [Complex.sub_re, e, e2, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [preim_spec] at e ⊢
    linarith
  · intro w u hw
    exact p2m_2886b99c_adj R hinj γ hR w u hw
