-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.invShiftOperator_selfAdjointCriterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:44:43.122237+00:00
-- url     : https://prove2.me/submissions/a284d582-efd6-4b78-8bba-7b65ee41fa6b

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterComplexShiftCore

set_option autoImplicit false

open BookProof.QgOuterFockFL BookProof.HashimotoShiftInvert in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (γ : ℝ) (hR : IsSelfAdjoint R) (w u : F)
    (hw : ∀ v : LinearMap.range (R : F →ₗ[ℂ] F),
      (inner ℂ (invShiftOperator R hinj γ v) w : ℂ) = inner ℂ (v : F) u) :
    ∃ h : w ∈ LinearMap.range (R : F →ₗ[ℂ] F), invShiftOperator R hinj γ ⟨w, h⟩ = u := by
  have hsym : ∀ x y : F, inner ℂ (R x) y = inner ℂ x (R y) := by
    intro x y
    have h1 : (ContinuousLinearMap.adjoint R) = R := hR
    rw [← ContinuousLinearMap.adjoint_inner_right, h1]
  -- preimage of R x is x
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
