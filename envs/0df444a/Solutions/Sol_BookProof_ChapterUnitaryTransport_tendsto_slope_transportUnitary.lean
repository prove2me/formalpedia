-- Prove2me | solution 1 for BookProof.ChapterUnitaryTransport.tendsto_slope_transportUnitary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:31:29.73557+00:00
-- url     : https://prove2.me/submissions/7b3b8b8a-00d6-46db-81bd-047f5207b49a

import Mathlib
import Definitions.Def_ChapterUnitaryTransport
-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.tendsto_slope_transportUnitary
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
theorem solution (W : H ≃ₗᵢ[ℂ] K) (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (U : ℝ → H ≃ₗᵢ[ℂ] H)
    (h : ∀ x : D, Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (U t (x : H) - (x : H)))
      (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I • A x)))
    (y : transportDomain W D) :
    Filter.Tendsto (fun t : ℝ => (t⁻¹ : ℝ) • (transportUnitary W (U t) (y : K) - (y : K)))
      (nhdsWithin 0 {0}ᶜ) (nhds (Complex.I • transportOp W D A y)) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨x, hxD, rfl⟩ := Submodule.mem_map.1 hy
  have hx := h ⟨x, hxD⟩
  have hcont := ((W : H →L[ℂ] K).continuous.tendsto (Complex.I • A ⟨x, hxD⟩)).comp hx
  have hsymm : (transportEquiv W D).symm ⟨(W.toLinearEquiv : H →ₗ[ℂ] K) x, hy⟩ = ⟨x, hxD⟩ := by
    apply (transportEquiv W D).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hop : transportOp W D A ⟨(W.toLinearEquiv : H →ₗ[ℂ] K) x, hy⟩ = W (A ⟨x, hxD⟩) := by
    simp only [transportOp, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    erw [hsymm]
    rfl
  rw [hop, ← map_smul]
  refine hcont.congr fun t => ?_
  simp only [Function.comp_apply, transportUnitary, LinearIsometryEquiv.trans_apply,
    ContinuousLinearMap.coe_coe, map_smul, map_sub]
  congr 2
  simp
