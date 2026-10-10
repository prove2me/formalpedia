-- Prove2me | solution 1 for BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:19:14.944189+00:00
-- url     : https://prove2.me/submissions/fcb5ab6a-0026-4162-9146-6f0795969475

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (B C : D →ₗ[ℂ] F)
    (h : ∀ x y : D, (inner ℂ (B x) (B y) : ℂ) = inner ℂ (C x) (C y)) :
    ∃ U : LinearMap.range B →ₗ[ℂ] F,
      (∀ x : D, U ⟨B x, LinearMap.mem_range_self B x⟩ = C x) ∧
      (∀ z : LinearMap.range B, ‖U z‖ = ‖(z : F)‖) ∧
      LinearMap.range U = LinearMap.range C := by

  have hnorm : ∀ x : D, ‖C x‖ = ‖B x‖ := by
    intro x
    have hx := h x x
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at hx
    have hsq : (‖B x‖ : ℝ) ^ 2 = (‖C x‖ : ℝ) ^ 2 := by exact_mod_cast hx
    nlinarith [norm_nonneg (B x), norm_nonneg (C x)]
  have hker : LinearMap.ker B ≤ LinearMap.ker C := by
    intro x hx
    have hx0 : B x = 0 := hx
    have : ‖C x‖ = 0 := by rw [hnorm x, hx0, norm_zero]
    simpa [LinearMap.mem_ker] using norm_eq_zero.mp this
  set f := (LinearMap.ker B).liftQ C hker with hf
  set U := f.comp (B.quotKerEquivRange.symm : LinearMap.range B →ₗ[ℂ] (D ⧸ LinearMap.ker B))
    with hU
  have hval : ∀ x : D, U ⟨B x, LinearMap.mem_range_self B x⟩ = C x := by
    intro x
    have he : B.quotKerEquivRange (Submodule.Quotient.mk x)
        = ⟨B x, LinearMap.mem_range_self B x⟩ := by
      apply Subtype.ext
      simp [LinearMap.quotKerEquivRange_apply_mk B x]
    have hsymm : B.quotKerEquivRange.symm ⟨B x, LinearMap.mem_range_self B x⟩
        = Submodule.Quotient.mk x := by
      rw [← he, LinearEquiv.symm_apply_apply]
    simp [hU, hsymm, hf, Submodule.liftQ_apply]
  refine ⟨U, hval, ?_, ?_⟩
  · rintro ⟨z, x, rfl⟩
    rw [hval x]
    exact hnorm x
  · ext y
    constructor
    · rintro ⟨⟨z, x, rfl⟩, rfl⟩
      exact ⟨x, (hval x).symm ▸ rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨B x, LinearMap.mem_range_self B x⟩, hval x⟩
