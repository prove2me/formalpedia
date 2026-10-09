-- Prove2me | solution 1 for BookProof.ChapterG.expectation_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:17:28.483852+00:00
-- url     : https://prove2.me/submissions/c55a19c6-2ecc-4a1f-8c66-b69be2bcb9a9

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.expectation_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (U : V →L[ℂ] V) (hU : U ∈ unitary (V →L[ℂ] V))
    (A : V →L[ℂ] V) (hA : A * U = U * A) (Ψ : V) :
    ⟪U Ψ, A (U Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ := by

  have hAU : A (U Ψ) = U (A Ψ) := by
    have := congr_arg (fun T : V →L[ℂ] V => T Ψ) hA
    simpa [ContinuousLinearMap.mul_apply] using this
  rw [hAU, ← ContinuousLinearMap.adjoint_inner_left]
  have hUU : (ContinuousLinearMap.adjoint U) * U = 1 := by
    have h := hU.1
    rwa [ContinuousLinearMap.star_eq_adjoint] at h
  calc ⟪(ContinuousLinearMap.adjoint U) (U Ψ), A Ψ⟫_ℂ
      = ⟪((ContinuousLinearMap.adjoint U) * U) Ψ, A Ψ⟫_ℂ := by rw [ContinuousLinearMap.mul_apply]
    _ = ⟪Ψ, A Ψ⟫_ℂ := by rw [hUU]; rfl
