-- Prove2me | solution 1 for BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T00:25:12.823339+00:00
-- url     : https://prove2.me/submissions/6494426b-04e6-45ed-b5d1-f8384169762e

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {I : Type*} (D : Submodule ℂ F) (H : D →ₗ[ℂ] D)
    (e : I → D) (lam : I → ℝ) (heig : ∀ i, H (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn D H := by

  have key : ∀ (c : ℂ), (∀ i, ((lam i : ℂ)) ≠ c) → ∀ w : F,
      (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (c • w)) → w = 0 := by
    intro c hc w hw
    refine htotal w fun i => ?_
    have h := hw (e i)
    rw [heig i] at h
    simp only [Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
    have hzero : (((lam i : ℂ)) - c) * (inner ℂ ((e i : F)) w : ℂ) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (hc i))
  refine ⟨key Complex.I ?_, fun w hw => key (-Complex.I) ?_ w (by simpa using hw)⟩
  · intro i hi
    have himag := congrArg Complex.im hi
    simp at himag
  · intro i hi
    have himag := congrArg Complex.im hi
    simp at himag
