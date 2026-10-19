-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:27:15.877087+00:00
-- url     : https://prove2.me/submissions/e51e0f6a-6b68-4d26-be57-e976e87e4c47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_selfAdjoint_commutant_scalar
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) {S : V →L[ℂ] V} (hcomm : M.Commutes S) :
    ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by

  -- The adjoint of `S` also commutes with the system, by normality.
  have hstar : M.Commutes (star S) := by
    intro m hm
    have hm' : ContinuousLinearMap.adjoint m ∈ M.ops := hM m hm
    have h := hcomm _ hm'
    have := congrArg (fun T : V →L[ℂ] V => star T) h
    simpa [star_mul, ContinuousLinearMap.star_eq_adjoint, eq_comm] using this
  set A : V →L[ℂ] V := (2 : ℂ)⁻¹ • (S + star S) with hA
  set B : V →L[ℂ] V := ((2 : ℂ) * Complex.I)⁻¹ • (S - star S) with hB
  have hAsa : IsSelfAdjoint A := by
    have : star A = A := by
      rw [hA, star_smul, star_add, star_star]
      simp [add_comm]
    exact this
  have hBsa : IsSelfAdjoint B := by
    have : star B = B := by
      rw [hB, star_smul, star_sub, star_star]
      rw [show star ((2 : ℂ) * Complex.I)⁻¹ = -((2 : ℂ) * Complex.I)⁻¹ by
        simp]
      module
    exact this
  have hAcomm : M.Commutes A := by
    intro m hm
    have h1 := hcomm m hm
    have h2 := hstar m hm
    rw [hA]
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, h1, h2]
  have hBcomm : M.Commutes B := by
    intro m hm
    have h1 := hcomm m hm
    have h2 := hstar m hm
    rw [hB]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, h1, h2]
  obtain ⟨a, ha⟩ := selfAdjoint_commutant_scalar M hirr hAsa hAcomm
  obtain ⟨b, hb⟩ := selfAdjoint_commutant_scalar M hirr hBsa hBcomm
  refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩
  have hS : S = A + Complex.I • B := by
    rw [hA, hB]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rw [smul_smul]
    rw [show Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = (2 : ℂ)⁻¹ by
      field_simp]
    module
  rw [hS, ha, hb, smul_smul, add_smul, mul_smul]
