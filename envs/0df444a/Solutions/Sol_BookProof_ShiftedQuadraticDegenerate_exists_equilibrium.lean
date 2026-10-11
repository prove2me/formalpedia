-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.exists_equilibrium
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:33:09.233986+00:00
-- url     : https://prove2.me/submissions/ea72b90f-7018-4678-9963-f5e3fd0aeebb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.exists_equilibrium
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_QuadraticRotation_exists_rotConj_eigenvalues
import Theorems.Thm_BookProof_QuadraticRotation_rotConj_eq
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
open BookProof.ShiftedQuadraticDegenerate




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    {w : Fin d → ℝ}
    (hw : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, w i * v i = 0) :
    ∃ a : Fin d → ℝ, ∀ i, ∑ j, A i j * a j = w i := by
  classical
  obtain ⟨O, hO, hAO⟩ := exists_rotConj_eigenvalues hA
  set c := hA.eigenvalues with hc
  have hOOt : O * Oᵀ = 1 := by simpa using mul_eq_one_comm.mp hO
  have hAeq : A = O * Matrix.diagonal c * Oᵀ := by rw [hAO, rotConj_eq]
  have hAO' : A * O = O * Matrix.diagonal c := by
    rw [hAeq, Matrix.mul_assoc, Matrix.mul_assoc, hO, Matrix.mul_one]
  set u : Fin d → ℝ := Oᵀ *ᵥ w with hu
  have hker : ∀ i, c i = 0 → u i = 0 := by
    intro i hci
    have hv : A *ᵥ (O *ᵥ (Pi.single i (1 : ℝ))) = 0 := by
      rw [Matrix.mulVec_mulVec, hAO', ← Matrix.mulVec_mulVec]
      have hz : Matrix.diagonal c *ᵥ (Pi.single i (1 : ℝ)) = 0 := by
        rw [Matrix.mulVec_single]
        funext j
        by_cases h : j = i <;> simp [h, hci]
      rw [hz, Matrix.mulVec_zero]
    have hsum := hw _ (fun j => congrFun hv j)
    rw [hu]
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mulVec_single]
    ring
  set y : Fin d → ℝ := fun i => if c i = 0 then 0 else u i / c i with hy
  refine ⟨O *ᵥ y, fun i => ?_⟩
  have hdy : Matrix.diagonal c *ᵥ y = u := by
    funext j
    rw [Matrix.mulVec_diagonal, hy]
    by_cases h : c j = 0
    · simp [h, hker j h]
    · simp only [h, if_false]
      field_simp
  have hfin : A *ᵥ (O *ᵥ y) = w := by
    rw [Matrix.mulVec_mulVec, hAO', ← Matrix.mulVec_mulVec, hdy, hu,
      Matrix.mulVec_mulVec, hOOt, Matrix.one_mulVec]
  calc ∑ j, A i j * (O *ᵥ y) j = (A *ᵥ (O *ᵥ y)) i := rfl
    _ = w i := by rw [hfin]
