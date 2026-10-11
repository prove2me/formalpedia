-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:33:40.859802+00:00
-- url     : https://prove2.me/submissions/fd533902-cd09-4149-a990-6ad2cee8d5b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_esa_of_kernel_orthogonal
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_exists_equilibrium
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_shiftedHMatOp_symmetric_of_equilibrium
import Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium
import Theorems.Thm_BookProof_ShiftedHermiteCore_polyGaussCoreT_dense
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
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
theorem solution {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (b b' : Fin d → ℝ)
    (hb : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, b i * v i = 0)
    (hb' : ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, b' i * v i = 0) :
    ∃ a k : Vd d,
      Dense ((polyGaussCoreT a k : Submodule ℂ (L2d d)) : Set (L2d d)) ∧
      SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') ∧
      EssentiallySelfAdjointOn (polyGaussCoreT a k) (shiftedHMatOp a k A b b') ∧
      ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
        IsSelfAdjointExtension (shiftedHMatOp a k A b b') T.op ∧ IsStoneFlow T U := by

  obtain ⟨a0, ha0⟩ := exists_equilibrium hA (w := fun i => -2 * b i) (by
    intro v hv
    have := hb v hv
    calc ∑ i, (-2 * b i) * v i = -2 * ∑ i, b i * v i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, mul_zero])
  obtain ⟨k0, hk0⟩ := exists_equilibrium hA (w := fun i => -(b' i) / 2) (by
    intro v hv
    have := hb' v hv
    calc ∑ i, (-(b' i) / 2) * v i = (-(1:ℝ)/2) * ∑ i, b' i * v i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [this, mul_zero])
  refine ⟨(WithLp.toLp 2 a0 : Vd d), (WithLp.toLp 2 k0 : Vd d), polyGaussCoreT_dense _ _,
    shiftedHMatOp_symmetric_of_equilibrium hA b b' _ _ ha0 hk0,
    shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium hA b b' _ _ ha0 hk0, ?_⟩
  exact exists_stone_flow_of_esa _ (polyGaussCoreT_dense _ _)
    (shiftedHMatOp_symmetric_of_equilibrium hA b b' _ _ ha0 hk0)
    (shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium hA b b' _ _ ha0 hk0)
