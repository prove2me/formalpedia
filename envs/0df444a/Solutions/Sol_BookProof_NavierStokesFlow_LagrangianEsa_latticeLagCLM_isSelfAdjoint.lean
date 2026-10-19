-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:31:53.10236+00:00
-- url     : https://prove2.me/submissions/51939160-ea94-4a02-8546-134f3f9fdfc0

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSelfAdjoint
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
theorem h43_mom2_symm : ((BookProof.ChapterContinuityUnitaryInfinite.momentum * BookProof.ChapterContinuityUnitaryInfinite.momentum : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.mul_apply]
  rw [← ContinuousLinearMap.coe_coe BookProof.ChapterContinuityUnitaryInfinite.momentum, BookProof.ChapterContinuityUnitaryInfinite.momentum_isSymmetric, BookProof.ChapterContinuityUnitaryInfinite.momentum_isSymmetric]

theorem h43_lagCLM_symm (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    ((latticeLagCLM v w fr nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric := by
  intro x y
  have hm := h43_mom2_symm x y
  have hv : ∀ u : LinfZ, ∀ x y : L2Z, inner ℂ (BookProof.ChapterContinuityUnitaryInfinite.velocityOp u x) y = inner ℂ x (BookProof.ChapterContinuityUnitaryInfinite.velocityOp u y) :=
    fun u x y => BookProof.ChapterContinuityUnitaryInfinite.velocityOp_isSymmetric u x y
  simp only [ContinuousLinearMap.coe_coe] at hm
  simp only [latticeLagCLM, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, sum_inner, inner_sum, hm, hv, Complex.conj_ofReal]

theorem h43_lagCLM_sa (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    IsSelfAdjoint (latticeLagCLM v w fr nu) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (h43_lagCLM_symm v w fr nu)

theorem solution (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    IsSelfAdjoint (latticeLagCLM v w fr nu) := by
  exact h43_lagCLM_sa v w fr nu

