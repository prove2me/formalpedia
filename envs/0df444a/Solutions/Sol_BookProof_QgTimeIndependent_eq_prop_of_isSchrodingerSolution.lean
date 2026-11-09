-- Prove2me | solution 1 for BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T20:02:39.432835+00:00
-- url     : https://prove2.me/submissions/7648a045-aed4-4bfa-bfdf-56dec6e93f03

-- Generated from ChapterQgTimeIndependentFlow.lean — solution of BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub_apply
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_stoneU_op
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_deriv
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.QgTimeIndependent




open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint E) {y : ℝ → E}
    (hy : IsSchrodingerSolution T y) (t s : ℝ) : y t = prop T t s (y s) := by

  set f : ℝ → E := fun r : ℝ => T.stoneU (t - r) (y r) with hf
  have hzero : ∀ u : ℝ, HasDerivAt f 0 u := by
    intro u
    have hd := hasDerivAt_stoneU_const_sub_apply T (hy.deriv u) (hy.mem u) (t := t)
    have hop : T.op ⟨T.stoneU (t - u) (y u),
        T.stoneU_mem_domain (t - u) ⟨y u, hy.mem u⟩⟩
        = T.stoneU (t - u) (T.op ⟨y u, hy.mem u⟩) := T.stoneU_op (t - u) ⟨y u, hy.mem u⟩
    have hsum : Complex.I • T.op ⟨T.stoneU (t - u) (y u),
          T.stoneU_mem_domain (t - u) ⟨y u, hy.mem u⟩⟩
        + T.stoneU (t - u) ((-Complex.I) • T.op ⟨y u, hy.mem u⟩) = 0 := by
      rw [hop, ContinuousLinearMap.map_smul]
      module
    rw [← hsum]
    exact hd
  have hdiff : Differentiable ℝ f := fun u => (hzero u).differentiableAt
  have hderiv : ∀ u, deriv f u = 0 := fun u => (hzero u).deriv
  have hconst : f t = f s := is_const_of_deriv_eq_zero hdiff hderiv t s
  have hft : f t = y t := by
    have h0 : f t = T.stoneU (t - t) (y t) := rfl
    rw [h0, sub_self, T.stoneU_zero]
    rfl
  rw [hft] at hconst
  exact hconst
