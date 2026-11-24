-- Prove2me | solution 1 for Formalism.L2.Th1.H.CmData.isSelfDual_matH_blk4_pow4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:45.73908+00:00
-- url     : https://prove2.me/submissions/86ef4d00-10dd-42f1-9f5c-aaabdd6ec262

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactAltForm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_StdDataCmProof
import Theorems.Thm_Formalism_L2_Th1_H_CmData_slice_embA
import Theorems.Thm_Formalism_L2_Th1_H_CmData_embA_mem
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_H_matrixForm_fourfoldBlock


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H Formalism.L2.Th1.H.CmData
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmPair cmTheta)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.L2.Th1.H.CmData
theorem _root_.solution (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (hsd : IsSelfDual (matH h) Λ) :
    IsSelfDual (matH (blk4 h)) (pow4 Λ) := by
  ext x
  constructor
  · intro hx a
    rw [← hsd]
    intro y hy
    obtain ⟨m, hm⟩ := hx (embA a y) (embA_mem Λ a hy)
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [altE, matrixForm_fourfoldBlock, slice_embA]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh; exact absurd (Finset.mem_univ a) hh
  · intro hx y hy
    have : ∀ a, ∃ m : ℤ, altE (matH h) (slice a x) (slice a y) = (m : ℝ) := fun a => by
      have h1 : slice a x ∈ dualLat (matH h) Λ := by rw [hsd]; exact hx a
      exact h1 _ (hy a)
    choose m hm using this
    refine ⟨∑ a, m a, ?_⟩
    simp only [altE] at hm
    simp only [altE, matrixForm_fourfoldBlock, Complex.im_sum, hm]
    push_cast
    rfl
end Formalism.L2.Th1.H.CmData
