-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.sp_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:08.192807+00:00
-- url     : https://prove2.me/submissions/7fa9b535-75ff-4881-a6b2-b00e8a217b8f

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_J_mul_transpose_inl
import Theorems.Thm_CompanionTheory_ThKR_Mp_J_mul_transpose_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution (s : Sp l) (i j : l ⊕ l) :
    ∑ a, (s.1 i (.inr a) * s.1 j (.inl a) - s.1 i (.inl a) * s.1 j (.inr a)) = Matrix.J l ℝ i j := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.1 s.2) i) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type] at h
  simp only [J_mul_transpose_inl, J_mul_transpose_inr] at h
  rw [← h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring
end CompanionTheory.ThKR.Mp
