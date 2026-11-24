-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.inner_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:06.706349+00:00
-- url     : https://prove2.me/submissions/5a844665-f834-4e77-9d87-c3a99ac6e9cd

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_tc_apply

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
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (x y : Eu l) :
    ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) y⟫ =
      ⟪y, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ := by
  have hS' : ∀ a b, S a b = S b a := fun a b => by
    simpa using (congrFun (congrFun hS.eq b) a)
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right, real_inner_smul_right]
  congr 2
  simp only [PiLp.inner_apply, tc_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hS']
  ring
end CompanionTheory.ThKR.Mp
