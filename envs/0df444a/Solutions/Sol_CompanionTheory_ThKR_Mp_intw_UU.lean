-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.intw_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:51.452213+00:00
-- url     : https://prove2.me/submissions/1b7be1e4-43bf-4b6d-8d5c-3235b7dd9784

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_inner_sym
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_fou
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_intw_ph


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
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (p q : Eu l) :
    Intw (UU S t) p q (p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q) q := by
  have h := (intw_fou _ _).mul ((intw_ph (inner_sym hS t) _ _).mul (intw_fouInv p q))
  rw [show p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q =
    -(-p + (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) q) by
      rw [ContinuousLinearMap.neg_apply, neg_add, neg_neg, neg_neg]]
  exact h
end CompanionTheory.ThKR.Mp
