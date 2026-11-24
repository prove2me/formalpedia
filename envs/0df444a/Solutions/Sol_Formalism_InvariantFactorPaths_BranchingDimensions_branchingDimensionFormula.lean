-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.branchingDimensionFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:16.61301+00:00
-- url     : https://prove2.me/submissions/5b8ff053-417e-422e-8883-23b5ba8f43da

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_extW_val
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_weylDim_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_W_id_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_W_id_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_core
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_finsum_prop_eq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_interl_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_W_extW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution : BranchDim := by
  intro n mu hmu
  have h : ∀ i : Fin n, mu i.succ ≤ mu i.castSucc := by
    intro i
    have := hmu i.val (by have := i.isLt; omega)
    have e1 : extW mu i.val = mu i.castSucc := extW_val mu i.castSucc
    have e2 : extW mu (i.val + 1) = mu i.succ := extW_val mu i.succ
    rwa [e1, e2] at this
  rw [finsum_prop_eq_sum _ _ _ (fun la => interl_iff la mu)]
  simp_rw [weylDim_eq, W_extW]
  rw [← Finset.sum_div, ← core mu h, W_id_succ]
  have h0 := W_id_ne_zero n
  have h1 : (∏ j : Fin n, ((j : ℝ) + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => by positivity
  field_simp
end Formalism.InvariantFactorPaths.BranchingDimensions
