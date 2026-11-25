-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.pieri_of_branching
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:56.653795+00:00
-- url     : https://prove2.me/submissions/491c8338-36f9-4d66-90fa-e167f87e6b97

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_dom_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_hstrip_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_antitone_of_mem_stripsUp
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_finsum_prop_eq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_weyl_dim_eq_gelfand_tsetlin
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_up


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
open WGT
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution : PieriOfBranch := by
  intro hB n μ B hn hdom
  have hW := weyl_dim_eq_gelfand_tsetlin hB
  have hμ := (dom_iff μ).mp hdom
  rw [finsum_prop_eq_sum _ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp μ B) _ (fun ν => hstrip_iff μ ν B),
    Finset.sum_congr rfl (fun ν hν => hW n ν (antitone_of_mem_stripsUp hν)), hW n μ hμ,
    ← Nat.cast_sum, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.up n μ B hμ, Nat.cast_mul]
  have hc : (n + B - 1).choose B = (B + n - 1).choose (n - 1) := by
    rw [show B + n - 1 = n + B - 1 by omega]
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hc]
end Formalism.InvariantFactorPaths.BranchingDimensions
