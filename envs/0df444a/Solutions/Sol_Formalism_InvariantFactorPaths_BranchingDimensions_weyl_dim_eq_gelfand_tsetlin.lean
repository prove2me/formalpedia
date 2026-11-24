-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.weyl_dim_eq_gelfand_tsetlin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:12.413872+00:00
-- url     : https://prove2.me/submissions/76d72cd6-d50b-4c41-af95-adfa831e70af

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_dom_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_interl_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_finsum_prop_eq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_dGT_succ


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
theorem _root_.solution : WeylGT := by
  intro hB n
  induction n with
  | zero =>
    intro μ _
    simp [weylDim, Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT]
  | succ n ih =>
    intro μ hμ
    rw [← hB n μ ((dom_iff μ).mpr hμ), finsum_prop_eq_sum _ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.gtBox μ) _ (fun la => interl_iff la μ),
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.dGT_succ, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun la hla => ih la ?_)
    have hI := (interl_iff la μ).mpr hla
    apply (dom_iff la).mp
    intro m hm
    exact le_trans (hI (m + 1) hm).1 (hI m (by omega)).2
end Formalism.InvariantFactorPaths.BranchingDimensions
