-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.branching_count_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:31.965385+00:00
-- url     : https://prove2.me/submissions/76f91f49-4733-4924-8c13-619c37f0928e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntBranch
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_dMu_eq_dGT
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_gtBox_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_gtBox


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT gtBox)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : CntBranch := by
  intro m _ lam hlam Sg hSg
  have hS : Sg = gtBox lam := by
    ext nu
    rw [hSg, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox]
    constructor
    · intro h i
      exact ⟨(h.2 i).2, (h.2 i).1⟩
    · intro h
      refine ⟨Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox lam nu).2 h), fun i => ⟨(h i).2, (h i).1⟩⟩
  rw [qk_dMu_eq_dGT (m + 1) lam hlam, hS]
  show ∑ κ ∈ gtBox lam, dGT m κ = _
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT m nu (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam hnu)]
end Formalism.InvariantFactorPaths.ColumnFamilies
