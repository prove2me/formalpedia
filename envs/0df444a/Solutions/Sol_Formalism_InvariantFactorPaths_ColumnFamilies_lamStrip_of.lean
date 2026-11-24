-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.lamStrip_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:18.836651+00:00
-- url     : https://prove2.me/submissions/1242c8b4-99b3-47bf-9785-bbe32253c254

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_be_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_torus
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_strVert
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_ps_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_lead

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
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hc : CntLam) : LamStrip := by
  intro n _ b
  refine ⟨ql_be b, ql_ps b, ql_be_inj b, ql_torus b, fun mu _ nu h => (ql_mem_strVert h).2.1, ?_,
    fun mu hmu nu h => ql_lead b hmu h, fun mu hmu => hc n mu b hmu⟩
  intro mu hmu nu h
  ext ⟨K, L⟩ I
  exact ql_ps_equiv b hmu h K L I
end Formalism.InvariantFactorPaths.ColumnFamilies
