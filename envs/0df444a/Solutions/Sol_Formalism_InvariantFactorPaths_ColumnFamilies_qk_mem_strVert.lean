-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_mem_strVert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.996286+00:00
-- url     : https://prove2.me/submissions/3d8d9fda-8938-4cef-b925-08393842fa9a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} : nu ∈ strVert mu b ↔
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  unfold strVert
  simp only [mem_filter, Fintype.mem_piFinset, mem_Icc]
end Formalism.InvariantFactorPaths.ColumnFamilies
