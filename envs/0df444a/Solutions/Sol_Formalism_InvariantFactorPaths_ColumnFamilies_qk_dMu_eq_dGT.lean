-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_dMu_eq_dGT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:10:22.555426+00:00
-- url     : https://prove2.me/submissions/081ffae3-f1d9-49ab-a237-32fa4d622374

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_tab_count


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT colHeight)
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch (TabP Dom cnt)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu → dMu mu = dGT n mu := by
  intro n _ mu hmu
  unfold dMu
  rw [Nat.card_congr (qk_tabEquiv hmu)]
  exact (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.tab_count n mu hmu).2
end Formalism.InvariantFactorPaths.ColumnFamilies
