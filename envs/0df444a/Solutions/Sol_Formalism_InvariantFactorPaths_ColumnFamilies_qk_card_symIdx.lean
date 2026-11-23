-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_card_symIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:00.172556+00:00
-- url     : https://prove2.me/submissions/fda9c09f-63b3-456f-9983-28872239533d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym

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
theorem _root_.solution (n b : ℕ) : Fintype.card (SymIdx n b) = (n + b - 1).choose b := by
  rw [Fintype.card_congr ((qk_symEquiv n b).trans (Sym.equivNatSumOfFintype (Fin n) b).symm),
    Sym.card_sym_eq_choose, Fintype.card_fin]
end Formalism.InvariantFactorPaths.ColumnFamilies
