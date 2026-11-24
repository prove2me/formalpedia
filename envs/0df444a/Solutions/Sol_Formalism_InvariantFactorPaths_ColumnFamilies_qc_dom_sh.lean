-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_dom_sh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.447891+00:00
-- url     : https://prove2.me/submissions/c7b4b651-1588-42cb-94bb-3d03ba3d7f1e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (h : Dominant mu) (ε : ℤ) : Dominant (qc_sh mu ε) :=
  fun _ _ hab => add_le_add_left (h hab) ε
end Formalism.InvariantFactorPaths.ColumnFamilies
