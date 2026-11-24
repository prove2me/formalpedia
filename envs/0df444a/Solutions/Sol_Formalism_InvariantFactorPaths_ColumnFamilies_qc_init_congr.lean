-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_init_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.342817+00:00
-- url     : https://prove2.me/submissions/5a7a0af6-21f4-454f-ba0e-b1caec18f7e0

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
theorem _root_.solution {n h h' : ℕ} (e : h = h') (hn : h ≤ n) (hn' : h' ≤ n) :
    (univ : Finset (Fin h)).map (Fin.castLEEmb hn) = (univ : Finset (Fin h')).map (Fin.castLEEmb hn') := by
  subst e; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
