-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_minorC_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.456473+00:00
-- url     : https://prove2.me/submissions/2bd3f6d2-4c79-40b4-b729-8aa1f2a4f5c2

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
theorem _root_.solution {n h h' : ℕ} (e : h = h') (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h)
    (hJ' : J.card = h') (hI' : I.card = h') : minorC J I hJ hI = minorC J I hJ' hI' := by
  subst e; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
