-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_mapCoord_brk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:56:36.60671+00:00
-- url     : https://prove2.me/submissions/dd44ef1a-8909-4083-820f-51775697d591

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_brk_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Phi_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_mapCoord_algebraMap
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_map_tableauBideterminant


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
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (F : Type) [CommRing F] (I : TIdx mu) :
    mapCoord (n := n) F (brk mu I) =
      qa_Phi F n (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) (qa_P F I) := by
  rw [qa_brk_eq, map_mul, qa_mapCoord_algebraMap, qa_Phi_apply, MvPolynomial.map_rename, map_tableauBideterminant]
end Formalism.InvariantFactorPaths.ColumnFamilies
