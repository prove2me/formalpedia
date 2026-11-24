-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_TMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:42.595072+00:00
-- url     : https://prove2.me/submissions/5bbf9697-c765-4bca-88f1-160c81516c74

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_prod_Ioc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_TMat_eq


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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (J I : TIdx mu) :
    TMat mu J I = ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext mu J) j) (ql_E lo N (qs_ext mu I) j) := by
  rw [qs_TMat_eq hmu lo (lo + N) h1 h2, qs_TM, ql_prod_Ioc]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
