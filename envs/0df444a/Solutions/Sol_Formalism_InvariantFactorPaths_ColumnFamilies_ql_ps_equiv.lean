-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_ps_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:35:27.366128+00:00
-- url     : https://prove2.me/submissions/b77d8e75-132c-4451-aef0-d01d187a7a4d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_strVert
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_core
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_range

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
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) * ((ql_ps b mu nu y I : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_ps b mu nu (K, L) I' : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
  obtain ⟨hb, hnu, -⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  exact ql_core b hmu hnu le_rfl (by rw [hN]; exact (hb 0).1) (hb _).1 hN.ge K L I
end Formalism.InvariantFactorPaths.ColumnFamilies
