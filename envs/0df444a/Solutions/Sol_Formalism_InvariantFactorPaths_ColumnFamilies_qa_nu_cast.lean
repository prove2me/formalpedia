-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_nu_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:19.974443+00:00
-- url     : https://prove2.me/submissions/f5e3c11e-3ead-40ba-af56-e4dcca58dcfe

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_last_le

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (p : Fin n) :
    (qa_nu mu p : ℤ) = mu p - mu (lastIdx n) := by
  unfold qa_nu
  have : mu (lastIdx n) ≤ mu p := hmu (qa_last_le p)
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
