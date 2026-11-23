-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_lt_colH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:32.398803+00:00
-- url     : https://prove2.me/submissions/d111a9fe-1518-4110-914a-ead97533a5a9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_lower_iff

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
theorem _root_.solution {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (p : Fin n) :
    p.val < colH mu c ↔ c ≤ mu p :=
  (qa_lower_iff (fun m => c ≤ mu m) (fun _ _ hqq hq => hq.trans (hmu hqq)) p).symm
end Formalism.InvariantFactorPaths.ColumnFamilies
