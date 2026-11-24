-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_nu_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:49.393493+00:00
-- url     : https://prove2.me/submissions/95118909-8f06-4f51-a581-21f0cf157909

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_le_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun a => ((qn_nu mu a : ℕ) : ℤ)) = fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ) := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
