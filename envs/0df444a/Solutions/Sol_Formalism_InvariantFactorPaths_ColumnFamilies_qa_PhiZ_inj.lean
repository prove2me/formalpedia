-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_PhiZ_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:56.144792+00:00
-- url     : https://prove2.me/submissions/f174176c-71c3-40b5-9551-a4146049fcd2

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_Phi_inj

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
theorem _root_.solution (n : ℕ) (u : GLCoord ℤ n) (hu : IsUnit u) : Function.Injective (qa_PhiZ n u) :=
  qa_Phi_inj ℤ n u hu
end Formalism.InvariantFactorPaths.ColumnFamilies
