-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:24.524082+00:00
-- url     : https://prove2.me/submissions/0cc67271-d22c-45b9-ba65-5f1e0bcf5692

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_coeff_lin
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {S : Type*} [CommRing S] (c : S) (m k : ℕ) :
    ((1 + Polynomial.X) ^ m * Polynomial.C c).coeff k = (m.choose k : S) * c := by
  simpa using ld_coeff_lin (1 : S) 1 c m k
end Formalism.CohomologicalDescent.LD
