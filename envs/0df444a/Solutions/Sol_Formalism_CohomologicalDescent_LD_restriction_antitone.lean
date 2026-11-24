-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.restriction_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:10.769783+00:00
-- url     : https://prove2.me/submissions/42e94e87-c4cc-4e18-8a13-f1cdb80ce2c1

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (n : ℕ) (lam : ℕ → ℕ) (ha : ∀ a b, a ≤ b → b < n → lam b ≤ lam a) : Antitone (res n lam) :=
  fun a b hab => ha a.val b.val hab b.isLt
end Formalism.CohomologicalDescent.LD
