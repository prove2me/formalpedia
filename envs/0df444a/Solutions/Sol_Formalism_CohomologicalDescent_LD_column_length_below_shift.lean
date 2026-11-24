-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.column_length_below_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:25.86582+00:00
-- url     : https://prove2.me/submissions/f5231256-c8eb-46e6-9050-f9243033778c

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
theorem _root_.solution (q c : ℕ) (lam2 tau : Fin q → ℕ) (j : ℕ) (hj : j < c) :
    colLen (fun b => lam2 b + c) (fun b => tau b + c) j = 0 := by
  unfold colLen
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro a _ ⟨h1, _⟩
  have h1' : lam2 a + c ≤ j := h1
  omega
end Formalism.CohomologicalDescent.LD
