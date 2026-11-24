-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_val_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:33.765551+00:00
-- url     : https://prove2.me/submissions/de69472e-96e3-4098-b59d-e706e7b853ea

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) (D : ℤ) (hD : D ≠ 0) :
    ∃ D' : ℤ, D = (l : ℤ) ^ padicValInt l D * D' ∧ ¬ (l : ℤ) ∣ D' := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨D', hD'⟩ := (padicValInt_dvd_iff (p := l) (padicValInt l D) D).mpr (Or.inr le_rfl)
  refine ⟨D', hD', fun hdiv => ?_⟩
  obtain ⟨E, hE⟩ := hdiv
  have h2 : (l : ℤ) ^ (padicValInt l D + 1) ∣ D := ⟨E, by rw [pow_succ, mul_assoc, ← hE]; exact hD'⟩
  rcases (padicValInt_dvd_iff (p := l) (padicValInt l D + 1) D).mp h2 with h3 | h3
  · exact hD h3
  · omega
end Formalism.CohomologicalDescent.LD
