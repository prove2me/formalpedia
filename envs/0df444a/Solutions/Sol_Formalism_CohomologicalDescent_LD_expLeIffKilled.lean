-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.expLeIffKilled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:26.146859+00:00
-- url     : https://prove2.me/submissions/bb2b0492-a02b-4358-b39d-d4e7e5f17045

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_val_split

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
theorem _root_.solution : ExpLeIffKilled := by
  intro l r ν μ e D hl hD
  obtain ⟨D', hD', hnd⟩ := ld_val_split l hl D hD
  set v := padicValInt l D with hv
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  constructor
  · intro h x hx
    obtain ⟨m, hm, hmx⟩ := h x hx
    refine ⟨m, hm, ?_⟩
    have e1 : m * ((l : ℤ) ^ e * D) = D' * (m * (l : ℤ) ^ (e + v)) := by
      rw [hD', pow_add]
      ring
    rw [e1, mul_smul]
    exact Submodule.smul_mem _ _ hmx
  · intro h x hx
    obtain ⟨m, hm, hmx⟩ := h x hx
    refine ⟨m * D', fun hdvd => ?_, ?_⟩
    · rcases hlp.dvd_or_dvd hdvd with h1 | h1
      · exact hm h1
      · exact hnd h1
    · have e1 : m * D' * (l : ℤ) ^ (e + v) = m * ((l : ℤ) ^ e * D) := by
        rw [hD', pow_add]
        ring
      rw [e1]
      exact hmx
end Formalism.CohomologicalDescent.LD
