-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.exp_le_of_nonzero_weight_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:11.502222+00:00
-- url     : https://prove2.me/submissions/bf17546a-dea5-49f5-9fdc-70821c7d80d4

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
theorem _root_.solution (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (hl : l.Prime)
    (H : ∀ x ∈ nablaWt r ν μ, x ≠ 0 → ExpLe l r ν μ e) : ExpLe l r ν μ e := by
  intro x hx
  by_cases h0 : x = 0
  · refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [h0, smul_zero]
    exact Submodule.zero_mem _
  · exact H x hx h0 x hx
end Formalism.CohomologicalDescent.LD
