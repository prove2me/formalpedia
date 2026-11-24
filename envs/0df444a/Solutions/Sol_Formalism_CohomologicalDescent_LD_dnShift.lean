-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dnShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:15.546579+00:00
-- url     : https://prove2.me/submissions/229c059a-0b53-4378-8126-1cabf69c2ef5

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_multiplicity_shift_invariant
import Theorems.Thm_Formalism_CohomologicalDescent_LD_muRange


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
theorem _root_.solution : DnShift := by
  intro p w i q c lam2 hb
  unfold Dn
  have hr : q + (w + c) + i = c + (q + w + i) := by omega
  rw [hr, Finset.prod_range_add]
  have h1 : ∏ k ∈ Finset.range c, (((w + c : ℕ) : ℤ) - ((k : ℤ) - (q : ℤ))) ^
      mu p (w + c) i (fun b => lam2 b + c) ((k : ℤ) - (q : ℤ)) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    have hz : mu p (w + c) i (fun b => lam2 b + c) ((k : ℤ) - (q : ℤ)) = 0 := by
      by_contra hne
      have := (muRange p (w + c) i q c (fun b => lam2 b + c) _
        (fun b => ⟨Nat.le_add_left _ _, Nat.add_le_add_right (hb b) c⟩) hne).1
      omega
    rw [hz, pow_zero]
  rw [h1, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  have e1 : (((c + k : ℕ) : ℤ) - (q : ℤ)) = ((k : ℤ) - (q : ℤ)) + (c : ℤ) := by
    push_cast
    ring
  rw [e1, multiplicity_shift_invariant]
  congr 1
  push_cast
  ring
end Formalism.CohomologicalDescent.LD
