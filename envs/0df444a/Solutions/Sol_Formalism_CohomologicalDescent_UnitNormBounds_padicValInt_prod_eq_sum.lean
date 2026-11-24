-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.padicValInt_prod_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:26.771524+00:00
-- url     : https://prove2.me/submissions/4708415d-eae9-42f6-adf5-ddf6e41dc278

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (l : ℕ) [Fact l.Prime] (s : Finset ℕ) (g : ℕ → ℤ) (hg : ∀ x ∈ s, g x ≠ 0) :
    padicValInt l (∏ x ∈ s, g x) = ∑ x ∈ s, padicValInt l (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValInt.mul (hg a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun x hx => hg x (Finset.mem_insert_of_mem hx)),
      ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]
end Formalism.CohomologicalDescent.UnitNormBounds
