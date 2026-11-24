-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.sum_padicVal_shift_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:28.121482+00:00
-- url     : https://prove2.me/submissions/8bd92d87-1804-4320-902d-f268d5adc802

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] (mB : ℤ) (n : ℕ) :
    ∑ ct ∈ Finset.Ioo mB (mB + 1 + (n : ℤ)), vl l (ct - mB) = padicValNat l n.factorial := by
  induction n with
  | zero =>
    have : Finset.Ioo mB (mB + 1 + ((0 : ℕ) : ℤ)) = ∅ := by
      ext x
      simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    rw [this]
    simp
  | succ n ih =>
    have hins : Finset.Ioo mB (mB + 1 + ((n + 1 : ℕ) : ℤ)) =
        insert (mB + 1 + (n : ℤ)) (Finset.Ioo mB (mB + 1 + (n : ℤ))) := by
      ext x
      simp only [Finset.mem_Ioo, Finset.mem_insert]
      omega
    have hnot : (mB + 1 + (n : ℤ)) ∉ Finset.Ioo mB (mB + 1 + (n : ℤ)) := by
      simp
    rw [hins, Finset.sum_insert hnot, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
    congr 1
    unfold vl
    have : mB + 1 + (n : ℤ) - mB = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, padicValInt.of_nat]
end Formalism.CohomologicalDescent.UnitNormBounds
