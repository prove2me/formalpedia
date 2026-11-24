-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.maxVal_three_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:27.089963+00:00
-- url     : https://prove2.me/submissions/aa2866d2-9931-4a7c-9141-7cd032bc0921

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
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
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : Formalism.RankGapBounds.JumpSetsAlt.maxVal 3 3 = 1 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hi' : i < 4 := Finset.mem_range.mp hi
    interval_cases i
    · simp [show Nat.choose 3 0 = 1 by decide]
    · simp [show Nat.choose 3 1 = 3 by decide, Nat.Prime.factorization_self Nat.prime_three]
    · simp [show Nat.choose 3 2 = 3 by decide, Nat.Prime.factorization_self Nat.prime_three]
    · simp [show Nat.choose 3 3 = 1 by decide]
  · have h1 : (Nat.choose 3 1).factorization 3 = 1 := by
      rw [Nat.choose_one_right]; exact Nat.Prime.factorization_self Nat.prime_three
    calc 1 = (Nat.choose 3 1).factorization 3 := h1.symm
      _ ≤ _ := Finset.le_sup (f := fun i => (Nat.choose 3 i).factorization 3)
          (Finset.mem_range.mpr (by norm_num))
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
