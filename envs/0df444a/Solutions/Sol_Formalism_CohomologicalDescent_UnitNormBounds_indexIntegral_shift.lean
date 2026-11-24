-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.indexIntegral_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:41.665884+00:00
-- url     : https://prove2.me/submissions/4cdfffde-77da-47c9-88f1-482bbb069b54

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
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
theorem _root_.solution (l : ℕ) (xm xp mB : ℤ) : IlInd l (xm - mB) (xp - mB) 0 = IlInd l xm xp mB := by
  unfold IlInd
  have h : (∃ y : ℤ, xm - mB ≤ y ∧ y ≤ xp - mB ∧ (l : ℤ) ∣ y - 0) ↔
      (∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB) := by
    constructor
    · rintro ⟨y, h1, h2, h3⟩
      exact ⟨y + mB, by omega, by omega, by simpa using h3⟩
    · rintro ⟨y, h1, h2, h3⟩
      exact ⟨y - mB, by omega, by omega, by simpa using h3⟩
  by_cases hc : ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB
  · rw [if_pos hc, if_pos (h.mpr hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (h.mp h'))]
end Formalism.CohomologicalDescent.UnitNormBounds
