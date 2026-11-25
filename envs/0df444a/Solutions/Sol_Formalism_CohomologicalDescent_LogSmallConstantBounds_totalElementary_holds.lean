-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.totalElementary_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:35:48.583076+00:00
-- url     : https://prove2.me/submissions/2b8ebb2b-1727-40b5-a274-7af8cc2c78db

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_sum_J_mul_log_le_totalBound
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_totalBound_mono
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_smallPrimeSumElementary_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_largePrimeSumElementary_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution : TotalElementary := by
  intro rs3 P H G ι _ D I hNW Q hQ
  have hXC : ∀ τ ∈ D.T2, ∀ Q' : Finset ℕ, (∀ l ∈ Q', l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q', (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ 2 * (P.m : ℝ) * P.b * P.L ^ 2 :=
    fun τ hτ Q' hQ' => smallPrimeSumElementary_holds P H G ι D I.thickA τ hτ Q' hQ'
  have hXD : ∀ τ ∈ D.T2, ∀ Q' : Finset ℕ, (∀ l ∈ Q', l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q', min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        18 * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) := by
    intro τ hτ Q' hQ'
    have h := largePrimeSumElementary_holds P H G ι D I.thickA I.cloudA I.shapeT hNW τ hτ Q' hQ'
    exact h.1.trans h.2
  refine (sum_J_mul_log_le_totalBound rs3 H G I _ _ hXC hXD Q hQ).trans (totalBound_mono P _ ?_)
  have hmbL : 0 ≤ (P.m : ℝ) * P.b * P.L ^ 2 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (b_pos' P).le) (sq_nonneg _)
  linarith
end Formalism.CohomologicalDescent.LogSmallConstantBounds
