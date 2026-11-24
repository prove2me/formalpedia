-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.log_le_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:02:30.590465+00:00
-- url     : https://prove2.me/submissions/0f7d6108-e6c6-4f23-99a0-49e2c4f8ddb1

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
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
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution : LgLog := by
  intro l y
  by_cases h0 : Nat.log l y = 0
  · rw [h0]
    simpa using Real.log_natCast_nonneg y
  · obtain ⟨hl, hy⟩ : 1 < l ∧ l ≤ y := by
      by_contra hcon
      apply h0
      rw [Nat.log_eq_zero_iff]
      omega
    have h1 : l ^ Nat.log l y ≤ y := Nat.pow_log_le_self l (by omega)
    have h2 : ((l : ℝ)) ^ Nat.log l y ≤ (y : ℝ) := by exact_mod_cast h1
    have h3 : (0 : ℝ) < (l : ℝ) ^ Nat.log l y := by positivity
    have h4 := Real.log_le_log h3 h2
    rwa [Real.log_pow] at h4
end Formalism.CohomologicalDescent.SL2BinomialLattices
