-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.nat_le_mul_log_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:23.119917+00:00
-- url     : https://prove2.me/submissions/5ad6a9db-8c37-42ea-8024-7ea5987bc0fa

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_log_le_log_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution (ex c l y : ℕ) (h : ex ≤ c * Nat.log l y) :
    (ex : ℝ) * Real.log l ≤ (c : ℝ) * Real.log y := by
  have h1 : (ex : ℝ) ≤ (c : ℝ) * (Nat.log l y : ℝ) := by exact_mod_cast h
  have h2 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
  calc (ex : ℝ) * Real.log l ≤ (c : ℝ) * (Nat.log l y : ℝ) * Real.log l :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (c : ℝ) * ((Nat.log l y : ℝ) * Real.log l) := by ring
    _ ≤ (c : ℝ) * Real.log y := mul_le_mul_of_nonneg_left (log_le_log_bound l y) (Nat.cast_nonneg c)
end Formalism.CohomologicalDescent.SL2BinomialLattices
