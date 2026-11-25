-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.size_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:17.792486+00:00
-- url     : https://prove2.me/submissions/346f3097-36bf-47ee-a8c0-23c01c40dc77

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_nat_le_mul_log_real
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_raising_split_three
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_three_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_real_log_mono_of_le
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_choose_two_le_sq

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
theorem _root_.solution : SizeLarge := by
  intro l N k h S eta ex m t xm lo U hl sh hex heta hmt
  obtain ⟨b1, -, -, b2, b3, -⟩ := three_bounds l N k h S eta xm lo U hl sh
  have h0 := raising_split_three N k l U
  rw [b2 heta] at h0
  constructor
  · have e1 := nat_le_mul_log_real _ _ _ _ b1
    have e3 := nat_le_mul_log_real _ _ _ _ b3
    have hex' : (ex : ℝ) ≤ (eCl U k l : ℝ) + (eCross U k l : ℝ) := by
      have : ex ≤ eCl U k l + eCross U k l := by omega
      exact_mod_cast this
    have hl0 : 0 ≤ Real.log l := Real.log_natCast_nonneg l
    push_cast at e3
    nlinarith [mul_le_mul_of_nonneg_right hex' hl0]
  · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
    have l1 : 0 ≤ Real.log (3 * (h : ℝ)) := by
      have := Real.log_natCast_nonneg (3 * h)
      push_cast at this
      exact this
    have l2 : 0 ≤ Real.log ((S : ℝ) + k) := by
      have := Real.log_natCast_nonneg (S + k)
      push_cast at this
      exact this
    have a1 : Real.log h ≤ Real.log (3 * (h : ℝ)) := real_log_mono_of_le h _ (by linarith) l1
    have a2 : Real.log S ≤ Real.log ((S : ℝ) + k) := real_log_mono_of_le S _ (by linarith) l2
    have a3 : ((N - k : ℕ) : ℝ) ≤ (m : ℝ) + t := by exact_mod_cast hmt
    have a4 : (k : ℝ) * ((N - k : ℕ) : ℝ) ≤ (k : ℝ) * ((m : ℝ) + t) :=
      mul_le_mul_of_nonneg_left a3 hk0
    have a5 := mul_le_mul a4 a1 (Real.log_natCast_nonneg h) (by positivity)
    have a6 := mul_le_mul (choose_two_le_sq k) a2 (Real.log_natCast_nonneg S) (by positivity)
    linarith
end Formalism.CohomologicalDescent.SL2BinomialLattices
