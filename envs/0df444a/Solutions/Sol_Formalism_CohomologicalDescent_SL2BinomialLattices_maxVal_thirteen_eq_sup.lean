-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.maxVal_thirteen_eq_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:02:32.940264+00:00
-- url     : https://prove2.me/submissions/a9cdfbaa-cbe8-4980-80a7-b1a60b270097

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
theorem _root_.solution (n : ℕ) (hn : n < 169) :
    Formalism.RankGapBounds.JumpSetsAlt.maxVal 13 n =
      (Finset.range (n + 1)).sup fun i => if 13 ≤ i % 13 + (n - i) % 13 then 1 else 0 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply Finset.sup_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hlog : Nat.log 13 n < 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · exact Nat.log_lt_of_lt_pow hpos.ne' (by norm_num; exact hn)
  rw [Nat.factorization_choose (by norm_num : Nat.Prime 13) hi' hlog]
  have h12 : Finset.Ico 1 2 = {1} := by decide
  rw [h12, Finset.filter_singleton]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by simpa using h1) h2
  · exact absurd (by simpa using h2) h1
  · rfl
end Formalism.CohomologicalDescent.SL2BinomialLattices
