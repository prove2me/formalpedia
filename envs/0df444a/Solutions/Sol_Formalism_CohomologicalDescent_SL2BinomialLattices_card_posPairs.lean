-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.card_posPairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:03.293733+00:00
-- url     : https://prove2.me/submissions/beae7ed0-8764-4758-a3a4-d9629c41b7b5

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
theorem _root_.solution (N : ℕ) : (posPairs N).card = N.choose 2 := by
  have h1 : (posPairs N).card = ∑ b : Fin N, (Finset.Iio b).card := by
    unfold posPairs
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.card_filter]
    congr 1
    ext a
    simp
  rw [h1]
  simp only [Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id, Nat.choose_two_right]
end Formalism.CohomologicalDescent.SL2BinomialLattices
