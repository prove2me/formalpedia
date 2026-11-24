-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.choose_split_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:49.763292+00:00
-- url     : https://prove2.me/submissions/d491a0d3-614c-4da0-bc0e-c79ece88f0d4

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_card_posPairs
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_sum_posPairs_split
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_posPairs_filter_lt
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_posPairs_filter_ge
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_posPairs_filter_cross
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
theorem _root_.solution : ChooseSplit := by
  intro N k hk
  have h1 : ((posPairs N).filter (fun p => p.2.val < k)).card = k.choose 2 := by
    rw [posPairs_filter_lt hk, Finset.card_map, card_posPairs]
  have h2 : ((posPairs N).filter (fun p => k ≤ p.1.val)).card = (N - k).choose 2 := by
    rw [posPairs_filter_ge hk, Finset.card_map, card_posPairs]
  have h3 : ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)).card = k * (N - k) := by
    rw [posPairs_filter_cross hk, Finset.card_product, Finset.card_map, Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  refine ⟨?_, h1, h2, h3⟩
  have h4 := sum_posPairs_split (N := N) k (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h4
  rw [card_posPairs, h1, h2, h3] at h4
  exact h4.symm
end Formalism.CohomologicalDescent.SL2BinomialLattices
