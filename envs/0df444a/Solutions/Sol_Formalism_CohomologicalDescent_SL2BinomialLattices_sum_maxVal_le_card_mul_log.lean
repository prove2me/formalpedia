-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.sum_maxVal_le_card_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:25.274184+00:00
-- url     : https://prove2.me/submissions/2012b40f-4b4a-4dc7-bb3c-dc2f4e4352dd

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_maxVal_le_log_alt
import Theorems.Thm_Formalism_CohomologicalDescent_max_val_eq_zero_of_lt


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
theorem _root_.solution {N : ℕ} (U : Fin N → ℤ) (l M : ℕ) (hl : 0 < l) (s : Finset (Fin N × Fin N))
    (h : ∀ p ∈ s, U p.1 - U p.2 ≤ (M : ℤ)) :
    ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat ≤ s.card * Nat.log l M ∧
      (M ≤ l → ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat = 0) := by
  constructor
  · rw [← smul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    have := h p hp
    exact (maxVal_le_log_alt l _).trans (Nat.log_mono_right (by omega))
  · intro hM
    apply Finset.sum_eq_zero
    intro p hp
    apply Formalism.CohomologicalDescent.max_val_eq_zero_of_lt
    have := h p hp
    omega
end Formalism.CohomologicalDescent.SL2BinomialLattices
