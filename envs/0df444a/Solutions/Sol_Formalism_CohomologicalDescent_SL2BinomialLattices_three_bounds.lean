-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.three_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:13.051216+00:00
-- url     : https://prove2.me/submissions/8d3208ec-6692-450f-b24d-c2805a7ab954

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_sum_maxVal_le_card_mul_log
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_choose_split_alt

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
theorem _root_.solution : ThreeBounds := by
  intro l N k h S eta xm lo U hl sh
  obtain ⟨-, c1, c2, c3⟩ := choose_split_alt N k sh.k_le
  have hlt : ∀ p ∈ posPairs N, p.1.val < p.2.val := fun p hp => (Finset.mem_filter.1 hp).2
  have b1 := sum_maxVal_le_card_mul_log U l S hl.pos ((posPairs N).filter (fun p => p.2.val < k)) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 := hlt p hp.1
    have h1 := sh.cloudIn p.1 (by omega)
    have h2 := sh.cloudIn p.2 hp.2
    omega)
  have b2 := sum_maxVal_le_card_mul_log U l eta hl.pos ((posPairs N).filter (fun p => k ≤ p.1.val)) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    have h0 := hlt p hp.1
    have h1 := sh.restIn p.1 hp.2
    have h2 := sh.restIn p.2 (by omega)
    omega)
  have b3 := sum_maxVal_le_card_mul_log U l h hl.pos
    ((posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val)) (by
    intro p _
    have h1 := sh.inRange p.1
    have h2 := sh.inRange p.2
    omega)
  rw [c1] at b1
  rw [c2] at b2
  rw [c3] at b3
  exact ⟨b1.1, b1.2, b2.1, b2.2, b3.1, Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))⟩
end Formalism.CohomologicalDescent.SL2BinomialLattices
