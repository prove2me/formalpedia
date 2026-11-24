-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.sum_posPairs_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:27.796797+00:00
-- url     : https://prove2.me/submissions/fe1ab543-11aa-4610-b389-840f6baecb6d

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices

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
theorem _root_.solution {N : ℕ} (k : ℕ) (g : Fin N × Fin N → ℕ) :
    ∑ p ∈ posPairs N, g p = ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), g p +
      ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), g p +
      ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val), g p := by
  have hlt : ∀ p ∈ posPairs N, p.1.val < p.2.val := fun p hp => (Finset.mem_filter.1 hp).2
  have hR : (posPairs N).filter (fun p => ¬ p.2.val < k ∧ k ≤ p.1.val) =
      (posPairs N).filter (fun p => k ≤ p.1.val) :=
    Finset.filter_congr fun p hp => by have := hlt p hp; omega
  have hC : (posPairs N).filter (fun p => ¬ p.2.val < k ∧ ¬ k ≤ p.1.val) =
      (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) :=
    Finset.filter_congr fun p hp => by have := hlt p hp; omega
  rw [← Finset.sum_filter_add_sum_filter_not (posPairs N) (fun p => p.2.val < k),
    ← Finset.sum_filter_add_sum_filter_not ((posPairs N).filter (fun p => ¬ p.2.val < k))
      (fun p => k ≤ p.1.val), Finset.filter_filter, Finset.filter_filter, hR, hC, add_assoc]
end Formalism.CohomologicalDescent.SL2BinomialLattices
