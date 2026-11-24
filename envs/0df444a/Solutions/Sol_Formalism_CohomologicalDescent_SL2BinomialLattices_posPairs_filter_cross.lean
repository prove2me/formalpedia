-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:02:34.268598+00:00
-- url     : https://prove2.me/submissions/4aa97b76-a3c9-4381-8f80-b3b068e1decf

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
theorem _root_.solution {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) =
      ((Finset.univ : Finset (Fin k)).map (embedFinFirst hk)) ×ˢ
        ((Finset.univ : Finset (Fin (N - k))).map (embedFinLast N k)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Finset.mem_product]
  constructor
  · rintro ⟨-, ha, hb⟩
    have hb2 := b.isLt
    refine ⟨⟨⟨a.val, ha⟩, rfl⟩, ⟨⟨b.val - k, by omega⟩, ?_⟩⟩
    apply Fin.ext
    show k + (b.val - k) = b.val
    omega
  · rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩
    have := a'.isLt
    refine ⟨?_, ?_, ?_⟩
    · show a'.val < k + b'.val
      omega
    · exact a'.isLt
    · show k ≤ k + b'.val
      omega
end Formalism.CohomologicalDescent.SL2BinomialLattices
