-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:03.655445+00:00
-- url     : https://prove2.me/submissions/2ad8b8f3-147b-4f38-b81e-d12202eacbb6

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
    (posPairs N).filter (fun p => p.2.val < k) =
      (posPairs k).map ((embedFinFirst hk).prodMap (embedFinFirst hk)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hab, hb⟩
    have hab' : a.val < b.val := hab
    exact ⟨(⟨a.val, by omega⟩, ⟨b.val, hb⟩), hab, rfl⟩
  · rintro ⟨⟨a', b'⟩, hab, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨hab, b'.isLt⟩
end Formalism.CohomologicalDescent.SL2BinomialLattices
