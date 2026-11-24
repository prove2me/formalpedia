-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:00:51.002157+00:00
-- url     : https://prove2.me/submissions/3d4bd321-609b-4edd-9b3b-79a03af11605

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
    (posPairs N).filter (fun p => k ≤ p.1.val) =
      (posPairs (N - k)).map ((embedFinLast N k).prodMap (embedFinLast N k)) := by
  ext ⟨a, b⟩
  simp only [posPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨hab, ha⟩
    have hab' : a.val < b.val := hab
    have ha2 := a.isLt
    have hb2 := b.isLt
    refine ⟨(⟨a.val - k, by omega⟩, ⟨b.val - k, by omega⟩), ?_, ?_⟩
    · show a.val - k < b.val - k
      omega
    · apply Prod.ext
      · apply Fin.ext
        show k + (a.val - k) = a.val
        omega
      · apply Fin.ext
        show k + (b.val - k) = b.val
        omega
  · rintro ⟨⟨a', b'⟩, hab, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    have hab' : a'.val < b'.val := hab
    refine ⟨?_, ?_⟩
    · show k + a'.val < k + b'.val
      omega
    · show k ≤ k + a'.val
      omega
end Formalism.CohomologicalDescent.SL2BinomialLattices
