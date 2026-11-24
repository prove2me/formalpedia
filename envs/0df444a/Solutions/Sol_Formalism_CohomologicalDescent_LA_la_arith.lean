-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:52:28.106948+00:00
-- url     : https://prove2.me/submissions/87b2adab-5647-43aa-81c2-c976ba6e1e84

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (l d : ℕ) (hl : l.Prime) :
    ∃ m : ℕ, ¬ l ∣ m ∧ ∀ i ≤ d, d.choose i ∣ m * l ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l d := by
  refine ⟨∏ i ∈ Finset.range (d + 1), d.choose i / l ^ ((d.choose i).factorization l), ?_, ?_⟩
  · rw [Prime.dvd_finset_prod_iff hl.prime]
    push_neg
    intro i hi
    exact Nat.not_dvd_ordCompl hl (Nat.choose_pos (by rw [Finset.mem_range] at hi; omega)).ne'
  · intro i hi
    have hmem : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    calc d.choose i = l ^ ((d.choose i).factorization l) *
          (d.choose i / l ^ ((d.choose i).factorization l)) :=
          (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
      _ ∣ l ^ Formalism.RankGapBounds.JumpSetsAlt.maxVal l d *
          ∏ j ∈ Finset.range (d + 1), d.choose j / l ^ ((d.choose j).factorization l) :=
        mul_dvd_mul (Nat.pow_dvd_pow l (Finset.le_sup (f := fun j => (d.choose j).factorization l) hmem))
          (Finset.dvd_prod_of_mem _ hmem)
      _ = _ := mul_comm _ _
end Formalism.CohomologicalDescent.LA
