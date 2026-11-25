-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.exact_z_rank_two_one_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:57.292648+00:00
-- url     : https://prove2.me/submissions/fce19f5f-e6e2-4349-8a96-ea297ea9762e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_eExp_r2n1
import Theorems.Thm_Formalism_CohomologicalDescent_LA_sharp_rank_two_one_column

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
theorem _root_.solution : ExZR2N1 := by
  unfold ExZR2N1
  intro hn ν l hl
  rw [la_eExp_r2n1]
  unfold exZ
  have hset : {e : ℕ | InclZ 2 1 hn ν l e} = {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e} := by
    ext e
    exact sharp_rank_two_one_column hn ν l e hl
  rw [hset]
  have hmem : Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ∈ {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0) ≤ e} :=
    le_refl (Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0))
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ (fun b hb => hb))
end Formalism.CohomologicalDescent.LA
