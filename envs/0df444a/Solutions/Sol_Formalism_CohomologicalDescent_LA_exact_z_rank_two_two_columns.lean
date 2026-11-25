-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.exact_z_rank_two_two_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:15:22.186799+00:00
-- url     : https://prove2.me/submissions/7b508075-7b14-43c9-80af-dab2c6d62c04

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_eExp_r2n2
import Theorems.Thm_Formalism_CohomologicalDescent_LA_sharp_rank_two_two_columns

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
theorem _root_.solution : ExZR2N2 := by
  unfold ExZR2N2
  intro hn ν hν l hl
  rw [la_eExp_r2n2]
  unfold exZ
  have hset : {e : ℕ | InclZ 2 2 hn ν l e} = {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e} := by
    ext e
    exact sharp_rank_two_two_columns hn ν hν l e hl
  rw [hset]
  have hmem : Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ∈
      {e : ℕ | Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) ≤ e} :=
    le_refl (Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1))
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ (fun b hb => hb))
end Formalism.CohomologicalDescent.LA
