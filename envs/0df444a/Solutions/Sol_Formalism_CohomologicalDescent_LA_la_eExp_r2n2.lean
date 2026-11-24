-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_eExp_r2n2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:11.137631+00:00
-- url     : https://prove2.me/submissions/ad8aa4f7-1dbd-49c5-a258-8e1f45ae84f2

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_exact_exponent_rank_two

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
theorem _root_.solution (ν : Fin 2 → ℕ) (l : ℕ) :
    Formalism.RankGapBounds.JumpSetsAlt.eExp (lamU 2 2 ν) l = Formalism.RankGapBounds.JumpSetsAlt.maxVal l (ν 0 - ν 1) := by
  rw [exact_exponent_rank_two 2 ν l]
  have h0 : rowNu (r := 2) ν 0 = ν 0 := dif_pos (by decide)
  have h1 : rowNu (r := 2) ν 1 = ν 1 := dif_pos (by decide)
  rw [h0, h1]
end Formalism.CohomologicalDescent.LA
