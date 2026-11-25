-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lattice_z_rank_two_two_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:11.246895+00:00
-- url     : https://prove2.me/submissions/1fe48cb3-44b9-4e92-bb87-5cd397f0f56c

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
theorem _root_.solution : LemmaAZ_r2n2 := by
  unfold LemmaAZ_r2n2
  intro hn ν hν l hl
  rw [la_eExp_r2n2]
  exact (sharp_rank_two_two_columns hn ν hν l _ hl).mpr le_rfl
end Formalism.CohomologicalDescent.LA
