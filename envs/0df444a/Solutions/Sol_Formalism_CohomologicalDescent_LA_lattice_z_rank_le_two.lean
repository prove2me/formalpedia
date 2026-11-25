-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lattice_z_rank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:07.357259+00:00
-- url     : https://prove2.me/submissions/4b7f509d-caff-4039-89e1-338e11c686ac

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_lattice_z_zero_columns
import Theorems.Thm_Formalism_CohomologicalDescent_LA_lattice_z_rank_two_one_column
import Theorems.Thm_Formalism_CohomologicalDescent_LA_lattice_z_rank_one
import Theorems.Thm_Formalism_CohomologicalDescent_LA_lattice_z_rank_two_two_columns

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
theorem _root_.solution : LatticeInclusionRankLeTwo := by
  unfold LatticeInclusionRankLeTwo
  intro r n hn hr ν hν l hl
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · exact lattice_z_zero_columns r hn ν l hl
  · obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
    · exact lattice_z_rank_one 1 hn ν hν l hl
    · exact lattice_z_rank_two_one_column hn ν l hl
  · obtain rfl : r = 2 := by omega
    exact lattice_z_rank_two_two_columns hn ν hν l hl
end Formalism.CohomologicalDescent.LA
