-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lemmaD_rank2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:02.877816+00:00
-- url     : https://prove2.me/submissions/2490ad7d-e17f-4733-bb3e-0d7ca85d3135

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_rank2_core
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_blockWt2
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
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : LemmaD_rank2 := by
  intro l w y hl hy eL _ i μ hd
  have hd' : μ 0 + i = w := by simpa [IsDepth] using hd
  rw [ld_blockWt2]
  exact ld_rank2_core l w y hl hy eL i μ hd'
end Formalism.CohomologicalDescent.LD
