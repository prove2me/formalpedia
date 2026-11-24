-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.wtBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:49.298435+00:00
-- url     : https://prove2.me/submissions/80b8083f-14f1-4294-810a-5baa9d2c6d7f

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dual_weyl_degree_bound
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : WtBound := by
  intro r M ν μ hν hM hne a
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hx0
  have hwt : Finsupp.weight (rowW r r) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
  have h1 : rowDeg d a = μ a := by rw [← ldrow_weight_rowW, hwt]
  rw [← h1]
  exact (dual_weyl_degree_bound ν hν a x hx.1 d hd).trans (hM _)
end Formalism.CohomologicalDescent.LD
