-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.expLeMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:43:46.34102+00:00
-- url     : https://prove2.me/submissions/054bdd0f-ea5b-45d7-bc0b-220c1e101f9f

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector

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
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : ExpLeMono := by
  intro l r ν μ e e' hee h x hx
  obtain ⟨m, hm, hmx⟩ := h x hx
  refine ⟨m, hm, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hee
  have e1 : m * (l : ℤ) ^ (e + d) = (l : ℤ) ^ d * (m * (l : ℤ) ^ e) := by ring
  rw [e1, mul_smul]
  exact Submodule.smul_mem _ _ hmx
end Formalism.CohomologicalDescent.LD
