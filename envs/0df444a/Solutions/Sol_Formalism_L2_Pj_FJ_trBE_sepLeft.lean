-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.trBE_sepLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:41.513281+00:00
-- url     : https://prove2.me/submissions/10c68b99-b499-4948-839f-1182c241fd22

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_trBE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (n : ℕ) : LinearMap.SeparatingLeft (trBE (E := E) n) := by
  intro l hl
  funext i
  refine (traceForm_nondegenerate ℚ E).1 (l i) (fun y => ?_)
  have h := hl (Pi.single i y)
  rw [trBE_apply] at h
  simpa [Pi.single_apply, Algebra.traceForm_apply] using h
end Formalism.L2.Pj.FJ
