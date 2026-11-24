-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.trBE_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:09.550783+00:00
-- url     : https://prove2.me/submissions/30a0507f-2906-4a51-817c-263ed5bd9660

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
import Theorems.Thm_Formalism_L2_Pj_FJ_trBE_symm
import Theorems.Thm_Formalism_L2_Pj_FJ_trBE_sepLeft

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
theorem _root_.solution (n : ℕ) : (trBE (E := E) n).Nondegenerate :=
  ⟨trBE_sepLeft n, fun x hx => trBE_sepLeft n x fun l => by rw [(trBE_symm n).eq]; exact hx l⟩
end Formalism.L2.Pj.FJ
