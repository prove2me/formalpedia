-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.dualZE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:06.713248+00:00
-- url     : https://prove2.me/submissions/bdc05beb-7cdb-44b3-b0b8-2a733ce95651

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
theorem _root_.solution {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) :
    dualZE Xs = ((trBE n).dualSubmodule (Xs.restrictScalars ℤ) : Set (Fin n → E)) := by
  ext l
  simp only [dualZE, Set.mem_ofPred_eq, SetLike.mem_coe,
    LinearMap.BilinForm.mem_dualSubmodule, Submodule.restrictScalars_mem, Submodule.mem_one, trBE_apply,
    Set.mem_range, algebraMap_int_eq, eq_intCast]
end Formalism.L2.Pj.FJ
