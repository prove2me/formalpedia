-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:09:24.499339+00:00
-- url     : https://prove2.me/submissions/d60cb999-bf0a-4aa7-8547-3fb155f88b8f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_P2M_Formalism_L2_Th1_A_WpSh_rescale_C__e9f3bb5ac876
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_derivative_rescale_neg_one
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    Cleared g2 g3 (rescale (-1 : K) r) := by
  unfold Cleared at h ⊢
  have e := congrArg (rescale (-1 : K)) h
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one, rescale_X,
    rescale_C'] at e
  rw [derivative_rescale_neg_one]
  linear_combination e
end Formalism.L2.Th1.A.WpSh
