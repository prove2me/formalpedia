-- Prove2me | solution 1 for Formalism.L2.Th1.A.Wp.isFlow_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:20.688674+00:00
-- url     : https://prove2.me/submissions/69eccf57-b042-476f-b4f2-2f48e42763a5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_apply
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_X
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Wp_isDer_dL__14cb087f2915
import Theorems.Thm_Formalism_L2_Th1_A_Wp_isFlowUW_sig
import Theorems.Thm_Formalism_L2_Th1_A_Wp_inv_mul_sig
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_chartFlowToFlow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Wp
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)
include he
namespace Formalism.L2.Th1.A.Wp
theorem _root_.solution (hc : ∀ f : K⟦X⟧, derivative K (f.subst e) = (D W f).subst e)
    (hne : toL e ≠ 0) :
    IsFlow (curveL W) dL ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))
      ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) := by
  have h := chartFlowToFlow _ (curveL W) dL (sig he X) (sig he (wSer W))
    ((toL e)⁻¹ ^ 3 * sig he (xS W)) isDer_dL' (isFlowUW_sig W he hc) (inv_mul_sig W he hne)
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  have hx : sig he X * ((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) := by
    rw [sig_X, sig_apply]
    linear_combination (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) * h2
  have hy : -((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 3 * toL ((yS W).subst e) := by
    rw [← sig_apply he (yS W), yS, map_neg, mul_neg]
  rwa [hx, hy] at h
end Formalism.L2.Th1.A.Wp
