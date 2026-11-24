-- Prove2me | solution 1 for Formalism.L2.Th1.A.Wp.isFlowUW_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:30.163276+00:00
-- url     : https://prove2.me/submissions/0e3941e6-2c53-43a2-9965-6d2f8ff3d0f5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ConstCurveDL
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_apply
import Theorems.Thm_Formalism_L2_Th1_A_Wp_sig_X
import Theorems.Thm_Formalism_L2_Th1_A_Wp_fwAt_sig
import Theorems.Thm_Formalism_L2_Th1_A_Wp_fuAt_sig
import Theorems.Thm_Formalism_L2_Th1_A_Wp_wEq_sig
import Theorems.Thm_Formalism_ELL_wSeriesUnique
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Wp
variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)
namespace Formalism.L2.Th1.A.Wp
theorem _root_.solution (hc : ∀ f : K⟦X⟧, derivative K (f.subst e) = (D W f).subst e) :
    IsFlowUW (curveL W) dL (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have hd := congrArg (derivative K) hw
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul] at hd
  have hDw : D W (wSer W) = fu W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, fw, fu]
    linear_combination hd
  have hDX : D W X = fw W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, PowerSeries.derivative_X, mul_one]
  refine ⟨wEq_sig W he, ?_, ?_⟩
  · have h2 : dL (sig he X) = sig he (fw W) := by
      have h1 := hc X
      rw [PowerSeries.subst_X he, hDX] at h1
      rw [sig_X, sig_apply, dL_toL, h1]
    rw [h2, fwAt_sig]
  · have h2 : dL (sig he (wSer W)) = sig he (fu W) := by
      rw [sig_apply, sig_apply, dL_toL, hc (wSer W), hDw]
    rw [h2, fuAt_sig]
end Formalism.L2.Th1.A.Wp
