-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsParam.eval_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:19.906259+00:00
-- url     : https://prove2.me/submissions/8158f74c-4b93-4676-af33-923ef8b0a397

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_ev_C
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_ev_X
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_pow
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_absSum_of_integral
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_sm
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smm
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smp
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_one_sub
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_eval_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_integral_w

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
open Formalism Formalism.ELL
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsParam
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) {t : K} (ht : ‖t‖ < 1) :
    evalPS w t = t ^ 3 + W.a₁ * t * evalPS w t + W.a₂ * t ^ 2 * evalPS w t
        + W.a₃ * evalPS w t ^ 2 + W.a₄ * t * evalPS w t ^ 2 + W.a₆ * evalPS w t ^ 3 ∧
      ‖evalPS w t‖ = ‖t‖ ^ 3 := by
  have hI := integral_w hW hw
  have hwv : Ev w t (evalPS w t) := ⟨absSum_of_integral hI ht, rfl⟩
  have hX := ev_X (K := K) t
  have hR := (((((hX.pow 3).add (((ev_C W.a₁ t).mul hX).mul hwv)).add
    (((ev_C W.a₂ t).mul (hX.pow 2)).mul hwv)).add ((ev_C W.a₃ t).mul (hwv.pow 2))).add
    (((ev_C W.a₄ t).mul hX).mul (hwv.pow 2))).add ((ev_C W.a₆ t).mul (hwv.pow 3))
  have weq := (congrArg (fun f => evalPS f t) hw.2).trans hR.2
  refine ⟨weq, ?_⟩
  set ω := evalPS w t with hω
  have h0 : coeff 0 w = 0 := by simpa using hw.1
  have hωt : ‖ω‖ ≤ ‖t‖ := norm_eval_le hI h0 ht
  have hω1 : ‖ω‖ < 1 := lt_of_le_of_lt hωt ht
  set E := W.a₁ * t + W.a₂ * t ^ 2 + W.a₃ * ω + W.a₄ * (t * ω) + W.a₆ * ω ^ 2 with hE
  have ht2 : ‖t ^ 2‖ < 1 := by rw [sq]; exact smp ht ht
  have hE1 : ‖E‖ < 1 :=
    sm (sm (sm (sm (smm hW.1 ht) (smm hW.2.1 ht2)) (smm hW.2.2.1 hω1))
      (smm hW.2.2.2.1 (smp ht hω1))) (smm hW.2.2.2.2 (by rw [sq]; exact smp hω1 hω1))
  have key : ω * (1 - E) = t ^ 3 := by rw [hE]; linear_combination weq
  have := congrArg norm key
  rw [norm_mul, norm_one_sub hE1, mul_one, norm_pow] at this
  exact this
end Formalism.ELL.FormalGroupPointsParam
