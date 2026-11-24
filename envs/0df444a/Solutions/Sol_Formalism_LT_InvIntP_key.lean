-- Prove2me | solution 1 for Formalism.LT.InvIntP.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:05:56.704637+00:00
-- url     : https://prove2.me/submissions/ef5422b6-356f-43ca-8181-7207f6665f8e

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_Low_mono
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_add
import Theorems.Thm_Formalism_LT_InvIntP_low_zero
import Theorems.Thm_Formalism_LT_InvIntP_low_one
import Theorems.Thm_Formalism_LT_InvIntP_subst_eq
import Theorems.Thm_Formalism_LT_InvIntP_agree_psubst
import Theorems.Thm_Formalism_LT_InvIntP_low_of_agree
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution [Finite ι] (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    {N : ℕ} {a b : MvPowerSeries ι K}
    (ha0 : MvPowerSeries.constantCoeff a = 0) (hb0 : MvPowerSeries.constantCoeff b = 0)
    (hab : Agree N a b) : Low (N + 1) (f.subst a - f.subst b - (a - b)) := by
  rw [subst_eq f h0 h1 ha0, subst_eq f h0 h1 hb0]
  have e : a + a ^ 2 * (tail2 f).subst a - (b + b ^ 2 * (tail2 f).subst b) - (a - b) =
      (a - b) * (a + b) * (tail2 f).subst a + b ^ 2 * ((tail2 f).subst a - (tail2 f).subst b) := by ring
  rw [e]
  have hd : Low N (a - b) := low_of_agree hab
  have hs : Low 1 (a + b) := low_one (by simp [ha0, hb0])
  have hb2 : Low 2 (b ^ 2) := by
    have := (low_one hb0).mul (low_one hb0)
    rw [pow_two]
    exact this
  refine Low.add ?_ ?_
  · have := (hd.mul hs).mul (low_zero ((tail2 f).subst a))
    simpa using this
  · exact (hb2.mul (low_of_agree (agree_psubst _ ha0 hb0 hab))).mono (by omega)
end Formalism.LT.InvIntP
