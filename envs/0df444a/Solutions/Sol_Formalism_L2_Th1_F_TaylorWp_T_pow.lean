-- Prove2me | solution 1 for Formalism.L2.Th1.F.TaylorWp.T.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:14.042633+00:00
-- url     : https://prove2.me/submissions/a786a35e-2c8c-4a0d-a06a-f5445a4ca0e9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_mul
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_const
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
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
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries
open Formalism.L2.Th1.F.TaylorWp
namespace Formalism.L2.Th1.F.TaylorWp
namespace T
theorem _root_.solution (hr : TaylorRing) {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (k : ℕ) :
    T (fun z => f z ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using T.const hr 1
  | succ k ih => simpa only [pow_succ] using T.mul hr ih hf
end T
end Formalism.L2.Th1.F.TaylorWp
