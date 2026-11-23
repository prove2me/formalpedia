-- Prove2me | solution 1 for Formalism.L2.Th1.F.TaylorWp.T.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:40.740519+00:00
-- url     : https://prove2.me/submissions/97441d38-14c7-472b-889e-a5fce20b5502

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
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
theorem _root_.solution (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z * g z) (F * G) :=
  ⟨hf.1.mul hg.1, by rw [(hr.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩
end T
end Formalism.L2.Th1.F.TaylorWp
