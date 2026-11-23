-- Prove2me | solution 1 for Formalism.L2.Th1.F.TaylorWp.T.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:18.966092+00:00
-- url     : https://prove2.me/submissions/ed90a5b9-6b45-4cb7-9050-312cd6e58bf8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp

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
theorem _root_.solution (hr : TaylorRing) (c : ℂ) : T (fun _ => c) (C c) :=
  ⟨analyticAt_const, hr.2.1 c⟩
end T
end Formalism.L2.Th1.F.TaylorWp
