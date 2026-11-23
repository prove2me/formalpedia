-- Prove2me | solution 1 for Formalism.L2.Th1.F.Taylor.coeff_taylor0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:00.74479+00:00
-- url     : https://prove2.me/submissions/29403e4f-a55f-4411-8022-9fc55b53c9e4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor

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
open Formalism.L2.Th1.F.Taylor
open PowerSeries
namespace Formalism.L2.Th1.F.Taylor
theorem _root_.solution (f : ℂ → ℂ) (n : ℕ) :
    coeff n (taylor0 f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  simp [taylor0]
end Formalism.L2.Th1.F.Taylor
