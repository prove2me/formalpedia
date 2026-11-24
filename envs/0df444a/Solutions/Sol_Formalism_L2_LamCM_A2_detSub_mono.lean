-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.detSub_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:13:13.1159+00:00
-- url     : https://prove2.me/submissions/854cdd12-7e75-425d-bac6-1696c0e38633

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {m : ℕ} {L L' : MLat K m} (h : L'.M ≤ L.M) : L'.detSub ≤ L.detSub :=
  Submodule.span_mono fun _ ⟨x, hx, hd⟩ => ⟨x, fun i => h (hx i), hd⟩
end Formalism.L2.LamCM.A2
