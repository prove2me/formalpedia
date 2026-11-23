-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.deg_detLine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:16.276801+00:00
-- url     : https://prove2.me/submissions/8b734445-5f88-47a2-bc5d-638867dde9ba

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
theorem _root_.solution {m : ℕ} (L : MLat K m) : L.detLine.deg =
    -Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) - ∑ σ, Real.log (Real.sqrt (L.H σ).det.re) := rfl
end Formalism.L2.LamCM.A2
