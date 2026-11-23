-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.det_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.793806+00:00
-- url     : https://prove2.me/submissions/db7556ec-d4ab-409b-81ef-f60364d24b2b

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
theorem _root_.solution {m : ℕ} (L : MLat K m) (x : Fin m → Fin m → K) (hx : ∀ i, x i ∈ L.M) :
    (Matrix.of x).det ∈ L.detSub :=
  Submodule.subset_span ⟨x, hx, rfl⟩
end Formalism.L2.LamCM.A2
