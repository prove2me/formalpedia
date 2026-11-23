-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.detIdeal_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:36.862836+00:00
-- url     : https://prove2.me/submissions/a3cbcde3-ec0d-439e-90a8-cd4f1d540c7e

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
theorem _root_.solution {m : ℕ} (L : MLat K m) (h : IsFractional (𝓞 K)⁰ L.detSub) :
    (L.detIdeal : Submodule (𝓞 K) K) = L.detSub := by
  have e : L.detIdeal = ⟨L.detSub, h⟩ := dif_pos h
  rw [e]
  rfl
end Formalism.L2.LamCM.A2
