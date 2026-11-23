-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.detIdeal_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:29.104175+00:00
-- url     : https://prove2.me/submissions/11f18192-d9c9-4738-b45f-8f89730fc9a6

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_isFractional
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_coe
import Theorems.Thm_Formalism_L2_LamCM_A2_det_mem
import Theorems.Thm_Formalism_L2_LamCM_A2_exists_det_ne

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
theorem _root_.solution {m : ℕ} (L : MLat K m) (hL : L.Good) : L.detIdeal ≠ 0 := by
  have hf := detSub_isFractional L hL.1
  obtain ⟨x, hx, hd⟩ := exists_det_ne L.M hL.2.1
  intro h0
  have hmem : (Matrix.of x).det ∈ (L.detIdeal : Submodule (𝓞 K) K) := by
    rw [detIdeal_coe L hf]; exact det_mem L x hx
  rw [h0] at hmem
  exact hd ((FractionalIdeal.mem_zero_iff _).1 hmem)
end Formalism.L2.LamCM.A2
