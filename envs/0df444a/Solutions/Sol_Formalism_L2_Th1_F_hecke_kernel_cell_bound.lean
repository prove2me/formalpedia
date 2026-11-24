-- Prove2me | solution 1 for Formalism.L2.Th1.F.hecke_kernel_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:53.894224+00:00
-- url     : https://prove2.me/submissions/cf429411-5d26-42c6-adcc-94eb06e13944

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_summ
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_cell_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : HkCellBound := by
  intro τ hτ
  refine ⟨fun p => 4 * (Hk2.kap τ ^ 2)⁻¹ * ((Hk2.kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹, ?_,
    fun s p hs0 hs1 hp => Hk2.cell_bound hτ hp hs0 hs1⟩
  have h := Hk2.summ.mul_left (4 * (Hk2.kap τ ^ 2)⁻¹ * (Hk2.kap τ ^ 3)⁻¹)
  refine h.congr (fun p => ?_)
  rw [mul_pow, mul_inv]
  ring
end Formalism.L2.Th1.F
