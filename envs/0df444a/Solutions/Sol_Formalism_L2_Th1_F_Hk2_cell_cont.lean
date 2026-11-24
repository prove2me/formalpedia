-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.cell_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:07.331839+00:00
-- url     : https://prove2.me/submissions/eebddfeb-c38d-47dc-a2d0-9452f5605d67

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_hk_cont

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
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) :
    Continuous fun s : ℝ => hkCell τ s p := by
  unfold hkCell
  refine Continuous.sub ?_ ?_
  · have h := (hk_cont hτ hp p.1).comp (Continuous.prodMk continuous_id (continuous_const (y := (0 : ℝ))))
    simpa [Function.uncurry, Function.comp_def] using h
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hk_cont hτ hp p.1) 0 1
end Formalism.L2.Th1.F.Hk2
