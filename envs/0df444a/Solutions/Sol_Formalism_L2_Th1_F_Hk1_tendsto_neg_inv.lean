-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk1.tendsto_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:02.076183+00:00
-- url     : https://prove2.me/submissions/93a90026-9349-4e8f-9d41-3d66aec6c8c2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelIntegralValue

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
open MeasureTheory Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk1
namespace Formalism.L2.Th1.F.Hk1
theorem _root_.solution (c : ℂ) (l : Filter ℝ) (hl : Tendsto (fun x : ℝ => |x + c.re|) l atTop) :
    Tendsto (fun x : ℝ => -((x : ℂ) + c)⁻¹) l (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => ‖(x : ℂ) + c‖) l atTop := by
    refine tendsto_atTop_mono (fun x => ?_) hl
    simpa using Complex.abs_re_le_norm ((x : ℂ) + c)
  have h2 := tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp h1)
  simpa using h2.neg
end Formalism.L2.Th1.F.Hk1
