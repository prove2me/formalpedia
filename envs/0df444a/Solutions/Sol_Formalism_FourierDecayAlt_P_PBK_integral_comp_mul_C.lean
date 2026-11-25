-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.integral_comp_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:24.482649+00:00
-- url     : https://prove2.me/submissions/3b72aa24-4e6c-4972-b37d-ba5795c97a07

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_map_mulEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (g : ℂ → E) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∫ z, g (ρ * z) = (‖ρ‖ ^ 2)⁻¹ • ∫ z, g z := by
  have h := integral_map_equiv (μ := (volume : Measure ℂ)) (mulEquiv ρ hρ) g
  rw [map_mulEquiv, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm
end Formalism.FourierDecayAlt.P.PBK
