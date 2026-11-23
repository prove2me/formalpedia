-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.integral_affine_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:33.817975+00:00
-- url     : https://prove2.me/submissions/b73e1d2a-2657-4b65-9563-6c9aa4e07192

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_affine_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (β : ℂ)
    (α γ : Y → ℂ) (hα : Measurable α) (hγ : Measurable γ) (h0 : ∀ᵐ y ∂ν, α y ≠ 0)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G : ℂ × Y → V)
    (hG : AEStronglyMeasurable G ((mu β).prod ν)) :
    ∫ p, G p ∂((mu β).prod ν) =
      ∫ p, ((‖α p.2‖ ^ 2 : ℝ) : ℂ) • G (α p.2 * p.1 + γ p.2, p.2) ∂((mu β).prod ν) := by
  have hT : Measurable (fun p : ℂ × Y => (α p.2 * p.1 + γ p.2, p.2)) := by fun_prop
  have hd : Measurable (fun p : ℂ × Y => (‖α p.2‖₊ ^ 2 : NNReal)) := by fun_prop
  have hm := affine_fibre ν β α γ hα hγ h0
  conv_lhs => rw [← hm]
  rw [integral_map hT.aemeasurable (by rw [hm]; exact hG), integral_withDensity_eq_integral_smul hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm]
  rw [← Complex.coe_smul]
end Formalism.FourierDecayAlt.P.G7
