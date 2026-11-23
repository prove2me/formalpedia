-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.scale_product_measure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:20.022832+00:00
-- url     : https://prove2.me/submissions/f1642d69-4d42-4e61-9ec2-d53b1410c6f8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_affine_change_of_variables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.ScalePi := by
  intro β z ι _ hz
  unfold muPi
  have hA := affine_change_of_variables β z 0 hz
  simp only [add_zero] at hA
  have hfun : (fun v : ι → ℂ => z • v) = fun v i => z * v i := by
    ext v i; simp
  have hc : Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) =
      (Real.toNNReal ((‖z‖ ^ 2)⁻¹)) ^ Fintype.card ι := by
    rw [← Real.toNNReal_pow (by positivity), inv_pow, pow_mul]
  have hsf : SigmaFinite (Measure.map (fun ρ : ℂ => z * ρ) (mu β)) := by
    rw [hA]; infer_instance
  rw [hfun, Measure.pi_map_pi (fun _ => (measurable_const_mul z).aemeasurable)]
  simp only [hA]
  refine Measure.pi_eq fun s hs => ?_
  rw [hc]
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]
end Formalism.FourierDecayAlt.P
