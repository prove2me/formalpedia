-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.parametrisation_map_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:48:55.740825+00:00
-- url     : https://prove2.me/submissions/47c2e7a0-84a4-44db-8924-349863ba61fe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_dilation_map_measure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_parametrisation_map_measurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution :
    (((volume : Measure ℂ).withDensity fun c => ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1)))).prod
      (volume : Measure (HPar k r'))).map (cm1Θ k r') = μx.prod volume := by
  ext s hs
  rw [Measure.map_apply parametrisation_map_measurable hs, Measure.prod_apply (parametrisation_map_measurable hs), Measure.prod_apply hs]
  unfold μx
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_left (parametrisation_map_measurable hs)),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (measurable_measure_prodMk_left hs)]
  apply lintegral_congr
  intro c
  simp only [Pi.mul_apply]
  by_cases hc : c = 0
  · subst hc; simp
  · have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have h1 : Prod.mk c ⁻¹' (cm1Θ k r' ⁻¹' s) =
        (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) ⁻¹' (Prod.mk c ⁻¹' s) := rfl
    have hm : Measurable (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) := by fun_prop
    rw [h1, ← Measure.map_apply hm (measurable_prodMk_left hs), heisenberg_dilation_map_measure c hc, Measure.smul_apply, smul_eq_mul,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [pow_add]
    field_simp
end Formalism.FourierDecayAlt.P.B2x8
