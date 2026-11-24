-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.heisenberg_dilation_map_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:24.81322+00:00
-- url     : https://prove2.me/submissions/b1f66c64-6646-4f8e-b989-9ad3c802b6d5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_map_smul_volume
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_map_mul_volume_real

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
theorem _root_.solution (c : ℂ) (hc : c ≠ 0) :
    (volume : Measure (HPar k r')).map (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) =
      ENNReal.ofReal ((‖c‖ ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • volume := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have e : (fun x : HPar k r' => (c • x.1, ‖c‖ ^ 2 * x.2)) =
      Prod.map (fun y : Fin (2 * r' + k + 1) → ℂ => c • y) (fun s : ℝ => ‖c‖ ^ 2 * s) := rfl
  rw [e, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ (measurable_const_smul c) (measurable_const_mul _),
    map_smul_volume c hc, map_mul_volume_real _ (by positivity), Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [abs_of_pos (by positivity), ← mul_inv, ← pow_add]
end Formalism.FourierDecayAlt.P.B2x8
