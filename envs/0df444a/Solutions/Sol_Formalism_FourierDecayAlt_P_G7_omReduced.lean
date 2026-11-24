-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.omReduced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:10.16481+00:00
-- url     : https://prove2.me/submissions/78f45087-fce1-4087-bd62-67a09e5a7016

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_jacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_blockIntegrand_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_integral_affine_fibre
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_mp_consMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_cof
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_remainder
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_embedding_coordMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_pointwise_red

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
theorem _root_.solution : OmReduced := by
  intro m β t c ht V _ _ _ Φ hint
  have hemb := embedding_coordMap (m + 1) t ht
  have hJ := jacobian (m + 1) β t ht
  have hfun : blockIntegrand β (m + 1) Φ t c = Fint β m Φ t c ∘ coordMap (m + 1) t :=
    funext (blockIntegrand_eq β m Φ t c ht)
  have hpos : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  set κ : NNReal := Real.toNNReal ((‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (Real.toNNReal_pos.2 (by positivity)).ne'
  have hF : Integrable (Fint β m Φ t c) (muBlock β (m + 1)) := by
    have h : Integrable (Fint β m Φ t c) (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) :=
      hemb.integrable_map_iff.2 (hfun ▸ hint)
    rw [hJ, ENNReal.smul_def] at h
    exact (integrable_smul_measure (by simpa using hκ0) ENNReal.coe_ne_top).1 h
  have h1 : OmBlock β (m + 1) Φ t c = κ • ∫ p, Fint β m Φ t c p ∂(muBlock β (m + 1)) := by
    unfold OmBlock
    rw [hfun, ← integral_smul_nnreal_measure, ← hJ, hemb.integral_map]
    rfl
  have hmp := mp_consMap β m
  have h2 : ∫ p, Fint β m Φ t c p ∂(muBlock β (m + 1)) = ∫ q, Fint β m Φ t c (consMap m q) ∂(muRed β m) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hF.1)]
  have hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      Cof (strictUpper y.2.1) y.2.2 t) := ((continuous_cof m t).comp continuous_snd).measurable
  have h3 := integral_affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β
    (fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t)
    (fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t)
    (measurable_const.div hcC) ((measurable_const.sub (continuous_remainder m t).measurable).div hcC)
    ((ae_cof_ne' β t ht m).mono fun y hy => div_ne_zero (pow_ne_zero _ ht) hy)
    (fun q => Fint β m Φ t c (consMap m q)) (hF.1.comp_measurePreserving hmp)
  have h4 : ∫ q, Fint β m Φ t c (consMap m q) ∂(muRed β m) = _ := h3
  simp only [pointwise_red β m Φ t c ht] at h4
  rw [integral_smul] at h4
  rw [h1, h2, h4, NNReal.smul_def, ← Complex.coe_smul, smul_smul, smul_smul]
  have hconst : ((‖t‖ ^ ((m + 1) * (m + 2)) : ℝ) : ℂ) * ((κ : ℝ) : ℂ) * ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) = 1 := by
    rw [hκ, Real.coe_toNNReal _ (by positivity), ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : ‖t‖ ^ ((m + 1) * (m + 2)) * (‖t‖ ^ ((m + 1) * (m + 1 + 3)))⁻¹ * ‖t‖ ^ (2 * (m + 1)) = 1 := by
      have e : (m + 1) * (m + 1 + 3) = (m + 1) * (m + 2) + 2 * (m + 1) := by ring
      rw [e, pow_add]
      field_simp
    rw [this, Complex.ofReal_one]
  rw [hconst, one_smul]
  rfl
end Formalism.FourierDecayAlt.P.G7
