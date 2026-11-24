-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.redIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:59.638545+00:00
-- url     : https://prove2.me/submissions/c6afb266-c2ef-4561-8e14-9f737494d0ef

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_affine_fibre
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_blockIntegrand_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_cof
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_remainder
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_embedding_coordMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_jacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_mp_consMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_pointwise_red
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_G7_ae_cof_ne__e121f0100f6f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution : RedIntegrable := by
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
  have hmp := mp_consMap β m
  have hG : Integrable (fun q => Fint β m Φ t c (consMap m q)) (muRed β m) :=
    hmp.integrable_comp_of_integrable hF
  have hcC : Measurable (fun y : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) =>
      Cof (strictUpper y.2.1) y.2.2 t) := ((continuous_cof m t).comp continuous_snd).measurable
  set α : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => t ^ (m + 1) / Cof (strictUpper y.2.1) y.2.2 t with hα
  set γ : (Fin m → ℂ) × (UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ) → ℂ :=
    fun y => (-(c * t ^ (m + 1)) - R0 (strictUpper y.2.1) y.2.2 y.1 t) / Cof (strictUpper y.2.1) y.2.2 t with hγ
  have hαm : Measurable α := measurable_const.div hcC
  have hγm : Measurable γ := (measurable_const.sub (continuous_remainder m t).measurable).div hcC
  have hm := affine_fibre ((muPi β (Fin m)).prod ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))) β
    α γ hαm hγm ((ae_cof_ne' β t ht m).mono fun y hy => div_ne_zero (pow_ne_zero _ ht) hy)
  have hT : Measurable (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m)) := by fun_prop
  have hd : Measurable (fun p : RedCoord m => (‖α p.2‖₊ ^ 2 : NNReal)) := by fun_prop
  have hG' : Integrable (fun q => Fint β m Φ t c (consMap m q))
      (Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal)))) := by
    have : Measure.map (fun p : RedCoord m => ((α p.2 * p.1 + γ p.2, p.2) : RedCoord m))
        ((muRed β m).withDensity (fun p => ((‖α p.2‖₊ ^ 2 : NNReal) : ENNReal))) = muRed β m := hm
    rw [this]; exact hG
  have h5 := hG'.comp_measurable hT
  have h6 := (integrable_withDensity_iff_integrable_smul hd).1 h5
  have h7 : Integrable (fun q : RedCoord m => ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) •
      redIntegrand β m Φ (c * t ^ (m + 1)) t q) (muRed β m) := by
    refine h6.congr (Filter.Eventually.of_forall fun q => ?_)
    have := pointwise_red β m Φ t c ht q
    simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Function.comp]
    rw [← Complex.coe_smul]
    exact this
  have hne : ((‖t‖ ^ (2 * (m + 1)) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  exact (integrable_smul_iff hne _).1 h7
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
