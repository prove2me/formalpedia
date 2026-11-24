-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.quotient_measure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:34.042451+00:00
-- url     : https://prove2.me/submissions/14de8d8e-7ae2-4a9c-8f93-261b7f351175

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_vecMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_norm_det_wMat
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_mul_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_lowRow_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_blk_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_inv_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_inv_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_coordU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_comp_equiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_joinU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_invU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_lmulU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.QuotientMeasure := by
  intro n β
  have hι : MeasurePreserving (fun k : UT n → ℂ => coordU (wMat n * (upper k)⁻¹ * wMat n)ᵀ)
      (muPi β (UT n)) (muPi β (UT n)) := by
    simp only [coordU_conj]
    exact (mp_comp_equiv β (revEquiv n)).comp (mp_invU β n)
  have hm : Measurable (Function.uncurry fun (k : UT n → ℂ) (r : BlockCoord n) =>
      ((r.1 ᵥ* (wMat n * (upper k)⁻¹ * wMat n), coordU (upper k * upper r.2.1), upper k *ᵥ r.2.2) :
        BlockCoord n)) := by
    refine Continuous.measurable ?_
    have hk : Continuous fun p : (UT n → ℂ) × BlockCoord n => upper p.1 :=
      (continuous_upper n).comp continuous_fst
    have hki : Continuous fun p : (UT n → ℂ) × BlockCoord n => (upper p.1)⁻¹ :=
      (continuous_inv_upper n).comp continuous_fst
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact Continuous.matrix_vecMul (continuous_fst.comp continuous_snd)
        ((continuous_const.matrix_mul hki).matrix_mul continuous_const)
    · exact (continuous_coordU n).comp (hk.matrix_mul
        ((continuous_upper n).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))))
    · exact Continuous.matrix_mulVec hk (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hS := hι.skew_product (μc := muBlock β n) (μd := muBlock β n) hm
    (Filter.Eventually.of_forall fun k =>
      ((mp_vecMul β (wMat n * (upper k)⁻¹ * wMat n)
          (by rw [Matrix.det_mul, Matrix.det_mul, det_inv_upper, norm_mul, norm_mul, norm_det_wMat]; simp)).prod
        ((mp_lmulU β n k).prod (mp_mulVec β (upper k) (by rw [det_upper]; simp)))).map_eq)
  have hA := (measurePreserving_prodAssoc (muPi β (UT n)) (muPi β (Fin n))
    ((muPi β (UT n)).prod (muPi β (Fin n)))).symm
  have hJ := (mp_joinU β n).prod (mp_joinU β n)
  have hall := hJ.comp (hA.comp hS)
  have he : quotMap n = Prod.map joinU joinU ∘ (MeasurableEquiv.prodAssoc.symm ∘
      fun p : (UT n → ℂ) × BlockCoord n => (coordU (wMat n * (upper p.1)⁻¹ * wMat n)ᵀ,
        ((p.2.1 ᵥ* (wMat n * (upper p.1)⁻¹ * wMat n), coordU (upper p.1 * upper p.2.2.1),
          upper p.1 *ᵥ p.2.2.2) : BlockCoord n))) := by
    funext q
    obtain ⟨k, a, u, b⟩ := q
    simp only [quotMap, Function.comp]
    rw [lowRow_mul, blk_transpose, coordU_blk, blk_mul_upper, coordU_blk, add_zero]
    rfl
  rw [he]
  exact hall
end Formalism.FourierDecayAlt.P
