-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_shear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:54.171879+00:00
-- url     : https://prove2.me/submissions/efc47cc3-5f79-4109-b09e-d8fa3f2aee73

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_vecMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_norm_det_wMat
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_det_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_upper

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (n : ℕ) (β : ℂ) :
    MeasurePreserving (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2.1, p.2.2) : BlockCoord n))
      (muBlock β n) (muBlock β n) := by
  have hm : Measurable (Function.uncurry fun (q : (UT n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) =>
      a ᵥ* (wMat n * upper q.1)) := by
    refine Continuous.measurable ?_
    exact Continuous.matrix_vecMul continuous_snd
      (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_fst)))
  have h1 := (MeasurePreserving.id ((muPi β (UT n)).prod (muPi β (Fin n)))).skew_product
    (μc := muPi β (Fin n)) (μd := muPi β (Fin n)) hm
    (Filter.Eventually.of_forall fun q => (mp_vecMul β (wMat n * upper q.1)
      (by rw [Matrix.det_mul, det_upper, mul_one, norm_det_wMat])).map_eq)
  exact (Measure.measurePreserving_swap.comp h1).comp Measure.measurePreserving_swap
end Formalism.FourierDecayAlt.P.G5
