-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.mp_shear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:31.859304+00:00
-- url     : https://prove2.me/submissions/93742c00-19cb-4b7a-9510-560ebd8f13d8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_mp_vecMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_det_wMat
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_upper


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
theorem _root_.solution (β : ℂ) (n : ℕ) :
    MeasurePreserving (fun p : BlockCoord n => ((p.1 ᵥ* (wMat n * upper p.2.1), p.2) : BlockCoord n))
      (muBlock β n) (muBlock β n) := by
  have h1 : MeasurePreserving
      (fun q : ((UT n → ℂ) × (Fin n → ℂ)) × (Fin n → ℂ) => (q.1, q.2 ᵥ* (wMat n * upper q.1.1)))
      (((muPi β (UT n)).prod (muPi β (Fin n))).prod (muPi β (Fin n)))
      (((muPi β (UT n)).prod (muPi β (Fin n))).prod (muPi β (Fin n))) := by
    refine (MeasurePreserving.id _).skew_product
      (g := fun (q : (UT n → ℂ) × (Fin n → ℂ)) (a : Fin n → ℂ) => a ᵥ* (wMat n * upper q.1)) ?_ ?_
    · refine Continuous.measurable ?_
      exact Continuous.matrix_vecMul continuous_snd
        (continuous_const.matrix_mul ((continuous_upper n).comp (continuous_fst.comp continuous_fst)))
    · exact Filter.Eventually.of_forall fun q =>
        (mp_vecMul β _ (by rw [Matrix.det_mul, det_upper, mul_one, norm_det_wMat])).map_eq
  exact Measure.measurePreserving_swap.comp (h1.comp Measure.measurePreserving_swap)
end Formalism.FourierDecayAlt.P.G7
