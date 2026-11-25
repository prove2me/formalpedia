-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.quotient_measure_long_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:16.408151+00:00
-- url     : https://prove2.me/submissions/fd3a56dc-0220-4eca-94f7-73357189210a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_coordU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_continuous_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_coordU_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_comp_equiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_invU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_lmulU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.FourierUniquenessMirabolic
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.QuotientMeasureLong := by
  intro d β
  have hι : MeasurePreserving (fun k : UT d → ℂ => coordU (wMat d * (upper k)⁻¹ * wMat d)ᵀ)
      (muPi β (UT d)) (muPi β (UT d)) := by
    simp only [G5.coordU_conj]
    exact (G5.mp_comp_equiv β (G5.revEquiv d)).comp (G5.mp_invU β d)
  have hm : Measurable (Function.uncurry fun (k : UT d → ℂ) (u : UT d → ℂ) => coordU (upper k * upper u)) := by
    refine Continuous.measurable ?_
    exact (G5.continuous_coordU d).comp
      (((G5.continuous_upper d).comp continuous_fst).matrix_mul ((G5.continuous_upper d).comp continuous_snd))
  exact hι.skew_product (μc := muPi β (UT d)) (μd := muPi β (UT d)) hm
    (Filter.Eventually.of_forall fun k => (G5.mp_lmulU β d k).map_eq)
end Formalism.FourierDecayAlt.P
