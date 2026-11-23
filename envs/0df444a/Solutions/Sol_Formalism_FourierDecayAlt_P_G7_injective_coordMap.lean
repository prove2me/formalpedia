-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.injective_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:22.51006+00:00
-- url     : https://prove2.me/submissions/19d638cc-3739-4549-84f8-9dba10354f2a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_wMat_ne_zero


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
theorem _root_.solution (n : ℕ) (t : ℂ) (ht : t ≠ 0) : Function.Injective (coordMap n t) := by
  rintro ⟨a, v, b⟩ ⟨a', v', b'⟩ h
  simp only [coordMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hv : v = v' := smul_right_injective _ ht h2
  have hb : b = b' := smul_right_injective _ ht h3
  subst hv hb
  have h4 : a ᵥ* (wMat n * G.upper v) = a' ᵥ* (wMat n * G.upper v) := smul_right_injective _ ht h1
  have hM : IsUnit (wMat n * G.upper v).det := by
    rw [Matrix.det_mul, det_upper, mul_one]
    exact (det_wMat_ne_zero n).isUnit
  have h5 := congrArg (fun x => x ᵥ* (wMat n * G.upper v)⁻¹) h4
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one] at h5
  rw [h5]
end Formalism.FourierDecayAlt.P.G7
