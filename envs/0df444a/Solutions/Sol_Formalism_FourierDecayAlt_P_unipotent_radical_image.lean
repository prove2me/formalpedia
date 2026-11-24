-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unipotent_radical_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:46:36.971262+00:00
-- url     : https://prove2.me/submissions/98521942-bc5f-44d3-bca0-91a3c29b75d4

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_isMonomial_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.URImage := by
  intro m P hP
  have hPu := isMonomial_unit hP
  ext u
  simp only [Set.mem_setOf_eq, C2.Lstg]
  constructor
  · rintro ⟨hu, u', hu', he⟩
    refine ⟨hu, ut_conjT hu, ?_⟩
    have : P⁻¹ * uᴴ * P = u'⁻¹ := by
      calc P⁻¹ * uᴴ * P = P⁻¹ * uᴴ * P * (u' * u'⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ (ut_unit hu'), Matrix.mul_one]
        _ = P⁻¹ * (uᴴ * P * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
        _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
    rw [this]; exact ut_inv hu'
  · rintro ⟨hu, _, hX⟩
    refine ⟨hu, (P⁻¹ * uᴴ * P)⁻¹, ut_inv hX, ?_⟩
    have e : uᴴ * P = P * (P⁻¹ * uᴴ * P) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_unit hX), Matrix.mul_one]
end Formalism.FourierDecayAlt.P
