-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_antidiagonal_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:20:34.774463+00:00
-- url     : https://prove2.me/submissions/375d8b1a-39a4-448d-aea6-e93720b6859d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_antiW_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_stabilizer_antidiagonal


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
theorem _root_.solution : C2.StabAntidiagExact := by
  intro s l u t hu ht
  have hW := c2x2_antiW_sq s
  constructor
  · intro h
    have h1 : l * C2.antiW s * u = C2.antiW s := by
      have : t • (l * C2.antiW s * u) = t • C2.antiW s := by
        rw [← h]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      exact smul_right_injective _ ht this
    calc l = l * C2.antiW s * u * u⁻¹ * C2.antiW s := by
          rw [Matrix.mul_assoc (l * C2.antiW s) u, Matrix.mul_nonsing_inv _ (ut_unit hu), Matrix.mul_one,
            Matrix.mul_assoc, hW, Matrix.mul_one]
      _ = C2.antiW s * u⁻¹ * C2.antiW s := by rw [h1]
  · rintro rfl
    exact (stabilizer_antidiagonal s u t hu ht).2.1
end Formalism.FourierDecayAlt.P
