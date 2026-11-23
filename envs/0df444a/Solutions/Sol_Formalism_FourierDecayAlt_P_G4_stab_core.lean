-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.stab_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:13.144851+00:00
-- url     : https://prove2.me/submissions/e5b61386-72a4-4e0b-81ce-605c5f2c99d3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_mul_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} {l u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) :
    l * wMat d * u = wMat d ↔ l = wMat d * u⁻¹ * wMat d := by
  constructor
  · intro h
    calc l = l * wMat d * (u * u⁻¹) * wMat d := by
            rw [upper_mul_inv hu, Matrix.mul_one, Matrix.mul_assoc, w_mul_w, Matrix.mul_one]
      _ = (l * wMat d * u) * u⁻¹ * wMat d := by simp only [Matrix.mul_assoc]
      _ = wMat d * u⁻¹ * wMat d := by rw [h]
  · rintro rfl
    calc wMat d * u⁻¹ * wMat d * wMat d * u = wMat d * (u⁻¹ * ((wMat d * wMat d) * u)) := by
            simp only [Matrix.mul_assoc]
      _ = wMat d := by rw [w_mul_w, Matrix.one_mul, upper_inv_mul hu, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.G4
