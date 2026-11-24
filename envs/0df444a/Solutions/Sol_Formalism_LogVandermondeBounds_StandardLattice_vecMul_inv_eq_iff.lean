-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.vecMul_inv_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:37:41.267354+00:00
-- url     : https://prove2.me/submissions/7578e2f3-f67f-4835-9f34-e7526187db66

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {F : Type} [Field F] {n : ℕ} (v : Fin n → F) (A : GL (Fin n) F) :
    Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v ↔
      Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v := by
  constructor
  · intro h
    calc Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F)
        = Matrix.vecMul (Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
            (A : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]
  · intro h
    calc Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
        = Matrix.vecMul (Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F))
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h]
      _ = v := by rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
end Formalism.LogVandermondeBounds.StandardLattice
