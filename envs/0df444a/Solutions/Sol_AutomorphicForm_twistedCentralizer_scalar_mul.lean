-- Prove2me | solution 1 for AutomorphicForm.twistedCentralizer_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8d9e8842-3762-5545-9e79-98512a4f46cc

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedCentralizer_scalar_mul

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem B5A1.scalarGL_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (c : R) := rfl
  simp only [Units.val_mul, h]
  exact (Matrix.scalar_commute (c : R) (fun r' => mul_comm _ _) _).eq

theorem solution
    (K L A : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A]
    (σ : L ≃ₐ[K] L) (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      AutomorphicForm.twistedCentralizer K L A σ δ := by
  ext t
  simp only [AutomorphicForm.twistedCentralizer, AutomorphicForm.mem_sigmaCentralizer_iff]
  have key : t * (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) * ((AutomorphicForm.sigmaGL K L A σ) t)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c * (t * δ * ((AutomorphicForm.sigmaGL K L A σ) t)⁻¹) := by
    rw [← mul_assoc t _ δ, ← B5A1.scalarGL_comm c t]
    simp only [mul_assoc]
  rw [key]
  exact mul_left_cancel_iff

end S_AutomorphicForm_twistedCentralizer_scalar_mul
end P2MW
export P2MW.S_AutomorphicForm_twistedCentralizer_scalar_mul (solution)
