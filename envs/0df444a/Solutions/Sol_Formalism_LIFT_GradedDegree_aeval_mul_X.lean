-- Prove2me | solution 1 for Formalism.LIFT.GradedDegree.aeval_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:20.146791+00:00
-- url     : https://prove2.me/submissions/4798b8d1-900e-4db5-a092-69712d5e1521

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LIFT
open Formalism.LIFT.GradedDegree
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
namespace Formalism.LIFT.GradedDegree
theorem _root_.solution {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (p : Polynomial ℤ_[ℓ]) : Polynomial.aeval g (p * Polynomial.X) = Polynomial.aeval g p * g := by
  rw [map_mul, Polynomial.aeval_X]
end Formalism.LIFT.GradedDegree
