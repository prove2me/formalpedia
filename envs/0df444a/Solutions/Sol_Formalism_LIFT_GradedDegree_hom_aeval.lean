-- Prove2me | solution 1 for Formalism.LIFT.GradedDegree.hom_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:32:00.974494+00:00
-- url     : https://prove2.me/submissions/3fd6e3f2-7368-4926-97be-7699877fa5e4

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded
import Theorems.Thm_Formalism_LIFT_GradedDegree_aeval_mul_X

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
theorem _root_.solution {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WD B M D} {W' : WD B M D'} (f : Hom W W')
    (p : Polynomial ℤ_[ℓ]) : ∀ x, f.f (Polynomial.aeval W.γ p x) = Polynomial.aeval W'.γ p (f.f x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, LinearMap.map_smul_of_tower]
  · intro p q hp hq x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  · intro k c h x
    rw [pow_succ, ← mul_assoc, aeval_mul_X, aeval_mul_X, Module.End.mul_apply,
      Module.End.mul_apply, h, f.γ_comm]
end Formalism.LIFT.GradedDegree
