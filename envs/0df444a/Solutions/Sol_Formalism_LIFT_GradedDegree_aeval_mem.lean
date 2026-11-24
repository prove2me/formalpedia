-- Prove2me | solution 1 for Formalism.LIFT.GradedDegree.aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:59.203319+00:00
-- url     : https://prove2.me/submissions/303041c2-00e9-4736-8bf3-fdfa1872c427

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
theorem _root_.solution {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (S : D → Prop) (hadd : ∀ x y, S x → S y → S (x + y))
    (hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x)) (hg : ∀ x, S x → S (g x))
    (p : Polynomial ℤ_[ℓ]) : ∀ x, S x → S (Polynomial.aeval g p x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x hx
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact hsmul c x hx
  · intro p q hp hq x hx
    rw [map_add, LinearMap.add_apply]
    exact hadd _ _ (hp x hx) (hq x hx)
  · intro k c h x hx
    rw [pow_succ, ← mul_assoc, aeval_mul_X, Module.End.mul_apply]
    exact h _ (hg x hx)
end Formalism.LIFT.GradedDegree
