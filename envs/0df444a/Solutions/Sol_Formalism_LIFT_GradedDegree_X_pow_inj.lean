-- Prove2me | solution 1 for Formalism.LIFT.GradedDegree.X_pow_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:58.44945+00:00
-- url     : https://prove2.me/submissions/7d8a1479-04da-4c74-93d6-4945111a3a68

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
theorem _root_.solution {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (k : ℕ) (x : D) (h : B.X ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply W.X_inj
    rw [← mul_smul, ← pow_succ']
    exact h
end Formalism.LIFT.GradedDegree
