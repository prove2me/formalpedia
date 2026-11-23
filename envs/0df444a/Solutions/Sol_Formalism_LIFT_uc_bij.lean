-- Prove2me | solution 1 for Formalism.LIFT.uc_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:23.412875+00:00
-- url     : https://prove2.me/submissions/0a01ef80-8111-43d4-a785-27cd7436beab

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
namespace Formalism.LIFT
theorem _root_.solution (W : WD B M D) (k : ℕ) : Function.Bijective (fun x : D => B.Q ^ k • x) := by
  have h : (fun x : D => B.Q ^ k • x) = (fun x : D => B.Q • x)^[k] := by
    funext x
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ← ih, pow_succ', mul_smul]
  rw [h]
  exact W.Q_bij.iterate k
end Formalism.LIFT
