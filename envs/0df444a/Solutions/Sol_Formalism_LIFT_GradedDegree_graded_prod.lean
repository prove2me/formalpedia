-- Prove2me | solution 1 for Formalism.LIFT.GradedDegree.graded_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:59.947834+00:00
-- url     : https://prove2.me/submissions/c29f0f45-def2-40bd-8186-0e275eb79517

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
theorem _root_.solution (hG : GradedStep) {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (i j : ℕ) (hij : i ≤ j) :
    ∀ m ∈ W.N, ∃ m' ∈ W.N, Polynomial.aeval W.γ
      (∏ k ∈ Finset.Ico i j, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ k))) (B.X ^ i • m)
        = B.X ^ j • m' := by
  induction j, hij using Nat.le_induction with
  | base => intro m hm; exact ⟨m, hm, by simp⟩
  | succ j hij ih =>
    intro m hm
    obtain ⟨m', hm', he⟩ := ih m hm
    obtain ⟨m'', hm'', hg⟩ := hG ℓ A B M D W j m' hm'
    refine ⟨m'', hm'', ?_⟩
    rw [Finset.prod_Ico_succ_top hij, mul_comm, map_mul, Module.End.mul_apply, he, map_sub,
      Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hg]
end Formalism.LIFT.GradedDegree
