-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:30.588055+00:00
-- url     : https://prove2.me/submissions/09115ec8-1b44-4d69-9199-fc221b31072b

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordLiftInduction
theorem _root_.solution (Ξ : Sesq M) (d K : ℕ) (dat : Fin K → Dat R) (c : Fin K → ℂ)
    (grid : Fin K → Fin (d + 1) → ℝ) (X X' : M) (S : Fin K → ℝ) (B : ℝ)
    (hw : (∏ a, c a) * Ξ X X' =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1)
    (hS : ∀ a, ∑ i, |lagCo (grid a) i| = S a)
    (hB : ∀ j : Fin K → Fin (d + 1),
      ‖Fw Ξ X X' (List.ofFn fun a => (dat a, grid a (j a))) 1 1‖ ≤ B) :
    (∏ a, ‖c a‖) * ‖Ξ X X'‖ ≤ (∏ a, S a) * B := by
  rw [← norm_prod, ← norm_mul, hw]
  refine (norm_sum_le _ _).trans ?_
  simp_rw [← hS]
  rw [prod_univ_sum, sum_mul, Fintype.piFinset_univ]
  refine sum_le_sum fun j _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_prod]
  exact mul_le_mul_of_nonneg_left (hB j) (prod_nonneg fun _ _ => abs_nonneg _)
end Formalism.FourierDecayAlt.P.WordLiftInduction
