-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.Fw_ind
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:48.906388+00:00
-- url     : https://prove2.me/submissions/7be1fd88-2e54-4199-ae02-10039dabafbc

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
theorem _root_.solution (Ξ : Sesq M) (X X' : M) (T : (R → R → ℂ) → Prop)
    (hsub : ∀ Φ Ψ, T Φ → T Ψ → T (fun P P' => Φ P P' - Ψ P P'))
    (hbase : ∀ Q Q' : R, T (fun P P' => Ξ ((P * Q) • X) ((P' * Q') • X'))) :
    ∀ (w : List (Dat R × ℝ)) (Q Q' : R), T (fun P P' => Fw Ξ X X' w (P * Q) (P' * Q')) := by
  intro w
  induction w with
  | nil => intro Q Q'; exact hbase Q Q'
  | cons l w ih =>
    intro Q Q'
    simp only [Fw, mul_assoc]
    exact hsub _ _ (ih _ _) (ih _ _)
end Formalism.FourierDecayAlt.P.WordLiftInduction
