-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.head_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:40.74736+00:00
-- url     : https://prove2.me/submissions/e3bab6d1-0b80-4446-8d95-1c244a646fee

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_Fw_ind

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
theorem _root_.solution (Ξ : Sesq M) (X X' : M) {d : ℕ} (D : Dat R) (g : Fin (d + 1) → ℝ) (c : ℂ)
    (h : ∀ Q Q' : R, ∑ i, ((lagCo g i : ℝ) : ℂ) * one Ξ D (g i) (Q • X) (Q' • X') =
      c * Ξ (Q • X) (Q' • X'))
    (w : List (Dat R × ℝ)) :
    ∑ i, ((lagCo g i : ℝ) : ℂ) * Fw Ξ X X' ((D, g i) :: w) 1 1 = c * Fw Ξ X X' w 1 1 := by
  have key := Fw_ind Ξ X X' (fun Φ => ∑ i, ((lagCo g i : ℝ) : ℂ) *
      (Φ (evR D.B (g i) + algebraMap ℂ R D.s * evR D.A (g i)) (evR D.Av (g i + 1)) -
        Φ (evR D.A (g i)) (evR D.Bv (g i + 1))) = c * Φ 1 1) ?_ ?_ w 1 1
  · simpa [Fw] using key
  · intro Φ Ψ hΦ hΨ
    simp only
    rw [mul_sub, ← hΦ, ← hΨ, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  · intro Q Q'
    simpa [one, mul_smul] using h Q Q'
end Formalism.FourierDecayAlt.P.WordLiftInduction
