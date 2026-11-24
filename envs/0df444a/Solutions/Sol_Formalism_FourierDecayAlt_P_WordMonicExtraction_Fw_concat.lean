-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.Fw_concat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:26.4279+00:00
-- url     : https://prove2.me/submissions/c34a4cb9-00f8-4551-844a-c62c5c6ce7ec

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (Ξ : Sesq M) (X X' : M) (l : Dat R × ℝ) (w : List (Dat R × ℝ)) (P P' : R) :
    Fw Ξ X X' (w ++ [l]) P P' =
      Fw Ξ ((evR l.1.B l.2 + algebraMap ℂ R l.1.s * evR l.1.A l.2) • X) (evR l.1.Av (l.2 + 1) • X')
          w P P' -
        Fw Ξ (evR l.1.A l.2 • X) (evR l.1.Bv (l.2 + 1) • X') w P P' := by
  induction w generalizing P P' with
  | nil =>
    simp only [List.nil_append, Fw, mul_smul]
  | cons m w ih =>
    simp only [List.cons_append, Fw]
    rw [ih, ih]
    ring
end Formalism.FourierDecayAlt.P.WordMonicExtraction
