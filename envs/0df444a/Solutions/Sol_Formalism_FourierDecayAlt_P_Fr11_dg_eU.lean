-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.dg_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:08.440942+00:00
-- url     : https://prove2.me/submissions/d65cfc74-3edd-4662-947e-85e76da8a183

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (g : Ix S → ℂ) (b : S) (i j : Fin 2)
    (h : ∀ x y : Ix S, (∀ c, c ≠ b → x c = y c) → g x = g y) :
    (dg g * eU b i j : SlopeTestRemainingChoices S A) = eU b i j * dg g := by
  apply Matrix.ext
  intro x y
  simp only [dg, eU, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs with hc
  · rw [h x y hc.2.2]
    simp
  · simp
end Formalism.FourierDecayAlt.P.Fr11
