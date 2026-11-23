-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.dg_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:42.43788+00:00
-- url     : https://prove2.me/submissions/34a67901-02a3-40f2-9152-1c3cdba57ba2

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
theorem _root_.solution (g h : Ix S → ℂ) : (dg g * dg h : SlopeTestRemainingChoices S A) = dg (fun e => g e * h e) := by
  unfold dg
  rw [Matrix.diagonal_mul_diagonal]
  simp only [map_mul]
end Formalism.FourierDecayAlt.P.Fr11
