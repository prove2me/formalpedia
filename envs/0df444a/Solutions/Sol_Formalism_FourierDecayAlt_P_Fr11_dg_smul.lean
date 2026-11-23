-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.dg_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:08.938026+00:00
-- url     : https://prove2.me/submissions/99b98e49-33d7-4489-9b15-188becbc5134

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
theorem _root_.solution (c : ℂ) (g : Ix S → ℂ) : (c • dg g : SlopeTestRemainingChoices S A) = dg (fun e => c * g e) := by
  apply Matrix.ext
  intro i j
  simp only [dg, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [Algebra.smul_def]
end Formalism.FourierDecayAlt.P.Fr11
