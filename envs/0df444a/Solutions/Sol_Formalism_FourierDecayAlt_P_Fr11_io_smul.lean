-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.io_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:09.087322+00:00
-- url     : https://prove2.me/submissions/9d1f9b64-bffa-4852-a70f-da433ea0cced

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
theorem _root_.solution (c : ℂ) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  apply Matrix.ext
  intro i j
  simp [io, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply]
end Formalism.FourierDecayAlt.P.Fr11
