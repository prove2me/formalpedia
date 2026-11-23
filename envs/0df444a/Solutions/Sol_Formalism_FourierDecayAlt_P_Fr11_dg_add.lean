-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.dg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:09.582412+00:00
-- url     : https://prove2.me/submissions/10d54acd-eeac-4335-b707-8280b545fee0

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
theorem _root_.solution (g h : Ix S → ℂ) : (dg g + dg h : SlopeTestRemainingChoices S A) = dg (fun e => g e + h e) := by
  unfold dg
  rw [Matrix.diagonal_add]
  simp only [map_add]
end Formalism.FourierDecayAlt.P.Fr11
