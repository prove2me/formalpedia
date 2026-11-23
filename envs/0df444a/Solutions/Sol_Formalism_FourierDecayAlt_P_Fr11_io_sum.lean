-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.io_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:09.156306+00:00
-- url     : https://prove2.me/submissions/3dda4e7b-3632-4372-b364-a9010822f5ed

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
theorem _root_.solution {J : Type} (s : Finset J) (x : J → A) : (io (∑ j ∈ s, x j) : SlopeTestRemainingChoices S A) = ∑ j ∈ s, io (x j) := by
  simp only [io, map_sum]
end Formalism.FourierDecayAlt.P.Fr11
