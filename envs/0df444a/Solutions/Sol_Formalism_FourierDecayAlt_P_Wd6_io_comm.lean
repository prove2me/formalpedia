-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.io_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:00.853281+00:00
-- url     : https://prove2.me/submissions/b49539a7-0315-49ab-acfc-e74f35811397

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show (io x : SlopeTestRemainingChoices S A) * io y = io y * io x
  rw [← io_mul, ← io_mul, h.eq]
end Formalism.FourierDecayAlt.P.Wd6
