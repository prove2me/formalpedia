-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.Rh0_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:38.911844+00:00
-- url     : https://prove2.me/submissions/77b8d774-c048-476e-82d8-9d76ca7dcbe8

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

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
theorem _root_.solution (a : S) (D : K) : (Rh0 a D : M2 (SlopeTestRemainingChoices S A))ᵀ = Rht0 a D := by
  unfold Rh0 Rht0 P0 Q0
  ext i j
  simp [Matrix.one_apply, eq_comm]
end Formalism.FourierDecayAlt.P.Wd6
