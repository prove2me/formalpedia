-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.io_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:40.05078+00:00
-- url     : https://prove2.me/submissions/c4ec7a29-f5e3-4b9a-982b-eb2a44b4718c

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
theorem _root_.solution (k : K) (x : A) : (io (k • x) : SlopeTestRemainingChoices S A) = k • io x := by
  unfold io
  ext X Y
  by_cases h : X = Y
  · subst h; simp
  · simp [h]
end Formalism.FourierDecayAlt.P.Wd6
