-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.diagScalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:42.695504+00:00
-- url     : https://prove2.me/submissions/8e505941-69b1-4676-a1cd-e1c5110bd583

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
theorem _root_.solution (x y : SlopeTestRemainingChoices S A) : d0 (x * y) = d0 x * d0 y := by
  unfold d0
  rw [Matrix.diagonal_mul_diagonal]
end Formalism.FourierDecayAlt.P.Wd6
