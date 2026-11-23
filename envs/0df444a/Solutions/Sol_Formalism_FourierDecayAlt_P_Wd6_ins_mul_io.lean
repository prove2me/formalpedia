-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.ins_mul_io
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:39.343673+00:00
-- url     : https://prove2.me/submissions/de256b6b-09a0-447a-8aac-4c6957859dc3

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
theorem _root_.solution (a : S) (x : A) (N : M2 A) :
    ins a (lift0 N) * (io x : SlopeTestRemainingChoices S A) = ∑ r, ∑ s, eU a r s * io (N r s * x) := by
  unfold ins lift0
  simp only [Finset.sum_mul, Matrix.map_apply, io_mul, mul_assoc]
end Formalism.FourierDecayAlt.P.Wd6
