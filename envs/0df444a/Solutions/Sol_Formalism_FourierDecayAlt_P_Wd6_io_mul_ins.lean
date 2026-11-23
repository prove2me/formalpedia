-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.io_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:40.062138+00:00
-- url     : https://prove2.me/submissions/e907d084-f502-4545-b30a-ab2e14e9bf08

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_io

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
    (io x : SlopeTestRemainingChoices S A) * ins a (lift0 N) = ∑ r, ∑ s, eU a r s * io (x * N r s) := by
  unfold ins lift0
  simp only [Finset.mul_sum, Matrix.map_apply, io_mul]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← (eU_io a r s x).eq, mul_assoc]
end Formalism.FourierDecayAlt.P.Wd6
