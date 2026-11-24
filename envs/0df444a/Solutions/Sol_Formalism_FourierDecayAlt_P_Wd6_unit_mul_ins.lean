-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.unit_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:38.277192+00:00
-- url     : https://prove2.me/submissions/47e0b3cb-040d-46ac-a6b9-d93886b5d110

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_unit_mul

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
theorem _root_.solution (a : S) (j i : Fin 2) (x : A) (N : M2 A) :
    (eU a j i : SlopeTestRemainingChoices S A) * io x * ins a (lift0 N) = ∑ s, eU a j s * io (x * N i s) := by
  unfold ins lift0
  simp only [Finset.mul_sum, Matrix.map_apply, unit_mul]
  simp
end Formalism.FourierDecayAlt.P.Wd6
