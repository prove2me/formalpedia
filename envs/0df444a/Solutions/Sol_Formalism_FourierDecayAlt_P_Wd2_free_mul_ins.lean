-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.free_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:44.135382+00:00
-- url     : https://prove2.me/submissions/4037f5d5-48fc-4d83-b8d4-de1b810e044b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (a : S) (x : SlopeTestRemainingChoices S A) (hx : FreeOf a x) (N : M2 (SlopeTestRemainingChoices S A)) :
    x * ins a N = ins a (Matrix.of fun k l => x * N k l) := by
  unfold ins
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.of_apply, ← mul_assoc, ← mul_assoc, (hx i j).eq]
end Formalism.FourierDecayAlt.P.Wd2
