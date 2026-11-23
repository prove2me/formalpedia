-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.eU_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:05.578479+00:00
-- url     : https://prove2.me/submissions/db0cabf9-c410-4f2e-a740-3b819ae6c4ff

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_eU_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_mul_ins

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd3
theorem _root_.solution (a : S) (k i : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    eU a k i * m * ins a N = ∑ s, eU a k s * (m * N i s) := by
  rw [mul_assoc, mul_ins a m N hm, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro r _ hr
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hr), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Wd3
