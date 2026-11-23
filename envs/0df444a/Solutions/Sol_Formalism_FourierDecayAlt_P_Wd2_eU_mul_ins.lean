-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.eU_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:05.342519+00:00
-- url     : https://prove2.me/submissions/5edb2e69-0546-4966-a5e3-82234d73a9ba

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_eU_mul

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
theorem _root_.solution (a : S) (m i : Fin 2) (N : M2 (SlopeTestRemainingChoices S A)) :
    eU a m i * ins a N = ∑ l, eU a m l * N i l := by
  unfold ins
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro k _ hk
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Wd2
