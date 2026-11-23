-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.ins_mul_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:04.862922+00:00
-- url     : https://prove2.me/submissions/bd4bad7e-e8ff-44aa-b4b7-9603c619ae39

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
theorem _root_.solution (a : S) (N : M2 (SlopeTestRemainingChoices S A)) (hN : FreeOf2 a N) (j m : Fin 2) :
    ins a N * eU a j m = ∑ k, eU a k m * N k j := by
  unfold ins
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [mul_assoc, ← (hN k j j m).eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro l _ hl
    rw [mul_assoc, ← (hN k l j m).eq, ← mul_assoc, eU_mul, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Wd2
