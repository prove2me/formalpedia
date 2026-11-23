-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.ins_mul_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:06.637817+00:00
-- url     : https://prove2.me/submissions/efa27d6a-1ecf-4a99-9b0e-2aabb5680237

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_eU_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul

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
theorem _root_.solution (a : S) (j k : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m)
    (hN : FreeOf2 a N) :
    ins a N * (m * eU a j k) = ∑ r, eU a r k * (N r j * m) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  have h1 : ∀ r s, FreeOf a (N r s) := hN
  have hN' : ∀ r s i j, Commute (eU a i j) (N r s) := fun r s => h1 r s
  rw [← mul_assoc, ins_mul a m N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · have hc : Commute (eU a j k) (N r j * m) := (hN' r j j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro s _ hs
    have hc : Commute (eU a j k) (N r s * m) := (hN' r s j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_neg hs, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h
end Formalism.FourierDecayAlt.P.Wd3
