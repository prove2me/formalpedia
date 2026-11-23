-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leading_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:13.062655+00:00
-- url     : https://prove2.me/submissions/153a5f2b-a30c-423e-b464-c88cf7bcb819

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_isStrictUpper_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_mulVec_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_mulVec_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_sum_mul_zero_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CofLead := by
  intro m X B ρ' hX
  constructor
  · rw [Cof, sum_mul_zero_pow m (fun j => ((-X) ^ j *ᵥ B) 0)]
    have e : (-X) ^ m = ((-1 : ℂ) ^ m) • X ^ m := by
      rw [← smul_pow, neg_one_smul]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, pow_mulVec_zero hX, smul_eq_mul]
  · rw [R0, sum_mul_zero_pow m (fun j => ∑ k : Fin m, ρ' k * ((-X) ^ j *ᵥ B) k.succ)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [pow_mulVec_succ (isStrictUpper_neg hX), mul_zero]
end Formalism.FourierDecayAlt.P
