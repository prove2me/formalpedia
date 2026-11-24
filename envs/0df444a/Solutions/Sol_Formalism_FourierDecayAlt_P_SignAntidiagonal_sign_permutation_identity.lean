-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.sign_permutation_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:50:47.475823+00:00
-- url     : https://prove2.me/submissions/56a96a80-d66f-4169-a42b-3b3994330a2c

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignPermutationIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgn_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sgn_step2
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_neg_one_pow_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : SignE := by
  intro s
  refine ⟨?_, ?_⟩
  · unfold sgnW; rw [← pow_add, sgn_step, neg_one_pow_sq]
  · unfold sgnW; rw [← pow_add, sgn_step2, pow_succ, Even.neg_one_pow (Nat.even_mul_succ_self s)]; ring
end Formalism.FourierDecayAlt.P.SignAntidiagonal
