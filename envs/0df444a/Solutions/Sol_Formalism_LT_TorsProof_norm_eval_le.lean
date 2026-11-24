-- Prove2me | solution 1 for Formalism.LT.TorsProof.norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:14.285095+00:00
-- url     : https://prove2.me/submissions/37539557-e08c-4730-8ed6-a99c887f0791

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof
import Theorems.Thm_Formalism_LT_TorsProof_eval_eq
import Theorems.Thm_Formalism_LT_TorsProof_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.LT Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {π : K} {q : ℕ} {e : Polynomial K}
namespace Formalism.LT.TorsProof
theorem _root_.solution (hq : 2 ≤ q) (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ < 1)
    (hsmall : ‖x‖ ^ (q - 1) ≤ ‖π‖) : ‖e.eval x‖ ≤ ‖π‖ * ‖x‖ := by
  rw [eval_eq]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (norm_nonneg π) (norm_nonneg x))
  intro i _
  rcases eq_or_ne i q with rfl | hiq
  · rw [norm_mul, he.2.2.1, one_mul, norm_pow]
    have : ‖x‖ ^ i = ‖x‖ ^ (i - 1) * ‖x‖ := by rw [← pow_succ]; congr 1; omega
    rw [this]; exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)
  · exact term_le he hx.le hiq
end Formalism.LT.TorsProof
