-- Prove2me | solution 1 for Formalism.LT.TorsProof.term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:47.298941+00:00
-- url     : https://prove2.me/submissions/89651ff2-4909-4ec0-8ff4-4ef1abb23551

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof

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
theorem _root_.solution (he : IsLTPoly q π e) {x : K} (hx : ‖x‖ ≤ 1) {i : ℕ} (hiq : i ≠ q) :
    ‖e.coeff i * x ^ i‖ ≤ ‖π‖ * ‖x‖ := by
  obtain ⟨h0, h1, -, hrest⟩ := he
  rcases Nat.lt_or_ge i 1 with hi | hi
  · have : i = 0 := by omega
    subst this; simp [h0, mul_nonneg (norm_nonneg π) (norm_nonneg x)]
  · rcases eq_or_ne i 1 with rfl | hi1
    · simp [h1]
    · rw [norm_mul, norm_pow]
      have hxi : ‖x‖ ^ i ≤ ‖x‖ := pow_le_of_le_one (norm_nonneg x) hx (by omega)
      exact mul_le_mul (hrest i hi1 hiq) hxi (by positivity) (norm_nonneg π)
end Formalism.LT.TorsProof
