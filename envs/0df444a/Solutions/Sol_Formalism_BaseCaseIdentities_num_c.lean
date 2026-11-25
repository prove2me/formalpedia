-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.num_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:24.558904+00:00
-- url     : https://prove2.me/submissions/a8bf071d-8934-4496-8c51-e7ec8f566b2d

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Theorems.Thm_Formalism_BaseCaseIdentities_rho_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_rho_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BaseCaseIdentities
namespace Formalism.BaseCaseIdentities
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 3 ≤ j) :
    1 + rho l ≤ -((j:ℝ) - 1) + (l:ℝ)^j * rho l := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hr := rho_pos hl
  have hm := rho_mul hl
  induction j, hj using Nat.le_induction with
  | base =>
    have h3 : 0 ≤ ((l:ℝ)^3 - 1 - 3 * ((l:ℝ)^2 - 1)) * rho l := by
      apply mul_nonneg _ hr.le
      nlinarith [mul_nonneg (sq_nonneg (l:ℝ)) (sub_nonneg.2 h2)]
    push_cast
    nlinarith
  | succ j hj ih =>
    have h4 : (l:ℝ)^2 ≤ (l:ℝ)^j := pow_le_pow_right₀ (by linarith) (by omega)
    have h5 : 0 ≤ ((l:ℝ)^j * ((l:ℝ) - 1) - ((l:ℝ)^2 - 1)) * rho l := by
      apply mul_nonneg _ hr.le
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith
end Formalism.BaseCaseIdentities
