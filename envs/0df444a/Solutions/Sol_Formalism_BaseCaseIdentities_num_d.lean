-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.num_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:36.818576+00:00
-- url     : https://prove2.me/submissions/1ed405ea-6b82-4ece-a91e-fbe6a33a4038

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Theorems.Thm_Formalism_BaseCaseIdentities_rho_pos

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
theorem _root_.solution {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 1 ≤ j) :
    1 + rho l ≤ -(j:ℝ) + (l:ℝ)^j * (1 + rho l) := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hr := rho_pos hl
  induction j, hj using Nat.le_induction with
  | base => push_cast; nlinarith
  | succ j hj ih =>
    have h4 : (1:ℝ) ≤ (l:ℝ)^j := one_le_pow₀ (by linarith)
    have h5 : 1 ≤ (l:ℝ)^j * (((l:ℝ) - 1) * (1 + rho l)) := by
      have : 1 ≤ ((l:ℝ) - 1) * (1 + rho l) := by nlinarith
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith
end Formalism.BaseCaseIdentities
