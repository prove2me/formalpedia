-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.euler_factor_product_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:09.293505+00:00
-- url     : https://prove2.me/submissions/da49dd2d-62c7-4c0d-8a65-3a1d73e9e5c6

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne
import Theorems.Thm_Formalism_ZeroFreeDirichlet_euler_factor_term_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ) :
    ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [euler_factor_term_norm_le φ p]
end Formalism.ZeroFreeDirichlet
