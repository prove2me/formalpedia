-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.id20_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:59.575864+00:00
-- url     : https://prove2.me/submissions/4ee7d89c-1f05-4f8d-ac3e-b87fb366e72f

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB

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
theorem _root_.solution : Id20 := by
  intro l i hl
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  have h1 : ((l:ℝ) - 1) ≠ 0 := by linarith
  have hL : ((l:ℝ)^i) ≠ 0 := by positivity
  constructor
  · unfold gam rho; field_simp; ring
  · unfold r1 del sg; field_simp; ring
end Formalism.BaseCaseIdentities
