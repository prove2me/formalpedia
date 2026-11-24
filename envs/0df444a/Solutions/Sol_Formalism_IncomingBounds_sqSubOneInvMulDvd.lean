-- Prove2me | solution 1 for Formalism.IncomingBounds.sqSubOneInvMulDvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:21.658794+00:00
-- url     : https://prove2.me/submissions/17795996-c0f5-438c-8a7b-4a1f23faeb9b

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : InvWeight := by
  intro l hl n n' hdvd
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (l : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < l - 1).ne'
  have h3 : (l : ℝ) + 1 ≠ 0 := (by linarith : (0 : ℝ) < l + 1).ne'
  have hmR : (n : ℝ) - l * n' = ((l : ℝ) ^ 2 - 1) * m := by exact_mod_cast hm
  have hn : (n : ℝ) = ((l : ℝ) - 1) * ((l : ℝ) + 1) * m + l * n' := by linear_combination hmR
  unfold rho
  rw [hn, show (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) by ring]
  field_simp
  ring
end Formalism.IncomingBounds
