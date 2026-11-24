-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_le_const_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:11.429539+00:00
-- url     : https://prove2.me/submissions/efe95e8d-b9d0-4a6c-b7b2-23873dd0ec50

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExcBoundOf

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
theorem _root_.solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log (3 * x) ≤ K * x ^ δ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨Real.log 3 + 1 / δ, add_pos hl3 (div_pos one_pos hδ), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have h2 : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ
  have h4 : Real.log 3 ≤ Real.log 3 * x ^ δ := by nlinarith
  have h5 : (Real.log 3 + 1 / δ) * x ^ δ = Real.log 3 * x ^ δ + x ^ δ / δ := by ring
  rw [Real.log_mul (by norm_num) hx0.ne', h5]
  linarith
end Formalism.ZeroFreeDirichlet
