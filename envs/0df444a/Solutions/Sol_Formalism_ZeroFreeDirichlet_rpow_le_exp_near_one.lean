-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.rpow_le_exp_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:20:34.686809+00:00
-- url     : https://prove2.me/submissions/428845a2-53b2-45c5-b953-ee1f9478b805

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Theorems.Thm_Formalism_ZeroFreeDirichlet_two_le_log_three_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Finset
noncomputable section
namespace Formalism.ZeroFreeDirichlet
private lemma rpow_le_exp_three_halves_of_le_log (q : ℕ) (hq : 3 ≤ q) (x t : ℝ) (hx : 1 ≤ x) (hxq : x ≤ 3 * q)
    (ht : t ≤ 3 / (2 * Real.log (3 * q))) : x ^ t ≤ Real.exp (3 / 2) := by
  have hL : 2 ≤ Real.log (3 * q) := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlxL : Real.log x ≤ Real.log (3 * q) := Real.log_le_log hx0 hxq
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have h1 : Real.log x * t ≤ Real.log x * (3 / (2 * Real.log (3 * q))) := mul_le_mul_of_nonneg_left ht hlx
  have h2 : Real.log x * (3 / (2 * Real.log (3 * q))) ≤ Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) :=
    mul_le_mul_of_nonneg_right hlxL (by positivity)
  have h3 : Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) = 3 / 2 := by field_simp; try ring
  linarith
end Formalism.ZeroFreeDirichlet
end
end

set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) :
    x ^ (3 / (2 * Real.log (3 * q))) ≤ Real.exp (3 / 2) := by
  have hqR : (0 : ℝ) ≤ q := by positivity
  exact rpow_le_exp_three_halves_of_le_log q hq x _ hx (by linarith) le_rfl
end Formalism.ZeroFreeDirichlet
