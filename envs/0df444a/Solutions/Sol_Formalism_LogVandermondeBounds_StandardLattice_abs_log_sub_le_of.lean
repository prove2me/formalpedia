-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.abs_log_sub_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:40.633152+00:00
-- url     : https://prove2.me/submissions/19f333fd-0baf-450f-ba55-2624b7348025

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution {x y m e : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y)
    (hxy : |x - y| ≤ e) : |Real.log x - Real.log y| ≤ e / m := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hm hy
  have h1 : Real.log x - Real.log y ≤ (x - y) / y := by
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at this
    rw [sub_div, div_self hy0.ne']; linarith
  have h2 : Real.log y - Real.log x ≤ (y - x) / x := by
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at this
    rw [sub_div, div_self hx0.ne']; linarith
  have he : 0 ≤ e := le_trans (abs_nonneg _) hxy
  have ha := abs_le.mp hxy
  have h3 : (x - y) / y ≤ e / m := by
    rw [div_le_div_iff₀ hy0 hm]
    nlinarith
  have h4 : (y - x) / x ≤ e / m := by
    rw [div_le_div_iff₀ hx0 hm]
    nlinarith
  rw [abs_le]; constructor <;> linarith
end Formalism.LogVandermondeBounds.StandardLattice
