-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.abs_log_sub_le_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:39.801417+00:00
-- url     : https://prove2.me/submissions/5086113b-90da-4780-b8ef-035cf2472893

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
theorem _root_.solution {x y e : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : |x - y| ≤ e) :
    |Real.log x - Real.log y| ≤ Real.log (1 + e) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have ha := abs_le.mp hxy
  have he : 0 ≤ e := le_trans (abs_nonneg _) hxy
  have h1 : Real.log x - Real.log y ≤ Real.log (1 + e) := by
    rw [← Real.log_div hx0.ne' hy0.ne']
    apply Real.log_le_log (div_pos hx0 hy0)
    rw [div_le_iff₀ hy0]; nlinarith
  have h2 : Real.log y - Real.log x ≤ Real.log (1 + e) := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    apply Real.log_le_log (div_pos hy0 hx0)
    rw [div_le_iff₀ hx0]; nlinarith
  rw [abs_le]; constructor <;> linarith
end Formalism.LogVandermondeBounds.StandardLattice
