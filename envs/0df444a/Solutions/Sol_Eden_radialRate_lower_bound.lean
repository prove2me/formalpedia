-- Prove2me | solution 1 for Eden.radialRate_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:52.864487+00:00
-- url     : https://prove2.me/submissions/0bf0c023-3cee-40a1-aadb-157a754b6dfd

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
import Theorems.Thm_Eden_radialRate_add_four

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    -4 ≤ radialRate s := by
  have h := mul_nonneg (sub_nonneg.mpr hs₂) (show 0 ≤ 5 * s + 1 by linarith)
  linarith [radialRate_add_four s]
end Eden
