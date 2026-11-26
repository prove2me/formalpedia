-- Prove2me | solution 1 for Eden.tangentialRate_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:54.357859+00:00
-- url     : https://prove2.me/submissions/b7386c9b-5b26-4965-8adb-97eb44c8c782

import Definitions.Def_Eden_Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eden_Algebra
import Theorems.Thm_Eden_tangentialRate_add_two

set_option autoImplicit true
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    -2 ≤ tangentialRate s := by
  have h := mul_nonneg hs₀ (show 0 ≤ 3 - s by linarith)
  linarith [tangentialRate_add_two s]
end Eden
