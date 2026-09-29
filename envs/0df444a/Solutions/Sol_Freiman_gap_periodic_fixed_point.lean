-- Prove2me | solution 1 for Freiman.gap_periodic_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:41:47.715078+00:00
-- url     : https://prove2.me/submissions/5bcc1f32-9592-445b-bf7b-5715f85ff83c

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_cfValue_prefix

set_option autoImplicit false
open Freiman

theorem solution (v : List ℕ+) (hv : v ≠ []) :
    cfValue (gapEventuallyPeriodic [] v) =
      prefixEval v (cfValue (gapEventuallyPeriodic [] v)) := by
  conv_lhs => rw [cfValue_prefix (gapEventuallyPeriodic [] v) v.length]
  have hp : (List.range v.length).map (gapEventuallyPeriodic [] v) = v := by
    apply List.ext_getElem
    · simp
    · intro k hk hkv
      simp [gapEventuallyPeriodic, Nat.mod_eq_of_lt hkv, hkv]
  rw [hp]
  congr 2
  funext k
  simp [gapEventuallyPeriodic]
