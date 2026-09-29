-- Prove2me | solution 1 for Freiman.gap_eventually_periodic_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:40:11.98044+00:00
-- url     : https://prove2.me/submissions/269b2021-64b1-4e63-b495-933c13d2eeb5

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_cfValue_prefix

set_option autoImplicit false
open Freiman

theorem solution (u v : List ℕ+) :
    cfValue (gapEventuallyPeriodic u v) =
      prefixEval u (cfValue (gapEventuallyPeriodic [] v)) := by
  rw [cfValue_prefix (gapEventuallyPeriodic u v) u.length]
  have hp : (List.range u.length).map (gapEventuallyPeriodic u v) = u := by
    apply List.ext_getElem
    · simp
    · intro k hk hku
      simp [gapEventuallyPeriodic, hku]
  rw [hp]
  congr 2
  funext k
  simp [gapEventuallyPeriodic]
