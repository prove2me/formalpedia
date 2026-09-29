-- Prove2me | solution 2 for Freiman.lower_bounded_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T09:31:33.854983+00:00
-- url     : https://prove2.me/submissions/78f1dfbc-c481-4279-8ba5-36fd46239d56

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_history_window_reduction
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lower_generic_suffix_birth

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n) : lowerBoundedHistory h n := by
  exact lower_history_window_reduction lower_forced_reflections
    (fun t' h' n' hh' l hl right hnew hchanged =>
      lower_generic_suffix_birth t' h' n' hh' l hl right hnew hchanged)
    t h n hh
