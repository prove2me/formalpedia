-- Prove2me | solution 1 for DeletionCode.SelectedWindows.seed_selects_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:21.899921+00:00
-- url     : https://prove2.me/submissions/4e92f4bb-2afc-40b5-b148-92286e04cfea

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_selected_window_cover

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s : Memory) (D k a : ℕ) (hD : D < 3 * (k + 1))
    (ha : a + k ≤ 3 * (k + 1) + D) (hknown : WindowKnown s a k) :
    ∃ w : Slot, SeedKnown s (windowStart D w) (3 * (k + 1)) k := by
  obtain ⟨w, hwa, haw⟩ := selected_window_cover D k a hD ha
  obtain ⟨bits, hread⟩ := hknown
  refine ⟨w, a - windowStart D w, bits, by omega, ?_⟩
  simpa [show windowStart D w + (a - windowStart D w) = a by omega] using hread
end DeletionCode.SelectedWindows
