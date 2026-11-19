-- Prove2me | solution 1 for DeletionCode.SelectedWindows.selected_window_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:44.694022+00:00
-- url     : https://prove2.me/submissions/6eb283df-be23-477a-a064-0896eb7da7c3

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_Windows_three_windows_cover


set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (D k a : ℕ) (hD : D < 3 * (k + 1))
    (ha : a + k ≤ 3 * (k + 1) + D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a + k ≤ windowStart D w + 3 * (k + 1) := by
  obtain ⟨b, hb, hba, hab⟩ := three_windows_cover k D a hD ha
  rcases hb with hb | hb | hb
  · refine ⟨⟨0, by omega⟩, ?_⟩
    simpa [windowStart, hb] using And.intro hba hab
  · refine ⟨⟨1, by omega⟩, ?_⟩
    simpa [windowStart, hb] using And.intro hba hab
  · refine ⟨⟨2, by omega⟩, ?_⟩
    simpa [windowStart, hb] using And.intro hba hab
end DeletionCode.SelectedWindows
