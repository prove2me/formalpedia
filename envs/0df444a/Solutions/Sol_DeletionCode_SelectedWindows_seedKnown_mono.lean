-- Prove2me | solution 1 for DeletionCode.SelectedWindows.seedKnown_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:11.538483+00:00
-- url     : https://prove2.me/submissions/0e0bedb4-18aa-4b5e-bce0-9893943f594f

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_mono

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s t : Memory) (start L k : ℕ)
    (hext : Extends s t) (h : SeedKnown s start L k) :
    SeedKnown t start L k := by
  rcases h with ⟨r, bits, hr, hread⟩
  obtain ⟨newBits, hnew⟩ := windowKnown_mono s t (start + r) k hext ⟨bits, hread⟩
  exact ⟨r, newBits, hr, hnew⟩
end DeletionCode.SelectedWindows
