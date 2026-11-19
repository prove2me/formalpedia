-- Prove2me | solution 1 for DeletionCode.SelectedWindows.adjacent_window_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:22.638937+00:00
-- url     : https://prove2.me/submissions/97a1d4ff-a2f2-41b9-9fc3-c66eb920dc3e

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_subblock
import Theorems.Thm_DeletionCode_Windows_three_windows_overlap

section
namespace DeletionCode.SelectedWindows
open Windows PartialWords Recovery
private theorem seedKnown_of_overlap (s : Memory) (a b L k : ℕ)
    (h : WindowKnown s a L)
    (ha : max a b + k ≤ a + L) (hb : max a b + k ≤ b + L) :
    SeedKnown s b L k := by
  have hma : a ≤ max a b := le_max_left a b
  have hmb : b ≤ max a b := le_max_right a b
  obtain ⟨bits, hread⟩ := windowKnown_subblock s a L (max a b) k h hma ha
  refine ⟨max a b - b, bits, by omega, ?_⟩
  simpa [show b + (max a b - b) = max a b by omega] using hread
variable {B : Type*}
end DeletionCode.SelectedWindows
end

set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery
namespace DeletionCode.SelectedWindows
theorem _root_.solution (s : Memory) (D k : ℕ) (v w : Slot)
    (hD : D < 3 * (k + 1)) (hadj : AdjSlot v w)
    (hknown : WindowKnown s (windowStart D v) (3 * (k + 1))) :
    SeedKnown s (windowStart D w) (3 * (k + 1)) k := by
  apply seedKnown_of_overlap s (windowStart D v) (windowStart D w)
    (3 * (k + 1)) k hknown
  all_goals
    have hover := three_windows_overlap k D hD
    have hhalf : D / 2 ≤ D := Nat.div_le_self D 2
    fin_cases v <;> fin_cases w <;>
      simp [AdjSlot, windowStart] at hadj ⊢ <;> omega
end DeletionCode.SelectedWindows
