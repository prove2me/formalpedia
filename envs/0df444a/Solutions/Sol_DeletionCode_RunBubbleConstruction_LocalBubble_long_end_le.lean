-- Prove2me | solution 1 for DeletionCode.RunBubbleConstruction.LocalBubble.long_end_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:38:16.1672+00:00
-- url     : https://prove2.me/submissions/9f2d7c9b-443c-4004-a21a-d1481a82577a

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length


set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns
open DeletionCode.RunBubbleConstruction.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}
namespace DeletionCode.RunBubbleConstruction.LocalBubble
theorem _root_.solution (p : LocalBubble k source target pos orientation) :
    p.before.length + p.bubble.longWord.length ≤ pos + windowLength k := by
  have h := p.edit_start
  have hrho := p.bubble.rho_upper
  rw [p.bubble.left_length] at h
  rw [p.bubble.longWord_length]
  simp only [longLength, BubbleWord.header]
  unfold windowLength at *
  omega
end DeletionCode.RunBubbleConstruction.LocalBubble
