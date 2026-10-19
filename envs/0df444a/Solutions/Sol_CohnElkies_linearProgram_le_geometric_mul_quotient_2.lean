-- Prove2me | solution 2 for CohnElkies.linearProgram_le_geometric_mul_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:32.665308+00:00
-- url     : https://prove2.me/submissions/d476baea-76fd-4848-91c7-25950f492b72

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution
    {d : ℕ} (f : Admissible d) :
    linearProgram d ≤
      (unitBallVolume d / (2 : ℝ) ^ d) * quotient f := by
  unfold linearProgram
  have hbdd : BddBelow (quotientSet d) := ⟨0, by
    rintro q ⟨g, rfl⟩; exact (div_pos (admissible_zero_pos g) g.fourier_zero_pos).le⟩
  exact mul_le_mul_of_nonneg_left (csInf_le hbdd ⟨f, rfl⟩)
    (div_nonneg (unitBallVolume_pos d).le (by positivity))

