-- Prove2me | solution 1 for CohnElkies.quotient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/c299e61a-702e-4e5e-bd27-fbe7710492e5

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap
namespace CohnElkies
theorem _root_.solution {d : ℕ} (f : Admissible d) : 0 < quotient f := by
  exact div_pos (admissible_zero_pos f) f.fourier_zero_pos
end CohnElkies
