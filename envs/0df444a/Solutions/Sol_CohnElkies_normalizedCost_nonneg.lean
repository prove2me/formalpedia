-- Prove2me | solution 1 for CohnElkies.normalizedCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/6fdfaba6-f633-4bc5-9e0e-a7b7450988de

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_quotient_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap
namespace CohnElkies
theorem _root_.solution {d : ℕ} (f : Admissible d) :
    0 ≤ normalizedCost f := by
  exact div_nonneg (Real.rpow_nonneg (quotient_pos f).le _)
    (Real.sqrt_nonneg _)
end CohnElkies
