-- Prove2me | solution 2 for CohnElkies.quotientInf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:06:56.883051+00:00
-- url     : https://prove2.me/submissions/d703f427-113f-44f4-a643-cfa90ff73fea

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set


theorem solution
    (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    0 ≤ sInf (quotientSet d) := by
  apply Real.sInf_nonneg
  rintro x ⟨f, rfl⟩
  unfold quotient
  exact div_nonneg (admissible_zero_pos f).le f.fourier_zero_pos.le

