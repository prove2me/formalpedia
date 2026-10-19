-- Prove2me | solution 2 for CohnElkies.manuscriptLinearProgram_eq_canonicalPackingPow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:11.408544+00:00
-- url     : https://prove2.me/submissions/ba4943be-e13d-459e-88e8-50ea518a6ea2

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
    {d : ℕ} (hd : 0 < d) :
    linearProgram d =
      (criticalPackingBase + manuscriptPackingRootError d) ^ d := by
  unfold manuscriptPackingRootError
  have hq : 0 ≤ sInf (quotientSet d) := by
    apply Real.sInf_nonneg
    rintro x ⟨f, rfl⟩
    exact (div_pos (admissible_zero_pos f) f.fourier_zero_pos).le
  have hL : 0 ≤ linearProgram d := by
    unfold linearProgram
    have := unitBallVolume_pos d
    positivity
  rw [add_sub_cancel, Real.rpow_inv_natCast_pow hL hd.ne']

