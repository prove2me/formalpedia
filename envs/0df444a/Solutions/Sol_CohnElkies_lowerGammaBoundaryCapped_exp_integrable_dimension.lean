-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryCapped_exp_integrable_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/b575a22c-d353-4c69-a9f6-0cf188337488

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_exp_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 < a) (R D : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  apply lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
    hℓ ha R D
  exact lowerGammaBoundaryLog_dimension_exp_integrable
    hd ha R
end CohnElkies
