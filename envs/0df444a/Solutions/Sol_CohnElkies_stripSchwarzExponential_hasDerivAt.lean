-- Prove2me | solution 1 for CohnElkies.stripSchwarzExponential_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/ddd16621-ef64-43dc-a208-4e89a9b7ff42

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripSchwarzExponential ℓ w y)
      (stripSchwarzExponential ℓ z y *
        ((Real.pi : ℂ) / (2 * (ℓ : ℂ)))) z := by
  have haffine :=
    ((((hasDerivAt_id z).sub_const (y : ℂ)).add_const
      (Complex.I * (ℓ : ℂ))).const_mul (Real.pi : ℂ)).div_const
      (2 * (ℓ : ℂ))
  unfold stripSchwarzExponential
  convert! haffine.cexp using 1
  all_goals simp
end CohnElkies
