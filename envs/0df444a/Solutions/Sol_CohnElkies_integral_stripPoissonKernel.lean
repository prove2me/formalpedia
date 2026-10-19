-- Prove2me | solution 1 for CohnElkies.integral_stripPoissonKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/40e0796c-f4df-4e01-be1d-77061a3ef08b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_abs
import Theorems.Thm_CohnElkies_stripPoissonKernel_integral_Ioi

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    (∫ T : ℝ, stripPoissonKernel σ T) = stripBottomMass σ := by
  calc
    (∫ T : ℝ, stripPoissonKernel σ T) =
        ∫ T : ℝ, stripPoissonKernel σ |T| := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun T => (stripPoissonKernel_abs σ T).symm)
    _ = 2 * ∫ T in Ioi (0 : ℝ), stripPoissonKernel σ T :=
      integral_comp_abs
    _ = 2 * (1 / 2 - stripAngle σ / (2 * Real.pi)) := by
      rw [stripPoissonKernel_integral_Ioi hbelow habove]
    _ = stripBottomMass σ := by
      unfold stripAngle stripBottomMass
      field_simp [Real.pi_ne_zero]
      ring
end CohnElkies
