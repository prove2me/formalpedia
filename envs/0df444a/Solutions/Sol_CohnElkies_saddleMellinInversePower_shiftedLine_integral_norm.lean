-- Prove2me | solution 1 for CohnElkies.saddleMellinInversePower_shiftedLine_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/d834f559-d837-4cad-a4c3-33f868a2a19b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {r a : ℝ} (hr : 0 < r)
    (F : ℂ → ℂ)
    (hF : Integrable
      (fun t : ℝ => F ((a : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ t : ℝ,
      ‖saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        F ((a : ℂ) + (t : ℂ) * Complex.I)‖) =
      r ^ (-a) *
        (∫ t : ℝ,
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
  calc
    (∫ t : ℝ,
      ‖saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        F ((a : ℂ) + (t : ℂ) * Complex.I)‖) =
      ∫ t : ℝ,
        r ^ (-a) *
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        rw [norm_mul,
          saddleMellinInversePower_shiftedLine_norm hr a t]
    _ = r ^ (-a) *
        (∫ t : ℝ,
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖) :=
      integral_const_mul_of_integrable hF.norm
end CohnElkies
