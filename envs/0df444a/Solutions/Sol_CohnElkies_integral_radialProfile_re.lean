-- Prove2me | solution 1 for CohnElkies.integral_radialProfile_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/45ba40b7-46fa-4179-9ddd-1ea57cb70783

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g) :
    (∫ x : Euclidean d, (g x).re) =
      radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * (radialProfile hd g r).re := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  calc
    (∫ x : Euclidean d, (g x).re) =
        ∫ x : Euclidean d, (radialProfile hd g ‖x‖).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [radialProfile_norm hd g hg x]
    _ = radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * (radialProfile hd g r).re := by
      simpa [radialSurfaceArea, volume_real_unitBall hd,
        nsmul_eq_mul, finrank_euclideanSpace_fin, mul_assoc,
        smul_eq_mul] using!
        (integral_fun_norm_addHaar
          (volume : Measure (Euclidean d))
          (fun r : ℝ => (radialProfile hd g r).re))
end CohnElkies
