-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/2d724c29-ee1a-40f8-afaa-d297fd4b1b64

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_re_weight_integrable
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_eq

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
    (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) :
    Integrable (normalizedRadialLogProfile hd g R) := by
  have hweight := radialProfile_re_weight_integrable hd g hg
  have hexp :=
    (integrable_scaled_exp_change_Ioi hR
      (fun r : ℝ => r ^ (d - 1) *
        (radialProfile hd g r).re)).mp hweight
  have hscaled :=
    hexp.const_mul (radialSurfaceArea d / radialL1Mass g)
  apply hscaled.congr
  filter_upwards [] with v
  simpa [smul_eq_mul] using!
    (normalizedRadialLogProfile_eq hd g R v).symm
end CohnElkies
