-- Prove2me | solution 1 for CohnElkies.radialProfile_re_weight_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/0805ff3f-49cd-46ed-9fd7-f0f26f93e305

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
    IntegrableOn
      (fun r : ℝ => r ^ (d - 1) * (radialProfile hd g r).re)
      (Ioi 0) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hre :
      Integrable
        (fun x : Euclidean d => (radialProfile hd g ‖x‖).re) := by
    apply g.integrable.re.congr
    filter_upwards [] with x
    change (g x).re = (radialProfile hd g ‖x‖).re
    rw [radialProfile_norm hd g hg x]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul] using!
    (integrable_fun_norm_addHaar
      (volume : Measure (Euclidean d))
      (f := fun r : ℝ => (radialProfile hd g r).re)).mp hre
end CohnElkies
