-- Prove2me | solution 1 for CohnElkies.norm_radialProfile_eq_abs_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/f17a2d37-2d9c-4807-a2c1-68bee1f099c2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_real

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
    (g : TestFunction d) (hg : IsRealValued g) (r : ℝ) :
    ‖radialProfile hd g r‖ =
      |(radialProfile hd g r).re| := by
  have hvalue :
      radialProfile hd g r =
        ((radialProfile hd g r).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using! radialProfile_real hd g hg r
  calc
    ‖radialProfile hd g r‖ =
        ‖((radialProfile hd g r).re : ℂ)‖ :=
      congrArg Norm.norm hvalue
    _ = |(radialProfile hd g r).re| := by
      simp [Complex.norm_real, Real.norm_eq_abs]
end CohnElkies
