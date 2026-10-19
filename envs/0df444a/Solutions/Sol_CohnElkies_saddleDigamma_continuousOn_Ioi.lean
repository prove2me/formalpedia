-- Prove2me | solution 1 for CohnElkies.saddleDigamma_continuousOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/48c7b4f8-0074-41eb-b6fa-68a60860c9c2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleDigamma_eq_complexDigamma_re
import Theorems.Thm_CohnElkies_complexDigamma_continuousOn_positiveHalfPlane

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    ContinuousOn saddleDigamma (Ioi (0 : ℝ)) := by
  have hmap :
      MapsTo (fun x : ℝ => (x : ℂ))
        (Ioi (0 : ℝ))
        {z : ℂ | 0 < z.re} := by
    intro x hx
    simpa using! hx
  have hcomplex :=
    complexDigamma_continuousOn_positiveHalfPlane.comp
      Complex.continuous_ofReal.continuousOn hmap
  have hre :
      ContinuousOn
        (fun x : ℝ => (Complex.digamma (x : ℂ)).re)
        (Ioi (0 : ℝ)) :=
    Complex.continuous_re.continuousOn.comp hcomplex
      (fun x hx => Set.mem_univ _)
  apply hre.congr
  intro x hx
  exact saddleDigamma_eq_complexDigamma_re hx
end CohnElkies
