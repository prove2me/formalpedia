-- Prove2me | solution 1 for CohnElkies.integral_re_eq_zero_of_antiFourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/1ddd27c4-cc80-4878-bef1-f5a2edf22507

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
theorem _root_.solution {d : ℕ}
    (g : TestFunction d)
    (hanti : (𝓕 g : TestFunction d) = -g)
    (hzero : g (0 : Euclidean d) = 0) :
    (∫ x : Euclidean d, (g x).re) = 0 := by
  have hfourierzero :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) = 0 := by
    rw [hanti]
    simpa using! hzero
  have hfourier_integral :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
        ∫ x : Euclidean d, g x := by
    change (𝓕 (g : Euclidean d → ℂ)) 0 = _
    rw [Real.fourier_eq']
    simp
  calc
    (∫ x : Euclidean d, (g x).re) =
        (∫ x : Euclidean d, g x).re :=
      integral_re g.integrable
    _ = ((𝓕 g : TestFunction d) (0 : Euclidean d)).re := by
      rw [hfourier_integral]
    _ = 0 := by
      rw [hfourierzero]
      rfl
end CohnElkies
