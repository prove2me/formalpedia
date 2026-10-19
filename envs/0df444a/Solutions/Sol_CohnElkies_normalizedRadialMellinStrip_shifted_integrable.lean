-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_shifted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/217d6adc-f2dd-4a73-bcde-9dc212c660ea

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_shifted_eq_fourier
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_weighted_fourier_integrable

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
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ =>
      normalizedRadialMellinStrip hd f R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) := by
  have hfourier :=
    normalizedRadialLogProfile_weighted_fourier_integrable
      hd f hreal hR ha
  have hscale : (2 * Real.pi)⁻¹ ≠ 0 := by
    exact inv_ne_zero
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscaled := hfourier.comp_mul_right' hscale
  apply hscaled.congr
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using!
    (normalizedRadialMellinStrip_shifted_eq_fourier
      hd f hreal R hR a t).symm
end CohnElkies
