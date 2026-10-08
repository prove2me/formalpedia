-- Prove2me | solution 1 for AvramDividend.Classical.tendsto_deriv_zero_of_concave_finite_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:07:07.818975+00:00
-- url     : https://prove2.me/submissions/4f38c194-5b60-4216-a9e9-e1c62e9bcf25

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

theorem solution
    (f : ℝ → ℝ) (L : ℝ)
    (hconc : ConcaveOn ℝ (Ioi (0 : ℝ)) f)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hlim : Tendsto f atTop (𝓝 L)) :
    Tendsto (deriv f) atTop (𝓝 (0 : ℝ)) := by
  have hplus :
      Tendsto (fun x : ℝ => f (x + 1)) atTop (𝓝 L) :=
    hlim.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hminus :
      Tendsto (fun x : ℝ => f (x - 1)) atTop (𝓝 L) := by
    have hshift : Tendsto (fun x : ℝ => x - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    exact hlim.comp hshift
  have hlow :
      Tendsto (fun x : ℝ => f (x + 1) - f x) atTop (𝓝 (0 : ℝ)) := by
    simpa using hplus.sub hlim
  have hupp :
      Tendsto (fun x : ℝ => f x - f (x - 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hlim.sub hminus
  have hlb :
      ∀ᶠ x : ℝ in atTop, f (x + 1) - f x ≤ deriv f x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hxp : 0 < x := by linarith
    have hyp : 0 < x + 1 := by linarith
    have hslope : slope f x (x + 1) = f (x + 1) - f x := by
      rw [slope_def_field]
      have hd : x + 1 - x = (1 : ℝ) := by ring
      rw [hd, div_one]
    calc
      f (x + 1) - f x = slope f x (x + 1) := hslope.symm
      _ ≤ deriv f x :=
        hconc.slope_le_deriv hxp hyp (by linarith) (hdiff x hxp)
  have hub :
      ∀ᶠ x : ℝ in atTop, deriv f x ≤ f x - f (x - 1) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hxp : 0 < x := by linarith
    have hxm : 0 < x - 1 := by linarith
    have hslope : slope f (x - 1) x = f x - f (x - 1) := by
      rw [slope_def_field]
      have hd : x - (x - 1) = (1 : ℝ) := by ring
      rw [hd, div_one]
    calc
      deriv f x ≤ slope f (x - 1) x :=
        hconc.deriv_le_slope hxm hxp (by linarith) (hdiff x hxp)
      _ = f x - f (x - 1) := hslope
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp hlb hub
