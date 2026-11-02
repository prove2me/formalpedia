-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_moving_base_drift_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:32:59.68489+00:00
-- url     : https://prove2.me/submissions/ae1d2ae5-eb87-4e8b-9713-88057f641939

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Set

theorem solution (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (x d : ℝ)
    (a b : ℝ → ℝ)
    (ha : Tendsto a (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x))
    (hb : Tendsto b (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x))
    (hab : ∀ h : ℝ, a h - b h = d * h) :
    Tendsto (fun h : ℝ => h⁻¹ * (w (a h) - w (b h)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (d * deriv w x)) := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  have hpos : ∀ᶠ h : ℝ in F, 0 < h := self_mem_nhdsWithin
  have hpair : Tendsto (fun h : ℝ => (a h, b h)) F (nhds (x, x)) :=
    by simpa only [nhds_prod_eq] using ha.prodMk hb
  have hstrict : HasStrictDerivAt w (deriv w x) x :=
    hw.hasStrictDerivAt (by norm_num)
  have hratio : Tendsto
      (fun h : ℝ => ‖a h - b h‖⁻¹ *
        ‖w (a h) - w (b h) - (a h - b h) * deriv w x‖)
      F (nhds (0 : ℝ)) :=
    (hasDerivAtFilter_iff_tendsto.mp hstrict).comp hpair
  have hratio' : Tendsto (fun h : ℝ => |d| *
      (‖a h - b h‖⁻¹ *
        ‖w (a h) - w (b h) - (a h - b h) * deriv w x‖))
      F (nhds (0 : ℝ)) := by
    convert tendsto_const_nhds.mul hratio using 1 <;> simp
  have hnormeq : (fun h : ℝ =>
        ‖h⁻¹ * (w (a h) - w (b h) - d * h * deriv w x)‖) =ᶠ[F]
      (fun h : ℝ => |d| *
        (‖a h - b h‖⁻¹ *
          ‖w (a h) - w (b h) - (a h - b h) * deriv w x‖)) := by
    filter_upwards [hpos] with h hh
    have hh0 : h ≠ 0 := ne_of_gt hh
    by_cases hd : d = 0
    · have heq : a h = b h := sub_eq_zero.mp (by simpa [hd] using hab h)
      simp [heq, hd]
    · have hdm : |d| ≠ 0 := abs_ne_zero.mpr hd
      have hhm : |h| ≠ 0 := abs_ne_zero.mpr hh0
      simp only [Real.norm_eq_abs, hab h, abs_mul, abs_inv]
      rw [mul_inv_rev]
      field_simp
  have hnorm : Tendsto (fun h : ℝ =>
        ‖h⁻¹ * (w (a h) - w (b h) - d * h * deriv w x)‖)
      F (nhds (0 : ℝ)) := hratio'.congr' hnormeq.symm
  have herr : Tendsto (fun h : ℝ =>
        h⁻¹ * (w (a h) - w (b h) - d * h * deriv w x))
      F (nhds (0 : ℝ)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hsum := herr.add (tendsto_const_nhds (x := d * deriv w x))
  have hsum' : Tendsto
      (fun h : ℝ => h⁻¹ * (w (a h) - w (b h) - d * h * deriv w x) + d * deriv w x)
      F (nhds (d * deriv w x)) := by simpa only [zero_add] using hsum
  apply hsum'.congr'
  filter_upwards [hpos] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  field_simp
  ring
