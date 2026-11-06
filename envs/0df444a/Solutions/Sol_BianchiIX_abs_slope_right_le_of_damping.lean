-- Prove2me | solution 1 for BianchiIX.abs_slope_right_le_of_damping
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:54:21.773087+00:00
-- url     : https://prove2.me/submissions/5dc39b0a-8fa9-4cbc-bd4f-ad592b6673ae

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {f : ℝ → ℝ} {t d g B r : ℝ}
    (hf : HasDerivAt f (d * f t + g) t) (hd : d ≤ 0) (hg : |g| ≤ B) (hr : B < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (|f s| - |f t|) < r := by
  let e : ℝ → ℝ := fun s => f s - (f t + (s - t) * (d * f t + g))
  have he : HasDerivAt e 0 t := by
    convert! hf.sub ((hasDerivAt_const t (f t)).add
      (((hasDerivAt_id t).sub_const t).mul_const (d * f t + g))) using 1
    simp
  have he0 : e t = 0 := by simp [e]
  have herr : ∀ᶠ s in 𝓝[>] t, ‖s - t‖⁻¹ * ‖e s - e t‖ < r - B :=
    (he.hasDerivWithinAt (s := Ioi t)).limsup_norm_slope_le (by simpa using sub_pos.mpr hr)
  have hdiag : ∀ᶠ s in 𝓝 t, 0 ≤ 1 + (s - t) * d := by
    have hc : ContinuousAt (fun s : ℝ => 1 + (s - t) * d) t := by fun_prop
    exact (hc.eventually (isOpen_Ioi.mem_nhds (by simp))).mono fun _ h => h.le
  filter_upwards [herr, hdiag.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hdiag hst
  have hh : 0 < s - t := sub_pos.mpr hst
  rw [he0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh] at hs
  have hEuler : |f t + (s - t) * (d * f t + g)| ≤ |f t| + (s - t) * B := by
    rw [show f t + (s - t) * (d * f t + g) = (1 + (s - t) * d) * f t + (s - t) * g by ring]
    calc
      _ ≤ |(1 + (s - t) * d) * f t| + |(s - t) * g| := abs_add_le _ _
      _ = (1 + (s - t) * d) * |f t| + (s - t) * |g| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hdiag, abs_of_pos hh]
      _ ≤ |f t| + (s - t) * B := add_le_add
        (mul_le_of_le_one_left (abs_nonneg _) (by nlinarith only [hd, hh.le]))
        (mul_le_mul_of_nonneg_left hg hh.le)
  have hdiff := norm_sub_norm_le (f s) (f t + (s - t) * (d * f t + g))
  simp only [Real.norm_eq_abs] at hdiff
  change |f s| - |f t + (s - t) * (d * f t + g)| ≤ |e s| at hdiff
  have H : |f s| - |f t| ≤ (s - t) * B + |e s| := by linarith only [hdiff, hEuler]
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * B + |e s|) = B + (s - t)⁻¹ * |e s| := by field_simp
  rw [hid] at H'
  linarith only [H', hs]
