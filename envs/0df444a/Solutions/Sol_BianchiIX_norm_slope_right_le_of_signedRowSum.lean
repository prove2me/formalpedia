-- Prove2me | solution 1 for BianchiIX.norm_slope_right_le_of_signedRowSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:37:13.259931+00:00
-- url     : https://prove2.me/submissions/e8d08821-74c7-4bfe-ad06-5c1adb0f9b05

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Theorems.Thm_BianchiIX_norm_euler_le_of_signedRowSum
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp


noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


/-- The forward norm slope is controlled without differentiating the norm. -/
theorem solution {f : ℝ → (ι → ℝ)} {t ρ r : ℝ}
    {A : Matrix ι ι ℝ} (hf : HasDerivAt f (A.mulVec (f t)) t)
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hr : ρ * ‖f t‖ < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (‖f s‖ - ‖f t‖) < r := by
  let e : ℝ → (ι → ℝ) := fun s => f s - (f t + (s - t) • A.mulVec (f t))
  have he : HasDerivAt e 0 t := by
    convert! hf.sub ((hasDerivAt_const t (f t)).add
      (((hasDerivAt_id t).sub_const t).smul_const (A.mulVec (f t)))) using 1
    simp
  have he0 : e t = 0 := by simp [e]
  have herr : ∀ᶠ s in 𝓝[>] t, ‖s - t‖⁻¹ * ‖e s - e t‖ < r - ρ * ‖f t‖ :=
    (he.hasDerivWithinAt (s := Ioi t)).limsup_norm_slope_le (by simpa using sub_pos.mpr hr)
  have hdiag : ∀ᶠ s in 𝓝 t, ∀ i, 0 ≤ 1 + (s - t) * A i i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun s : ℝ => 1 + (s - t) * A i i) t := by fun_prop
    exact (hc.eventually (isOpen_Ioi.mem_nhds (by simp))).mono fun _ hs => hs.le
  filter_upwards [herr, hdiag.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hd hst
  have hh : 0 < s - t := sub_pos.mpr hst
  rw [he0, sub_zero, Real.norm_eq_abs, abs_of_pos hh] at hs
  have hEuler := norm_euler_le_of_signedRowSum hA hh.le hd (f t)
  have H : ‖f s‖ - ‖f t‖ ≤ (s - t) * ρ * ‖f t‖ + ‖e s‖ := by
    have H' := norm_sub_norm_le (f s) (f t + (s - t) • A.mulVec (f t))
    change ‖f s‖ - ‖f t + (s - t) • A.mulVec (f t)‖ ≤ ‖e s‖ at H'
    nlinarith only [hEuler, H']
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * ρ * ‖f t‖ + ‖e s‖) =
      ρ * ‖f t‖ + (s - t)⁻¹ * ‖e s‖ := by field_simp
  rw [hid] at H'
  linarith only [H', hs]
