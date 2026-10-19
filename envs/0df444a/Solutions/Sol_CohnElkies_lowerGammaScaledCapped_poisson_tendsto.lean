-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCapped_poisson_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/ff4afe53-509c-4d6b-8dd5-ffca7e868f78

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCapped_poisson_product_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaled_poisson_product_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {c σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) (n : ℝ) (((d : ℝ) / 2) * Y))
      atTop
      (𝓝 (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryLog ((d : ℝ) / 2)
          (c * Real.sqrt d) (((d : ℝ) / 2) * Y))) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  let b : ℝ → ℝ := fun Y =>
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y)
  let K : ℝ → ℝ := fun Y => stripPoissonKernel σ (s - Y)
  have hbase : Integrable (fun Y : ℝ => K Y * b Y) :=
    lowerGammaScaled_poisson_product_integrable
      hd (R := c * Real.sqrt d) hbelow habove s
  apply tendsto_integral_of_dominated_convergence
    (fun Y : ℝ => |K Y * b Y|)
  · intro n
    exact
      (lowerGammaScaledCapped_poisson_product_integrable
        hd (R := c * Real.sqrt d) (D := (n : ℝ))
        hbelow habove s).aestronglyMeasurable
  · exact hbase.abs
  · intro n
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with Y hY
    have harg : ((d : ℝ) / 2) * Y ≠ 0 :=
      mul_ne_zero hℓ.ne' hY
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hclip : |min (b Y) (n : ℝ)| ≤ |b Y| := by
      rcases le_total (b Y) (n : ℝ) with hle | hle
      · rw [min_eq_left hle]
      · rw [min_eq_right hle,
          abs_of_nonneg hn,
          abs_of_nonneg (le_trans hn hle)]
        exact hle
    change
      ‖K Y *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) (n : ℝ)
          (((d : ℝ) / 2) * Y)‖ ≤
        |K Y * b Y|
    rw [lowerGammaBoundaryCapped, if_neg harg,
      Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hclip (abs_nonneg (K Y))
  · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with Y hY
    have harg : ((d : ℝ) / 2) * Y ≠ 0 :=
      mul_ne_zero hℓ.ne' hY
    have ht : Tendsto (fun n : ℕ => (n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop (R := ℝ)
    have hevent : ∀ᶠ n : ℕ in atTop, b Y ≤ (n : ℝ) :=
      ht.eventually (Ici_mem_atTop (b Y))
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    change
      K Y * b Y =
        K Y * lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) (n : ℝ)
          (((d : ℝ) / 2) * Y)
    rw [lowerGammaBoundaryCapped, if_neg harg, min_eq_left hn]
end CohnElkies
