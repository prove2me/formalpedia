-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedLowerClip_poisson_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/960d7a41-79d5-4c7c-97c5-98b79291486c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCapped_poisson_product_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedLowerClip_poisson_integrable

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
    {d : ℕ} (hd : 0 < d) {c D σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
          lowerGammaScaledCappedLowerClip
            d c D (n : ℝ) Y)
      atTop
      (𝓝 (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))) := by
  let b : ℝ → ℝ := fun Y =>
    lowerGammaBoundaryCapped ((d : ℝ) / 2)
      (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)
  let K : ℝ → ℝ := fun Y => stripPoissonKernel σ (s - Y)
  have hbase : Integrable (fun Y : ℝ => K Y * b Y) :=
    lowerGammaScaledCapped_poisson_product_integrable
      hd (R := c * Real.sqrt d) (D := D)
      hbelow habove s
  apply tendsto_integral_of_dominated_convergence
    (fun Y : ℝ => |K Y * b Y|)
  · intro n
    exact
      (lowerGammaScaledCappedLowerClip_poisson_integrable
        hd (c := c) (D := D) (n := (n : ℝ))
        hbelow habove s).aestronglyMeasurable
  · exact hbase.abs
  · intro n
    filter_upwards [] with Y
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hclip :
        |max (b Y) (-(n : ℝ))| ≤ |b Y| := by
      rcases le_total (b Y) (-(n : ℝ))
        with hle | hle
      · rw [max_eq_right hle,
          abs_of_nonpos (neg_nonpos.mpr hn),
          abs_of_nonpos (le_trans hle (neg_nonpos.mpr hn))]
        linarith
      · rw [max_eq_left hle]
    change
      ‖K Y * max (b Y) (-(n : ℝ))‖ ≤ |K Y * b Y|
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hclip (abs_nonneg (K Y))
  · filter_upwards [] with Y
    have ht : Tendsto (fun n : ℕ => -(n : ℝ))
        atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have hevent : ∀ᶠ n : ℕ in atTop, -(n : ℝ) ≤ b Y :=
      ht.eventually (Iic_mem_atBot (b Y))
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    change
      K Y * b Y = K Y * max (b Y) (-(n : ℝ))
    rw [max_eq_left hn]
end CohnElkies
