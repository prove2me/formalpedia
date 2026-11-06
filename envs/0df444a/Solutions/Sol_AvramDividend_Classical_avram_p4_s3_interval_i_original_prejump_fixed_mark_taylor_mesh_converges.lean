-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:15:50.481206+00:00
-- url     : https://prove2.me/submissions/15e95c42-0243-4feb-83bb-c7556c0e9e12

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Pointwise physical fixed-mark nonlinear Itô–Meyer Taylor kernel
convergence from actual original controlled pre-jump mesh values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (z : ℝ)
    (hwy : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))
    (hwyz : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z))
    (hder : ContinuousAt (deriv w) (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) :
    Tendsto
      (fun n =>
        let y := Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s n)
        w (y + z) - w y - z * deriv w y)
      atTop
      (𝓝 ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
        (Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))) := by
  let Y : ℝ≥0 → ℝ := fun u =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v ω - rightLimit D v ω) u
  have hY : Tendsto (fun n => Y (s n)) atTop (𝓝 (Y t)) := by
    simpa only [Y] using
      (avram_p4_s3_interval_i_original_postpayment_prejump_left_mesh_converges
        X x D hD ω t s hsle hst)
  have hYz : Tendsto (fun n => Y (s n) + z) atTop
      (𝓝 (Y t + z)) := hY.add tendsto_const_nhds
  have hwz := hwyz.tendsto.comp hYz
  have hww := hwy.tendsto.comp hY
  have hd := hder.tendsto.comp hY
  have hz : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
  have hTaylor := (hwz.sub hww).sub (hz.mul hd)
  change Tendsto
    (fun n => w (Y (s n) + z) - w (Y (s n)) -
      z * deriv w (Y (s n))) atTop
    (𝓝 (w (Y t + z) - w (Y t) - z * deriv w (Y t))) at hTaylor
  exact hTaylor
