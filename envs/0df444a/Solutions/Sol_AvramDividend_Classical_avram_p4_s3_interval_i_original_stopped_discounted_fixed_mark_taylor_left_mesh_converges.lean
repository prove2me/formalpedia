-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_i_original_stopped_discounted_fixed_mark_taylor_left_mesh_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:05:48.64519+00:00
-- url     : https://prove2.me/submissions/d7e822fa-7bd8-4471-b812-20ce3df3ac66

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ω : Ω) (t : ℝ≥0)
    (s : ℕ → ℝ≥0) (hsle : ∀ n, s n ≤ t)
    (hst : Tendsto s atTop (𝓝 t))
    (w : ℝ → ℝ) (q z : ℝ)
    (hwy : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t))
    (hwyz : ContinuousAt w (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t + z))
    (hder : ContinuousAt (deriv w) (Function.leftLim
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t)) :
    let K : ℝ≥0 → ℝ := fun u =>
      Real.exp (-(q * (u : ℝ))) *
        ((fun y : ℝ => w (y + z) - w y - z * deriv w y)
          (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))
    Tendsto
      (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
      atTop
      (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t)) := by
  let Y : ℝ≥0 → ℝ := fun u =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v ω - rightLimit D v ω) u
  let H : ℝ → ℝ := fun y => w (y + z) - w y - z * deriv w y
  let K : ℝ≥0 → ℝ := fun u =>
    Real.exp (-(q * (u : ℝ))) * H (Y u)
  change Tendsto
    (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
    atTop (𝓝 ((if t ≤ τ ω then (1 : ℝ) else 0) * K t))
  have hTaylor : Tendsto (fun n => H (Y (s n))) atTop
      (𝓝 (H (Y t))) := by
    simpa only [H, Y] using
      (avram_p4_s3_interval_i_original_prejump_fixed_mark_taylor_mesh_converges
        X x D hD ω t s hsle hst w z hwy hwyz hder)
  have hExp : Tendsto
      (fun n => Real.exp (-(q * (s n : ℝ)))) atTop
      (𝓝 (Real.exp (-(q * (t : ℝ))))) := by
    have hc : Continuous (fun u : ℝ≥0 =>
        Real.exp (-(q * (u : ℝ)))) := by
      fun_prop
    exact hc.continuousAt.tendsto.comp hst
  have hK : Tendsto (fun n => K (s n)) atTop (𝓝 (K t)) := by
    change Tendsto
      (fun n => Real.exp (-(q * (s n : ℝ))) * H (Y (s n)))
      atTop (𝓝 (Real.exp (-(q * (t : ℝ))) * H (Y t)))
    exact hExp.mul hTaylor
  by_cases ht : t ≤ τ ω
  · have hle : ∀ n, s n ≤ τ ω := fun n => (hsle n).trans ht
    simpa [ht, hle] using hK
  · have hlt : τ ω < t := lt_of_not_ge ht
    have hEventually : ∀ᶠ n : ℕ in atTop, τ ω < s n :=
      hst.eventually (isOpen_Ioi.mem_nhds hlt)
    have hZero : (fun n =>
        (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
        =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
      filter_upwards [hEventually] with n hn
      simp [not_le.mpr hn]
    have hConv : Tendsto
        (fun n => (if s n ≤ τ ω then (1 : ℝ) else 0) * K (s n))
        atTop (𝓝 (0 : ℝ)) :=
      (tendsto_congr' hZero).2 tendsto_const_nhds
    simpa [ht] using hConv
