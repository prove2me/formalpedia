-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb28_original_finite_mark_physical_floor_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:51:44.60779+00:00
-- url     : https://prove2.me/submissions/b2bd2691-d008-4ca0-b4df-6c3e2577dfcb

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_A_K_common_realtime_ae_limit
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_real_horizon_away_ruin_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_A_floor_rate_eventually_eq_sample
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) (hMassPos : 0 < X.ν (Iio (0 : ℝ))) (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (ω : Ω) (hRuinNonzero : ruinTime X x D ω ≠ 0)
    (hSource : ∀ r : ℝ≥0, r ≤ (⟨T, le_of_lt hT⟩ : ℝ≥0) →
      X.X r ω = (r : ℝ) * X.drift) :
    let U : ℝ≥0 → ℝ := fun t =>
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) * ψ (U t)
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal
    let F : ℕ → ℝ → ℝ := fun n r =>
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        let i : ℕ := ⌊(r / T) * ((n : ℝ) + 2)⌋₊
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
           0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
        then rate (u n i) else 0
      else 0
    let G : ℕ → ℝ → ℝ := fun n r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T - T / ((n : ℝ) + 2) ∧
          (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    let f : ℝ → ℝ := fun r =>
      let t : ℝ≥0 := Real.toNNReal r
      if 0 < r ∧ r < T ∧
          (t : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then rate t else 0
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      Tendsto (fun n => F n r) atTop (𝓝 (f r))) ∧
    (∀ᵐ r ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      Tendsto (fun n => G n r) atTop (𝓝 (f r))) := by
  classical
  let U : ℝ≥0 → ℝ := fun t =>
    Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let ψ : ℝ → ℝ := fun b => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν
  let rate : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))) * ψ (U t)
  have hSource' : ∀ r : ℝ≥0, (r : ℝ) ≤ T →
      X.X r ω = (r : ℝ) * X.drift := by
    intro r hr
    exact hSource r (by exact_mod_cast hr)
  have hAe :=
    avram_bvb_b23_original_A_K_common_realtime_ae_limit
      X hX hBV x C hxc D hD ω hFinite w hw_cont hw_neg
      hActivity q T hT hSource'
  have hGood :=
    avram_bvb_b23_original_real_horizon_away_ruin_ae
      T hT (ruinTime X x D ω)
  dsimp only
  constructor
  · filter_upwards [hAe, hGood] with r ha hr
    have hcoe : (Real.toNNReal r : ℝ) = r :=
      Real.coe_toNNReal r hr.1.le
    have hstep :=
      avram_bvb_b24_original_A_floor_rate_eventually_eq_sample
        T hT C (ruinTime X x D ω) u huniform U ψ q
        r hr.1.le hr.2.1
    simpa [U, ψ, rate, hcoe, hr.1, hr.2.1] using
      (ha.1.congr' (by
        filter_upwards [hstep] with n hn
        simpa [U, ψ, rate, hcoe] using hn.symm))
  · filter_upwards [hAe, hGood] with r ha hr
    have hcoe : (Real.toNNReal r : ℝ) = r :=
      Real.coe_toNNReal r hr.1.le
    have htpos : 0 < Real.toNNReal r :=
      Real.toNNReal_pos.mpr hr.1
    simpa [U, ψ, rate, hcoe, hr.1, hr.2.1, htpos] using ha.2
