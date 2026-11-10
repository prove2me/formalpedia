-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite26_original_cofinal_strict_reward_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T03:25:54.851063+00:00
-- url     : https://prove2.me/submissions/875da6b7-60cc-4c77-b11d-74ebffdbaa3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : Ω → ℝ≥0) (hσle : ∀ ω, σ ω ≤ τ ω)
    (ρ : ℕ → Ω → ℝ≥0)
    (hρle : ∀ j ω, ρ j ω ≤ σ ω)
    (hρmono : ∀ ω, Monotone (fun j : ℕ => ρ j ω))
    (hρlim : ∀ᵐ ω ∂P, Tendsto (fun j => ρ j ω) atTop (nhds (σ ω))) :
    let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω => if ζ ω = 0 then w x else Real.exp (-(q * (ζ ω : ℝ))) * w (riskProcess X x D (ζ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal (H (ρ j) ω)) atTop (nhds (ENNReal.ofReal (H σ ω))) := by
  classical
  let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω => if ζ ω = 0 then w x else Real.exp (-(q * (ζ ω : ℝ))) * w (riskProcess X x D (ζ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  change ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal (H (ρ j) ω)) atTop (nhds (ENNReal.ofReal (H σ ω)))
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hNuZero, hρlim] with ω hXcont hLim
  by_cases hTzero : σ ω = 0
  · have hfun : (fun j => ENNReal.ofReal (H (ρ j) ω)) =
        (fun _ => ENNReal.ofReal (H σ ω)) := by
      funext j
      have hj : ρ j ω = 0 := le_antisymm (by simpa [hTzero] using hρle j ω) zero_le
      simp [H, hTzero, hj]
    rw [hfun]
    exact tendsto_const_nhds
  have hTpos : 0 < σ ω := pos_iff_ne_zero.mpr hTzero
  by_cases heq : ∃ j, ρ j ω = σ ω
  · obtain ⟨j₀, hj₀⟩ := heq
    have hevent : (fun j => ENNReal.ofReal (H (ρ j) ω)) =ᶠ[atTop] (fun _ => ENNReal.ofReal (H σ ω)) := by
      filter_upwards [eventually_ge_atTop j₀] with j hj
      have hval : ρ j ω = σ ω :=
        le_antisymm (hρle j ω) (by simpa [hj₀] using hρmono ω hj)
      simp [H, hval]
    exact tendsto_const_nhds.congr' hevent.symm
  ·
    have hlt (j : ℕ) : ρ j ω < σ ω :=
      lt_of_le_of_ne (hρle j ω) (fun h => heq ⟨j, h⟩)
    have hτR : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
      have hh := (avram_wave7_08_source_truncated_clock_nnreal_bounds
        X x D n).2.2 ω
      rw [hτeq ω]
      exact hh
    have hσR : (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
      calc
        (σ ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by exact_mod_cast hσle ω
        _ ≤ _ := hτR
    have hPreruin (j : ℕ) : (ρ j ω : ℝ≥0∞) < ruinTime X x D ω := by
      calc
        (ρ j ω : ℝ≥0∞) < (σ ω : ℝ≥0∞) := by exact_mod_cast hlt j
        _ ≤ _ := hσR
    have hYnn (j : ℕ) : 0 ≤ riskProcess X x D (ρ j ω) ω := riskProcess_nonnegative_strictly_before_ruin
        X x D ω (ρ j ω) (hPreruin j)
    have hDleft : ContinuousWithinAt (fun t : ℝ≥0 => D t ω)
        (Iic (σ ω)) (σ ω) := hD.1.1.2.2.1 ω (σ ω)
    have hXleft : ContinuousWithinAt (fun t : ℝ≥0 => X.X t ω) (Iic (σ ω)) (σ ω) :=
      hXcont.continuousAt.continuousWithinAt
    have hYleft : ContinuousWithinAt
        (fun t : ℝ≥0 => riskProcess X x D t ω) (Iic (σ ω)) (σ ω) := by
      change ContinuousWithinAt (fun t : ℝ≥0 => x + X.X t ω - D t ω)
        (Iic (σ ω)) (σ ω)
      exact (continuousWithinAt_const.add hXleft).sub hDleft
    have hClockWithin : Tendsto (fun j => ρ j ω) atTop
        (𝓝[Iic (σ ω)] (σ ω)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hLim, Filter.Eventually.of_forall (fun j => hρle j ω)⟩
    have hYlim : Tendsto
        (fun j => riskProcess X x D (ρ j ω) ω) atTop (𝓝 (riskProcess X x D (σ ω) ω)) :=
      hYleft.tendsto.comp hClockWithin
    have hYat : riskProcess X x D (σ ω) ω ∈ Ici (0 : ℝ) :=
      isClosed_Ici.mem_of_tendsto hYlim
        (Filter.Eventually.of_forall hYnn)
    have hYwithin : Tendsto (fun j => riskProcess X x D (ρ j ω) ω) atTop
        (𝓝[Ici (0 : ℝ)] (riskProcess X x D (σ ω) ω)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hYlim, Filter.Eventually.of_forall hYnn⟩
    have hWlim : Tendsto (fun j => w (riskProcess X x D (ρ j ω) ω)) atTop
        (𝓝 (w (riskProcess X x D (σ ω) ω))) :=
      (hw_cont.continuousWithinAt hYat).tendsto.comp hYwithin
    have hExpCont : Continuous
        (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ)))) := by fun_prop
    have hExpLim := (hExpCont.tendsto (σ ω)).comp hLim
    have hTermLim := hExpLim.mul hWlim
    have hReal : Tendsto (fun j => (ρ j ω : ℝ)) atTop
        (𝓝 (σ ω : ℝ)) :=
      (NNReal.continuous_coe.tendsto (σ ω)).comp hLim
    have hMonoR : Monotone (fun j => (ρ j ω : ℝ)) := by
      intro i j hij
      exact_mod_cast hρmono ω hij
    have hBelowR (j : ℕ) : (ρ j ω : ℝ) ≤ (σ ω : ℝ) := by
      exact_mod_cast hρle j ω
    have hCover (s : ℝ) (hs : s < (σ ω : ℝ)) :
        ∃ j, s < (ρ j ω : ℝ) :=
      (hReal.eventually (Ioi_mem_nhds hs)).exists
    have hCash := avram_gclose17_original_strict_cash_real_monotone_cofinal_clock X x C D hD ω q (le_of_lt hq) (σ ω : ℝ) (by exact_mod_cast hTpos) (fun j => (ρ j ω : ℝ)) hMonoR hBelowR hCover
    have hPositive : ∀ᶠ j in atTop, ρ j ω ≠ 0 :=
      (hLim.eventually (Ioi_mem_nhds hTpos)).mono
        (fun j hj => ne_of_gt hj)
    have hEvent : (fun j => H (ρ j) ω) =ᶠ[atTop]
        (fun j =>
          Real.exp (-(q * (ρ j ω : ℝ))) * w (riskProcess X x D (ρ j ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ j ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) := by
      filter_upwards [hPositive] with j hj
      simp [H, hj]
    have hFull := hTermLim.add hCash
    have hH : Tendsto (fun j => H (ρ j) ω) atTop
        (𝓝 (H σ ω)) := by
      have hσEq : H σ ω =
          Real.exp (-(q * (σ ω : ℝ))) *
            w (riskProcess X x D (σ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by simp [H, ne_of_gt hTpos]
      rw [hσEq]
      exact hFull.congr' hEvent.symm
    exact (ENNReal.continuous_ofReal.tendsto (H σ ω)).comp hH