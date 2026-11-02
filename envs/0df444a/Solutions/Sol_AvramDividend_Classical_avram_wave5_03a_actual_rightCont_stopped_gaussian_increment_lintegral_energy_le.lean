-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:18:43.844197+00:00
-- url     : https://prove2.me/submissions/7d178509-865b-4871-b5dd-5a6f49c83a52

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_quotient_pointwise_drift_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-- Fatou gives the actual same-path stopped Gaussian increment's finite L2 energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) ∂P)
        ≤ ENNReal.ofReal ((h : ℝ) * X.σ ^ 2) := by
  classical
  let Δ : Ω → ℝ := fun ω => X.X (τ ω + h) ω - X.X (τ ω) ω
  let Y : Ω → ℝ := fun ω => Δ ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun θ ω =>
    (Real.exp (θ * Δ ω - (h : ℝ) * X.ψ θ) - 1) / θ
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  change (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) ≤
    ENNReal.ofReal ((h : ℝ) * X.σ ^ 2)
  have hε0 : Filter.Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    simpa only [ε] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεpos : ∀ n : ℕ, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε : Filter.Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hε0, Filter.Eventually.of_forall (fun n => Set.mem_Ioi.mpr (hεpos n))⟩
  have hsqrt0 : Filter.Tendsto (fun n => Real.sqrt (ε n))
      atTop (𝓝 (0 : ℝ)) := by
    have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hε0
    change Filter.Tendsto (fun n => Real.sqrt (ε n))
      atTop (𝓝 (Real.sqrt 0)) at ht
    simpa only [Real.sqrt_zero] using ht
  have hsqrt : Filter.Tendsto (fun n => Real.sqrt (ε n))
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hsqrt0, Filter.Eventually.of_forall
        (fun n => Set.mem_Ioi.mpr (Real.sqrt_pos.2 (hεpos n)))⟩
  have hZpt (ω : Ω) :
      Filter.Tendsto (fun n => Z (Real.sqrt (ε n)) ω)
        atTop (𝓝 (Y ω)) := by
    have ht :=
      (avram_wave5_03a_source_gaussian_stopped_exponential_quotient_pointwise_drift_limit
        X hν τ h ω).comp hsqrt
    change Filter.Tendsto (fun n => Z (Real.sqrt (ε n)) ω)
      atTop (𝓝 (Y ω)) at ht
    exact ht
  obtain ⟨Xrc, hpaths, hc, hsig, hmeasure⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hFuture : Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      Xrc.X (τ ω + t) ω - Xrc.X (τ ω) ω) :=
    levy_finiteStopping_stoppedFuturePath_measurable Xrc τ hτ
  rw [hpaths] at hFuture
  have hΔ : Measurable Δ := by
    dsimp [Δ]
    exact (measurable_pi_apply h).comp hFuture
  have hZm (θ : ℝ) : Measurable (Z θ) := by
    dsimp [Z]
    exact ((((measurable_const.mul hΔ).sub measurable_const).exp.sub
      measurable_const).div_const θ)
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal ((Z (Real.sqrt (ε n)) ω) ^ 2)
  have hFm (n : ℕ) : Measurable (F n) :=
    ((hZm (Real.sqrt (ε n))).pow_const 2).ennreal_ofReal
  have hFlim (ω : Ω) :
      Filter.Tendsto (fun n => F n ω) atTop
        (𝓝 (ENNReal.ofReal ((Y ω) ^ 2))) := by
    have hs : Filter.Tendsto (fun n => (Z (Real.sqrt (ε n)) ω) ^ 2)
        atTop (𝓝 ((Y ω) ^ 2)) := by
      have ht := ((continuous_id.pow 2).tendsto (Y ω)).comp (hZpt ω)
      change Filter.Tendsto (fun n => (Z (Real.sqrt (ε n)) ω) ^ 2)
        atTop (𝓝 ((Y ω) ^ 2)) at ht
      exact ht
    exact (ENNReal.continuous_ofReal.tendsto ((Y ω) ^ 2)).comp hs
  have hFatou := lintegral_liminf_le (μ := P) (u := atTop) (f := F) hFm
  have hLeft : (fun ω => Filter.liminf (fun n => F n ω) atTop) =
      (fun ω => ENNReal.ofReal ((Y ω) ^ 2)) := by
    funext ω
    exact (hFlim ω).liminf_eq
  rw [hLeft] at hFatou
  have hI (n : ℕ) :
      (∫⁻ ω, F n ω ∂P) =
        ENNReal.ofReal (∫ ω, (Z (Real.sqrt (ε n)) ω) ^ 2 ∂P) := by
    have hMem : MemLp (Z (Real.sqrt (ε n))) 2 P := by
      simpa only [Z, Δ] using
        (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
          X hν τ hτ T hbounded h (Real.sqrt (ε n))
          (Real.sqrt_nonneg _)).1
    have hSq : Integrable
        (fun ω => (Z (Real.sqrt (ε n)) ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq hMem.aestronglyMeasurable).mp hMem
    exact (ofReal_integral_eq_lintegral_ofReal hSq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).symm
  have hEnergy : Filter.Tendsto
      (fun n => (∫ ω, (Z (Real.sqrt (ε n)) ω) ^ 2 ∂P))
      atTop (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
    have ht :=
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
        X hν τ hτ T hbounded h).comp hε
    change Filter.Tendsto
      (fun n => (∫ ω, (Z (Real.sqrt (ε n)) ω) ^ 2 ∂P))
      atTop (𝓝 ((h : ℝ) * X.σ ^ 2)) at ht
    exact ht
  have hEnergyE : Filter.Tendsto
      (fun n => ENNReal.ofReal
        (∫ ω, (Z (Real.sqrt (ε n)) ω) ^ 2 ∂P))
      atTop (𝓝 (ENNReal.ofReal ((h : ℝ) * X.σ ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto ((h : ℝ) * X.σ ^ 2)).comp hEnergy
  have hRight : (fun n => (∫⁻ ω, F n ω ∂P)) =
      (fun n => ENNReal.ofReal
        (∫ ω, (Z (Real.sqrt (ε n)) ω) ^ 2 ∂P)) :=
    funext hI
  rw [hRight] at hFatou
  exact hFatou.trans_eq hEnergyE.liminf_eq
