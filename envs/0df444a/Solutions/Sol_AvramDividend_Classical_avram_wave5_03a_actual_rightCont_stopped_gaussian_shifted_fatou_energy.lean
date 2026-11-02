-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:06:54.880098+00:00
-- url     : https://prove2.me/submissions/20031d39-d815-407f-84db-6673c7a9c38f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_quotient_pointwise_drift_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (a : ℝ) :
    (∫⁻ ω, ENNReal.ofReal
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c + a) ^ 2) ∂P)
        ≤ ENNReal.ofReal ((h : ℝ) * X.σ ^ 2 + a ^ 2) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Δ : Ω → ℝ := fun ω => X.X (τ ω + h) ω - X.X (τ ω) ω
  let Y : Ω → ℝ := fun ω => Δ ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun θ ω =>
    (Real.exp (θ * Δ ω - (h : ℝ) * X.ψ θ) - 1) / θ
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  change (∫⁻ ω, ENNReal.ofReal ((Y ω + a) ^ 2) ∂P) ≤
    ENNReal.ofReal ((h : ℝ) * X.σ ^ 2 + a ^ 2)
  have hε0 : Filter.Tendsto ε atTop (𝓝 (0 : ℝ)) := by simpa only [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεpos : ∀ n : ℕ, 0 < ε n := by intro n; dsimp [ε]; positivity
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
  have hΔ : Measurable Δ := by dsimp [Δ]; exact (measurable_pi_apply h).comp hFuture
  have hZm (θ : ℝ) : Measurable (Z θ) := by dsimp [Z]; exact ((((measurable_const.mul hΔ).sub measurable_const).exp.sub
      measurable_const).div_const θ)
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal ((Z (Real.sqrt (ε n)) ω + a) ^ 2)
  have hFm (n : ℕ) : Measurable (F n) :=
    (((hZm (Real.sqrt (ε n))).add_const a).pow_const 2).ennreal_ofReal
  have hFlim (ω : Ω) :
      Filter.Tendsto (fun n => F n ω) atTop
        (𝓝 (ENNReal.ofReal ((Y ω + a) ^ 2))) := by
    have hs : Filter.Tendsto (fun n => (Z (Real.sqrt (ε n)) ω + a) ^ 2)
        atTop (𝓝 ((Y ω + a) ^ 2)) := by
      have hc : Filter.Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
      have ht := ((hZpt ω).add hc).pow 2
      change Filter.Tendsto (fun n => (Z (Real.sqrt (ε n)) ω + a) ^ 2)
        atTop (𝓝 ((Y ω + a) ^ 2)) at ht
      exact ht
    exact (ENNReal.continuous_ofReal.tendsto ((Y ω + a) ^ 2)).comp hs
  have hFatou := lintegral_liminf_le (μ := P) (u := atTop) (f := F) hFm
  have hLeft : (fun ω => Filter.liminf (fun n => F n ω) atTop) =
      (fun ω => ENNReal.ofReal ((Y ω + a) ^ 2)) := by
    funext ω; exact (hFlim ω).liminf_eq
  rw [hLeft] at hFatou
  have hIexpand (n : ℕ) :
      (∫ ω, (Z (Real.sqrt (ε n)) ω + a) ^ 2 ∂P) =
        (∫ ω, (Z (Real.sqrt (ε n)) ω) ^ 2 ∂P) + a ^ 2 := by
    let θ := Real.sqrt (ε n)
    have hMem : MemLp (Z θ) 2 P := by simpa only [Z, Δ, θ] using (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h θ (Real.sqrt_nonneg _)).1
    have hSq : Integrable (fun ω => (Z θ ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq hMem.aestronglyMeasurable).mp hMem
    have hZi : Integrable (Z θ) P := hMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hMean : (∫ ω, Z θ ω ∂P) = 0 := by simpa only [Z, Δ, θ] using (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h θ (Real.sqrt_nonneg _)).2
    have hp : ∀ ω, (Z θ ω + a) ^ 2 =
        (Z θ ω) ^ 2 + (2 * a) * Z θ ω + a ^ 2 := by intro ω; ring
    calc
      (∫ ω, (Z θ ω + a) ^ 2 ∂P) =
          ∫ ω, ((Z θ ω) ^ 2 + ((2 * a) * Z θ ω + a ^ 2)) ∂P := by
            congr 1
            funext ω; rw [hp ω]; ring
      _ = (∫ ω, (Z θ ω) ^ 2 ∂P) +
          (∫ ω, ((2 * a) * Z θ ω + a ^ 2) ∂P) :=
            integral_add hSq ((hZi.const_mul (2 * a)).add (integrable_const (a ^ 2)))
      _ = (∫ ω, (Z θ ω) ^ 2 ∂P) + a ^ 2 := by
            rw [integral_add (hZi.const_mul (2 * a)) (integrable_const (a ^ 2))]
            rw [integral_const_mul, hMean]
            simp
  have hI (n : ℕ) :
      (∫⁻ ω, F n ω ∂P) =
        ENNReal.ofReal (∫ ω, (Z (Real.sqrt (ε n)) ω + a) ^ 2 ∂P) := by
    let θ := Real.sqrt (ε n)
    have hMem : MemLp (Z θ) 2 P := by simpa only [Z, Δ, θ] using (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
        X hν τ hτ T hbounded h θ (Real.sqrt_nonneg _)).1
    have hSq : Integrable (fun ω => (Z θ ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq hMem.aestronglyMeasurable).mp hMem
    have hZi : Integrable (Z θ) P := hMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hSqShift : Integrable (fun ω => (Z θ ω + a) ^ 2) P := by
      have heq : (fun ω => (Z θ ω + a) ^ 2) =
          (fun ω => (Z θ ω) ^ 2 + (2 * a) * Z θ ω + a ^ 2) := by
        funext ω; ring
      rw [heq]
      exact (hSq.add (hZi.const_mul (2 * a))).add (integrable_const (a ^ 2))
    exact (ofReal_integral_eq_lintegral_ofReal hSqShift
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))).symm
  have hEnergy : Filter.Tendsto
      (fun n => (∫ ω, (Z (Real.sqrt (ε n)) ω + a) ^ 2 ∂P))
      atTop (𝓝 ((h : ℝ) * X.σ ^ 2 + a ^ 2)) := by
    have ht :=
      (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
        X hν τ hτ T hbounded h).comp hε
    have ht2 := ht.add_const (a ^ 2)
    convert ht2 using 1
    funext n; exact hIexpand n
  have hEnergyE : Filter.Tendsto
      (fun n => ENNReal.ofReal
        (∫ ω, (Z (Real.sqrt (ε n)) ω + a) ^ 2 ∂P))
      atTop (𝓝 (ENNReal.ofReal ((h : ℝ) * X.σ ^ 2 + a ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto ((h : ℝ) * X.σ ^ 2 + a ^ 2)).comp hEnergy
  have hRight : (fun n => (∫⁻ ω, F n ω ∂P)) =
      (fun n => ENNReal.ofReal (∫ ω, (Z (Real.sqrt (ε n)) ω + a) ^ 2 ∂P)) := funext hI
  rw [hRight] at hFatou
  exact hFatou.trans_eq hEnergyE.liminf_eq
