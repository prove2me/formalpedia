-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB116_original_finitecap_one_mesh_gradient_L2_to_physical_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:26:23.058458+00:00
-- url     : https://prove2.me/submissions/0771bda4-eda7-439e-be28-c2ff37f1a75f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gbB102_original_finitecap_step_coefficient_ae_time_convergence
import Theorems.Thm_AvramDividend_Classical_avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB147_original_real_time_H_fixed_t_exponential_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB152_original_finitecap_K_joint_measurable_direct
import Theorems.Thm_AvramDividend_Classical_avram_gbB154_original_finitecap_step_K_uniform_bound_inside_horizon
import Theorems.Thm_AvramDividend_Classical_avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
          then G i ω else 0)
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let H : ℝ → Ω → ℝ := fun t ω =>
        if Real.toNNReal t < ρ ω then
          Real.exp (-(q * t)) *
            (if x + X.X (Real.toNNReal t) ω -
                  rightLimit D (Real.toNNReal t) ω ∈ Icc a b
             then deriv w (x + X.X (Real.toNNReal t) ω -
                  rightLimit D (Real.toNNReal t) ω)
             else 1)
        else 0
      Tendsto (fun m : ℕ =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K m t ω - H t ω) ^ 2 ∂P) ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  intro k ρ hρstop hρle δ hδ hFloor A hA j K a b H
  letI : IsProbabilityMeasure P := X.isProbability
  rcases avram_gbB154_original_finitecap_step_K_uniform_bound_inside_horizon
    X q hq w C hC hFiniteCap hw_smooth x D n ρ δ hδ j
    with ⟨BK, hBK, hKb⟩
  rcases avram_gbB147_original_real_time_H_fixed_t_exponential_bound
    X q hq w C hC hFiniteCap hw_smooth x D ρ δ hδ j
    with ⟨BH, hBH, hHb⟩
  have hKm : ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2) :=
    avram_gbB152_original_finitecap_K_joint_measurable_direct
      X q hq w C hC hFiniteCap hw_smooth x D hD
      n hn ρ hρstop δ hδ j
  have hHm : Measurable (fun z : ℝ × Ω => H z.1 z.2) :=
    avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
      X q hq w C hC hFiniteCap hw_smooth x D hD
      ρ hρstop δ hδ j
  have hHi : ∀ t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) → |H t ω| ≤ BH := by
    intro t ω ht
    have ht0 : 0 ≤ t := le_of_lt ht.1
    have htc : (Real.toNNReal t : ℝ) = t := Real.coe_toNNReal t ht0
    have hb := hHb t ω
    simpa only [htc, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul]
      using hb
  have hAE := avram_gbB102_original_finitecap_step_coefficient_ae_time_convergence
    X hX hBV hν q hq w C hC hFiniteCap hw_smooth
    x D hD n hn ρ hρstop δ hδ hFloor j
  exact avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
    P n hn K H hKm hHm BK BH hBK hBH hKb hHi
    (by simpa only [K, H] using hAE)
