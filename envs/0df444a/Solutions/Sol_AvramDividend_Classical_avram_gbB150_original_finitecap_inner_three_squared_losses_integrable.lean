-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB150_original_finitecap_inner_three_squared_losses_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:40:08.79267+00:00
-- url     : https://prove2.me/submissions/2b72fbd0-1c65-44f2-8549-c374f71d5b21

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gbB152_original_finitecap_K_joint_measurable_direct
import Theorems.Thm_AvramDividend_Classical_avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB145_original_finitecap_step_K_bound_from_generic_clipped_gradient
import Theorems.Thm_AvramDividend_Classical_avram_gbB147_original_real_time_H_fixed_t_exponential_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
      let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℝ := x + X.X s ω - rightLimit D s ω
        if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y ∈ Icc a b then deriv w Y else 1)
        else 0
      let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        (Finset.range (m + 1)).sum (fun i =>
          if (s i : ℝ) ≤ t ∧ t < ((s i + Δ : ℝ≥0) : ℝ)
          then G m i ω else 0)
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
      ∀ (m p : ℕ) (t : ℝ),
        Integrable (fun ω => (K m t ω - K p t ω) ^ 2) P ∧
        Integrable (fun ω => (K m t ω - H t ω) ^ 2) P ∧
        Integrable (fun ω => (H t ω - K p t ω) ^ 2) P := by
  intro G K a b H m p t
  letI : IsProbabilityMeasure P := X.isProbability
  have hmK : ∀ r, Measurable (fun z : ℝ × Ω => K r z.1 z.2) :=
    avram_gbB152_original_finitecap_K_joint_measurable_direct
      X q hq w C hC hFiniteCap hw_smooth x D hD
      n hn ρ hρstop δ hδ j
  have hmH : Measurable (fun z : ℝ × Ω => H z.1 z.2) :=
    avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
      X q hq w C hC hFiniteCap hw_smooth x D hD ρ hρstop δ hδ j
  rcases avram_gbB145_original_finitecap_step_K_bound_from_generic_clipped_gradient
      X q hq w C hC hFiniteCap hw_smooth x D n ρ δ hδ j
    with ⟨BK, hBK, hKB⟩
  rcases avram_gbB147_original_real_time_H_fixed_t_exponential_bound
      X q hq w C hC hFiniteCap hw_smooth x D ρ δ hδ j
    with ⟨BH, hBH, hHB⟩
  let Bk : ℕ → ℝ := fun r => (r + 1 : ℕ) * BK
  let Bh : ℝ → ℝ := fun s =>
    Real.exp (-(q * (s - (Real.toNNReal s : ℝ)))) * BH
  have hBk : ∀ r, 0 ≤ Bk r := by
    intro r
    exact mul_nonneg (by positivity) hBK
  have hBh : ∀ s, 0 ≤ Bh s := by
    intro s
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) hBH
  have hk : ∀ r s ω, |K r s ω| ≤ Bk r := hKB
  have hh : ∀ s ω, |H s ω| ≤ Bh s := hHB
  constructor
  · exact avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
      P (fun z : ℝ × Ω => K m z.1 z.2) (fun z => K p z.1 z.2)
      (hmK m) (hmK p) (fun _ => Bk m) (fun _ => Bk p)
      (fun _ => hBk m) (fun _ => hBk p)
      (fun s ω => hk m s ω) (fun s ω => hk p s ω) t
  constructor
  · exact avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
      P (fun z : ℝ × Ω => K m z.1 z.2) (fun z => H z.1 z.2)
      (hmK m) hmH (fun _ => Bk m) Bh
      (fun _ => hBk m) hBh
      (fun s ω => hk m s ω) hh t
  · exact avram_gbB148_measurable_fibre_squared_loss_integrable_with_time_bounds
      P (fun z : ℝ × Ω => H z.1 z.2) (fun z => K p z.1 z.2)
      hmH (hmK p) Bh (fun _ => Bk p)
      hBh (fun _ => hBk p)
      hh (fun s ω => hk p s ω) t
