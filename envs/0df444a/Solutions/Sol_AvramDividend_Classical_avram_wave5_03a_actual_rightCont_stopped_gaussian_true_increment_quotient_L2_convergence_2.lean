-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:57:09.309558+00:00
-- url     : https://prove2.me/submissions/253eadd9-5944-4624-9498-6f282555542e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ ξ) - 1) / ξ
  let a : ℝ := (h : ℝ) * X.σ ^ 2
  let excess : ℝ → ℝ := fun θ =>
    (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 - a
  let error : ℝ → ℝ≥0∞ := fun θ =>
    ∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P
  change Filter.Tendsto error (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
  have hSquare0 :
      Filter.Tendsto (fun θ : ℝ => θ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Filter.Tendsto (fun θ : ℝ => θ)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))).pow 2)
    simpa using ht
  have hSquare :
      Filter.Tendsto (fun θ : ℝ => θ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hSquare0, by
        filter_upwards [self_mem_nhdsWithin] with θ hθ
        exact Set.mem_Ioi.mpr (sq_pos_of_pos (Set.mem_Ioi.mp hθ))⟩
  have hReal : Filter.Tendsto excess
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := (avram_wave5_03a_exp_quadratic_secant_right_limit a 0).comp hSquare
    have ht' := ht.sub_const a
    convert ht' using 1
    · funext θ
      dsimp [excess, a]
      have harg : (h : ℝ) * (X.σ ^ 2 * θ ^ 2) =
          ((h : ℝ) * X.σ ^ 2) * θ ^ 2 := by ring
      rw [harg]
      simp only [zero_mul, add_zero, sub_zero]
    · simp
  have hENN : Filter.Tendsto
      (fun θ => ENNReal.ofReal (excess θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    have ht := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hReal
    change Filter.Tendsto (fun θ => ENNReal.ofReal (excess θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal 0)) at ht
    simpa only [ENNReal.ofReal_zero] using ht
  have hIfTop : Filter.Tendsto
      (fun θ : ℝ => if 0 < θ then ENNReal.ofReal (excess θ) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    apply hENN.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact (if_pos (Set.mem_Ioi.mp hθ)).symm
  have hLow :
      (fun _ : ℝ => (0 : ℝ≥0∞)) ≤
      (fun θ : ℝ => if 0 < θ then error θ else 0) := by
    intro θ
    change (0 : ℝ≥0∞) ≤ if 0 < θ then error θ else 0
    by_cases hθ : 0 < θ
    · rw [if_pos hθ]
      exact bot_le
    · rw [if_neg hθ]
  have hHigh :
      (fun θ : ℝ => if 0 < θ then error θ else 0) ≤
      (fun θ : ℝ => if 0 < θ then ENNReal.ofReal (excess θ) else 0) := by
    intro θ
    by_cases hθ : 0 < θ
    · simp only [if_pos hθ]
      exact
        (avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
          X hν τ hτ T hbounded h θ hθ)
    · simp only [if_neg hθ, le_refl]
  have hSqueezed : Filter.Tendsto
      (fun θ : ℝ => if 0 < θ then error θ else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hIfTop hLow hHigh
  apply hSqueezed.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  exact if_pos (Set.mem_Ioi.mp hθ)
