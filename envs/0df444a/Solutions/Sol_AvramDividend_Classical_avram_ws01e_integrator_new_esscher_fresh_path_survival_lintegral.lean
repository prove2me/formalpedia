-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_esscher_fresh_path_survival_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:36:03.109985+00:00
-- url     : https://prove2.me/submissions/a5bcc43e-2038-4914-8bde-9ea102b37ad9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Pull a genuine non-ruin Esscher reward back from the original full-path law,
including the real-to-ENNReal integral bridge, at one fixed future horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫⁻ y : ℝ≥0 → ℝ,
      (if ∀ j : ℕ, τ j ≤ u → 0 ≤ z + y (τ j) then
        ENNReal.ofReal (Real.exp
          (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
    ENNReal.ofReal (∫ ω,
      ({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ω}).indicator
        (fun ω => Real.exp
          (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by
  classical
  let A : Set (ℝ≥0 → ℝ) :=
    {y | ∀ j : ℕ, τ j ≤ u → 0 ≤ z + y (τ j)}
  let B : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ω}
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let V : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun y =>
    A.indicator (fun y => ENNReal.ofReal (Real.exp
      (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) y
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hPair : Measurable (fun y : ℝ≥0 → ℝ => (z, y)) :=
    measurable_const.prodMk measurable_id
  have hA : MeasurableSet A := by
    change MeasurableSet {y : ℝ≥0 → ℝ |
      ∀ j : ℕ, τ j ≤ u → 0 ≤ z + y (τ j)}
    simpa only [preimage, mem_setOf_eq] using
      (chat04_countable_shifted_future_reserve_survival_measurable τ u).preimage hPair
  have hReward : Measurable
      (fun y : ℝ≥0 → ℝ => ENNReal.ofReal (Real.exp
        (θ * y u - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (measurable_pi_apply u)).sub measurable_const))
  have hV : Measurable V := hReward.indicator hA
  have hEvent (ω : Ω) : (Y ω ∈ A) ↔ ω ∈ B := by
    have hs := chat04_random_reserve_shifted_closed_survival_schedule_iff
      X (fun _ : Ω => z) ω 0 u τ hCover hTerminal
    simpa [A, B, Y, X.X_zero] using hs.symm
  have hB : MeasurableSet B := by
    have hPre : MeasurableSet (Y ⁻¹' A) := hA.preimage hY
    convert hPre using 1
    ext ω
    exact (hEvent ω).symm
  have hInt : Integrable
      (B.indicator (fun ω => Real.exp
        (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ))) P :=
    (esscher_exp_process_integrable X θ hθ u).indicator hB
  have hNonneg : ∀ ω : Ω, 0 ≤
      B.indicator (fun ω => Real.exp
        (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω := by
    intro ω
    by_cases hw : ω ∈ B
    · rw [Set.indicator_of_mem hw]
      exact (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hw]
  change (∫⁻ y, V y ∂(Measure.map Y P)) =
    ENNReal.ofReal (∫ ω,
      B.indicator (fun ω => Real.exp
        (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
  rw [lintegral_map hV hY]
  calc
    (∫⁻ ω, V (Y ω) ∂P) =
        ∫⁻ ω, ENNReal.ofReal
          (B.indicator (fun ω => Real.exp
            (θ * X.X u ω - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω) ∂P := by
      apply lintegral_congr
      intro ω
      by_cases hw : ω ∈ B
      · have hwa : Y ω ∈ A := (hEvent ω).mpr hw
        simp [V, Y, hwa, Set.indicator_of_mem hw, Set.indicator_of_mem hwa]
      · have hwa : Y ω ∉ A := fun h => hw ((hEvent ω).mp h)
        simp [V, hwa, Set.indicator_of_notMem hw, Set.indicator_of_notMem hwa]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall hNonneg)).symm
