-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_original_path_killed_scale_scalar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:12:59.83798+00:00
-- url     : https://prove2.me/submissions/8a2916b6-287b-4064-81c1-c7b51e137aa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_deterministic_killed_qscale_no_root
import Theorems.Thm_AvramDividend_Classical_chat04_standing_history_killed_scale_real_ennreal_integral_bridge
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The source BV killed semigroup fixes the scale reward in the law
of the entire genuine Lévy path, with exact rational-cover survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∫⁻ y : ℝ≥0 → ℝ,
      if ∀ j : ℕ, τ j ≤ T → 0 ≤ x + y (τ j) then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + y T))
      else (0 : ℝ≥0∞)
      ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
    ENNReal.ofReal (W x) := by
  classical
  let path : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let f : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun y =>
    if ∀ j : ℕ, τ j ≤ T → 0 ≤ x + y (τ j) then
      ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + y T))
    else 0
  have hSet : MeasurableSet {y : ℝ≥0 → ℝ |
      ∀ j : ℕ, τ j ≤ T → 0 ≤ x + y (τ j)} := by
    have h := chat04_countable_shifted_future_reserve_survival_measurable τ T
    simpa only [preimage, mem_setOf_eq, id_eq] using
      (h.preimage (measurable_const.prodMk measurable_id))
  have hWmeas : Measurable W :=
    (scaleFunction_monotone X q W hW).measurable
  have hf : Measurable f := by
    dsimp [f]
    exact Measurable.ite hSet
      (ENNReal.measurable_ofReal.comp
        (measurable_const.mul
          (hWmeas.comp (measurable_const.add (measurable_pi_apply T)))))
      measurable_const
  have hReindex (ω : Ω) :
      (∀ j : ℕ, τ j ≤ T → 0 ≤ x + X.X (τ j) ω) ↔
      (∀ v : ℝ≥0, v ≤ T → 0 ≤ x + X.X v ω) := by
    have h := chat04_random_reserve_shifted_closed_survival_schedule_iff
      X (fun _ : Ω => x) ω 0 T τ hCover hTerminal
    simpa only [zero_add, X.X_zero, sub_zero] using h.symm
  have hBridge := chat04_standing_history_killed_scale_real_ennreal_integral_bridge
    X hX q hq W hW x T
  have hFixed := avram_ws01b_bv_deterministic_killed_qscale_no_root
    X hX q hq W hW hBV x T
  calc
    _ = ∫⁻ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ T → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))
      else (0 : ℝ≥0∞)) ∂P := by
        change (∫⁻ y, f y ∂(Measure.map path P)) = _
        rw [lintegral_map hf (levy_wholePath_measurable X)]
        exact lintegral_congr fun ω => by
          dsimp only [f, path]
          rw [hReindex ω]
    _ = ENNReal.ofReal
      (∫ ω, ({z : Ω | ∀ v : ℝ≥0, v ≤ T → 0 ≤ x + X.X v z}).indicator
        (fun z => Real.exp (-(q * (T : ℝ))) * W (x + X.X T z)) ω ∂P) := by
        simpa only [Set.indicator, Set.mem_setOf_eq] using hBridge
    _ = ENNReal.ofReal (W x) := congrArg ENNReal.ofReal hFixed
