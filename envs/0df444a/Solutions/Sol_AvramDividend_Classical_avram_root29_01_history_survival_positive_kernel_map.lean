-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_history_survival_positive_kernel_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:22:25.737018+00:00
-- url     : https://prove2.me/submissions/9a386abd-794f-4ecc-84c0-b3361ebcade2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_history_survival_pair_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Lift a positive monotone future-reserve kernel through the exact
original-P history reserve/survival pair, retaining all threshold atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (s : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (F : ℝ → ℝ) (hF : Monotone F) :
    (∫⁻ h : ℝ × Bool,
      (if h.2 then
        ENNReal.ofReal (Real.exp
          (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (F (x + h.1))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) P)) =
    (∫⁻ ω : Ω,
      (if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp
          (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
        ENNReal.ofReal (F (x + X.X s ω))
       else (0 : ℝ≥0∞)) ∂P) := by
  classical
  let H : Ω → ℝ × Bool := fun ω =>
    (X.X s ω, decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))
  let G : ℝ × Bool → ℝ≥0∞ := fun h =>
    if h.2 then
      ENNReal.ofReal (Real.exp
        (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
      ENNReal.ofReal (F (x + h.1))
    else 0
  have hHm : Measurable H := by
    exact (avram_ws01e_integrator_new_history_survival_pair_measurable
      X x s τ hCover).mono (𝓕.le s) le_rfl
  have hFm : Measurable F := hF.measurable
  have hA : Measurable (fun h : ℝ × Bool =>
      ENNReal.ofReal (Real.exp
        (θ * h.1 - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_fst).sub measurable_const))
  have hB : Measurable (fun h : ℝ × Bool =>
      ENNReal.ofReal (F (x + h.1))) :=
    ENNReal.measurable_ofReal.comp
      (hFm.comp (measurable_const.add measurable_fst))
  have hFlag : MeasurableSet {h : ℝ × Bool | h.2 = true} :=
    (measurableSet_singleton true).preimage measurable_snd
  have hGm : Measurable G := Measurable.ite hFlag (hA.mul hB) measurable_const
  change (∫⁻ h : ℝ × Bool, G h ∂(Measure.map H P)) =
    ∫⁻ ω : Ω, (if ∀ v : ℝ≥0, v ≤ s →
      0 ≤ x + X.X v ω then
      ENNReal.ofReal (Real.exp
        (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)) *
      ENNReal.ofReal (F (x + X.X s ω))
    else 0) ∂P
  rw [lintegral_map hGm hHm]
  apply lintegral_congr
  intro ω
  by_cases hp : ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω
  · simp [H, G, hp]
  · simp [H, G, hp]
