-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_original_grid_killed_kernel_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:16:16.707225+00:00
-- url     : https://prove2.me/submissions/70c1a0c3-b3c5-49ea-8d52-ea89ac0f825e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_survival_discounted_scale_expectation
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_killed_scale_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The actual original-P full-future-path law has the exact q-scale reward
normalisation, with the lower survival event detected by a countable grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (τ : ℕ → ℝ≥0) (t : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = t)
    (x : ℝ) :
    (∫⁻ y : ℝ≥0 → ℝ,
      (if ∀ j : ℕ, τ j ≤ t → 0 ≤ x + y (τ j)
        then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + y t))
        else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)) =
      ENNReal.ofReal (W x) := by
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω u => X.X u ω
  let S : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}
  let f : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun y =>
    if ∀ j : ℕ, τ j ≤ t → 0 ≤ x + y (τ j)
    then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + y t))
    else 0
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro u
    exact (X.adapted u).mono (𝓕.le u) le_rfl
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hf : Measurable f :=
    (chat04_countable_shifted_killed_scale_payoff_measurable
      τ t t q W hWm).comp (measurable_const.prodMk measurable_id)
  have hEvent (ω : Ω) :
      (∀ j : ℕ, τ j ≤ t → 0 ≤ x + X.X (τ j) ω) ↔
      ω ∈ S := by
    have hh := chat04_random_reserve_shifted_closed_survival_schedule_iff
      X (fun _ => x) ω 0 t τ hCover hTerminal
    simpa only [S, Set.mem_setOf_eq, zero_add, X.X_zero ω, sub_zero] using hh.symm
  change (∫⁻ y, f y ∂(Measure.map Z P)) = ENNReal.ofReal (W x)
  calc
    (∫⁻ y, f y ∂(Measure.map Z P)) =
        ∫⁻ ω, f (Z ω) ∂P := lintegral_map hf hZ
    _ = ∫⁻ ω, S.indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P := by
      apply lintegral_congr
      intro ω
      by_cases hw : ω ∈ S
      · have hgrid := (hEvent ω).mpr hw
        simp only [f, Z, S, Set.indicator_of_mem hw, if_pos hgrid]
      · have hgrid : ¬ (∀ j : ℕ, τ j ≤ t → 0 ≤ x + X.X (τ j) ω) :=
          fun hg => hw ((hEvent ω).mp hg)
        simp only [f, Z, S, Set.indicator_of_notMem hw, if_neg hgrid]
    _ = ENNReal.ofReal (W x) :=
      chat04_unbounded_killed_survival_discounted_scale_expectation
        X q hq W hW hnbv x t
