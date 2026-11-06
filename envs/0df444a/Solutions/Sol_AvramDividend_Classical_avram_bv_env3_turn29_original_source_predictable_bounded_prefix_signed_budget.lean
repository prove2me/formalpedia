-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:20:42.461737+00:00
-- url     : https://prove2.me/submissions/806c783f-3521-49b8-a134-a7747141cd0c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original-process martingale increments and nonpositive signed drift admit a predictable bounded random stopping-prefix budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (k : Ω → ℕ) (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hPredictable : ∀ i, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < k ω})
    (B : ℕ → Ω → ℝ) (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω) ∂P) ≤ 0 := by
  have hMI (i : ℕ) :
      Integrable (fun ω => Y (u (i + 1)) ω - Y (u i) ω) P :=
    (hMart.integrable (u (i + 1))).sub (hMart.integrable (u i))
  have hCondZero (i : ℕ) :
      P[(fun ω => Y (u (i + 1)) ω - Y (u i) ω) | 𝓕.rightCont (u i)]
        =ᵐ[P] (fun _ => (0 : ℝ)) :=
    avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
      X Y hMart u hu i
  exact avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
    X u m k hk hkBound
    (fun i ω => Y (u (i + 1)) ω - Y (u i) ω)
    B hMI hBI hPredictable hCondZero hDrift
