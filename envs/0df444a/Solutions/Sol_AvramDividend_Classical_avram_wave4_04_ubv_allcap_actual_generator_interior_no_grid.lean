-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_allcap_actual_generator_interior_no_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:43:42.39302+00:00
-- url     : https://prove2.me/submissions/11b197d4-ecb4-44ea-9d7f-4de0861401f8

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_all_cap_actual_admissible_generator_interior_sigma_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
The physical-time source generator is applicable on the true controlled
strict interior almost everywhere, uniformly for any predetermined s-finite
time measure and any nonzero finite or infinite cap. Dense/cofinal
observation schedules are constructed internally, not demanded of users.
-/

private theorem denseCofinalSchedules :
    ∃ (times horizons : ℕ → ℝ≥0),
      (∀ a b : ℝ≥0, a < b →
        ∃ m : ℕ, a < times m ∧ times m < b) ∧
      (∀ n : ℕ, 0 < horizons n) ∧
      (∀ ε : ℝ≥0, 0 < ε →
        ∃ n : ℕ, horizons n ≤ ε) := by
  obtain ⟨times, hDense⟩ :=
    TopologicalSpace.exists_dense_seq ℝ≥0
  let horizons : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  refine ⟨times, horizons, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨z, ⟨n, hn⟩, hz⟩ := Dense.exists_between hDense hab
    refine ⟨n, ?_, ?_⟩
    · simpa only [← hn] using hz.1
    · simpa only [← hn] using hz.2
  · intro n
    dsimp [horizons]
    positivity
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, le_of_lt hn⟩

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C := by
  obtain ⟨times, horizons, hdense, hpos, hcofinal⟩ :=
    denseCofinalSchedules
  exact avram_wave4_04_ubv_all_cap_actual_admissible_generator_interior_sigma_finite
    X hBV x C hC0 D hD hxc times horizons hdense hpos hcofinal μ
