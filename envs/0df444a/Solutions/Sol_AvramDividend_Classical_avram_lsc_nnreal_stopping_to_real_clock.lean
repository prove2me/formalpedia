-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_nnreal_stopping_to_real_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T17:08:39.515325+00:00
-- url     : https://prove2.me/submissions/7c748271-2c56-4c6d-819c-4fecde5a8911

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transfer an Avram nonnegative-time stopping clock to the real-time Brownian filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (ℱr : Filtration ℝ mΩ)
    (hℱr : ∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    IsStoppingTime ℱr (fun ω => ((τ ω : ℝ) : WithTop ℝ)) := by
  intro t
  rw [hℱr t]
  by_cases ht : 0 ≤ t
  · have hset :
        {ω : Ω | ((τ ω : ℝ) : WithTop ℝ) ≤ t} =
          {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ Real.toNNReal t} := by
      ext ω
      simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
      change ((τ ω : ℝ) ≤ t) ↔ (τ ω ≤ Real.toNNReal t)
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht]
    rw [hset]
    exact hτ (Real.toNNReal t)
  · have hset : {ω : Ω | ((τ ω : ℝ) : WithTop ℝ) ≤ t} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        WithTop.coe_le_coe]
      exact not_le_of_gt
        (lt_of_lt_of_le (lt_of_not_ge ht) (NNReal.coe_nonneg (τ ω)))
    rw [hset]
    letI : MeasurableSpace Ω := 𝓕.rightCont (Real.toNNReal t)
    exact MeasurableSet.empty
