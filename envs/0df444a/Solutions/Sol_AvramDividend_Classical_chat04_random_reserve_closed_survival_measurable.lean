-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_closed_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:01:25.266182+00:00
-- url     : https://prove2.me/submissions/cbd3a8f3-4a42-4169-9892-77a7a9ce2200

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | ∀ t : ℝ≥0, t ≤ T → 0 ≤ H ω + X.X t ω} := by
  have hXm : ∀ t, Measurable (X.X t) := fun t => (X.adapted t).mono (𝓕.le t) le_rfl
  have e : {ω : Ω | ∀ t : ℝ≥0, t ≤ T → 0 ≤ H ω + X.X t ω} =
      (⋂ n : ℕ, ⋂ k : ℕ, {ω : Ω | 0 < n → (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ H ω + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω}) ∩ {ω : Ω | 0 ≤ H ω + X.X T ω} := by
    ext ω
    rw [Set.mem_setOf_eq, AvramDividend.Classical.chat04_random_reserve_lower_survival_closed_grid_iff X H ω T]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun n k hn hk => h1 n hn k hk, h2⟩, fun ⟨h1, h2⟩ => ⟨fun n hn k hk => h1 n k hn hk, h2⟩⟩
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_)
    (measurableSet_le measurable_const (hH.add (hXm T)))
  by_cases hn : 0 < n
  · by_cases hk : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T
    · simp only [hn, hk, true_implies]
      exact measurableSet_le measurable_const (hH.add (hXm _))
    · simp [hk]
  · simp [hn]
