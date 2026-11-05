-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:38:35.339015+00:00
-- url     : https://prove2.me/submissions/0eeefdd2-3227-4a3b-86a4-e11b6c37af12

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual source Lévy measure is sigma-finite if it has zero mass
at zero and finite mass outside every reciprocal neighbourhood of zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hZero : X.ν ({0} : Set ℝ) = 0)
    (hAway : ∀ n : ℕ,
      X.ν {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|} < ⊤) :
    SFinite X.ν := by
  let S : ℕ → Set ℝ := fun n =>
    {0} ∪ {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|}
  have hFinite (n : ℕ) : X.ν (S n) < ⊤ := by
    change X.ν ({0} ∪ {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|}) < ⊤
    calc
      _ ≤ X.ν ({0} : Set ℝ) +
          X.ν {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|} :=
        measure_union_le _ _
      _ = X.ν {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|} := by
        simp [hZero]
      _ < ⊤ := hAway n
  have hCover : ⋃₀ (Set.range S) = (Set.univ : Set ℝ) := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      by_cases hz : z = 0
      · have hz0 : z ∈ S 0 := by
          simp only [S, Set.mem_union, Set.mem_singleton_iff]
          exact Or.inl hz
        exact Set.mem_sUnion.mpr ⟨S 0, ⟨0, rfl⟩, hz0⟩
      · obtain ⟨n, hn⟩ :=
          exists_nat_one_div_lt (abs_pos.mpr hz)
        have hzn : z ∈ S n := by
          simp only [S, Set.mem_union, Set.mem_singleton_iff]
          exact Or.inr (le_of_lt hn)
        exact Set.mem_sUnion.mpr ⟨S n, ⟨n, rfl⟩, hzn⟩
  have hSigma : SigmaFinite X.ν := by
    apply Measure.sigmaFinite_of_countable (Set.countable_range S)
    · rintro s ⟨n, rfl⟩
      exact hFinite n
    · exact hCover
  letI : SigmaFinite X.ν := hSigma
  infer_instance
