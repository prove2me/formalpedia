-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_survival_closed_window_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:01:54.608989+00:00
-- url     : https://prove2.me/submissions/4c238ca1-1475-4a68-a24b-a0953d7414b7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_strict_lower_exit_closed_window_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! A future closed-window no-ruin event is Borel-measurable by exact
countable-grid detection and terminal-time observation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    MeasurableSet
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < lower} := by
  let g (n k : ℕ) : ℝ≥0 :=
    (k : ℝ≥0) * (n : ℝ≥0)⁻¹
  let E : Set Ω :=
    {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u → ¬ X.X v ω < lower}
  have hEq :
      E = {ω | ¬ X.X u ω < lower} ∩
        ⋂ n : ℕ, ⋂ k : ℕ,
          {ω | (0 < n ∧ s ≤ g n k ∧ g n k < u) →
            ¬ X.X (g n k) ω < lower} := by
    ext ω
    simp only [E, mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      refine ⟨h u hsu le_rfl, ?_⟩
      intro n k hnk
      exact h (g n k) hnk.2.1 (le_of_lt hnk.2.2)
    · rintro ⟨hterm, hgrid⟩ v hsv hvu hbad
      rcases
          (chat04_strict_lower_exit_closed_window_grid_iff
            X ω lower s u hsu).mp ⟨v, hsv, hvu, hbad⟩ with
        hu | ⟨n, hn, k, hsk, hku, hkbad⟩
      · exact hterm hu
      · have hnk : 0 < n ∧ s ≤ g n k ∧ g n k < u := by
          exact ⟨hn, hsk, hku⟩
        exact (hgrid n k hnk) hkbad
  change MeasurableSet E
  rw [hEq]
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hterm : MeasurableSet {ω : Ω | ¬ X.X u ω < lower} :=
    (measurableSet_lt hXu measurable_const).compl
  apply hterm.inter
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro k
  by_cases hnk : 0 < n ∧ s ≤ g n k ∧ g n k < u
  · have hXg : Measurable (X.X (g n k)) :=
      (X.adapted (g n k)).mono (𝓕.le (g n k)) le_rfl
    have hsafe : MeasurableSet
        {ω : Ω | ¬ X.X (g n k) ω < lower} :=
      (measurableSet_lt hXg measurable_const).compl
    simpa [hnk] using hsafe
  · simpa [hnk] using
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
