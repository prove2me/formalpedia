-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB304_original_localized_fixed_level_hit_mesh_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:38:01.369694+00:00
-- url     : https://prove2.me/submissions/588ba21e-3407-4697-a48b-29ff8dd175ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB287_positive_mesh_open_cells_or_endpoints
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n M m : ℕ) (hm : 0 < m) :
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  let N : ℕ := n * m ^ 4
  let E : Set (Ω × ℝ) := {z | z.2 ∈ Set.range
    (fun i : Fin N => (i : ℝ) * δ)}
  let B : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    1 / ((m : ℝ) ^ 3) <
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  let G : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
        1 / ((m : ℝ) ^ 3) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b}
  let S : Set (Ω × ℝ) := {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  S ⊆ E ∪ (B ∪ G) := by
  let δ : ℝ := 1 / ((m : ℝ) ^ 4)
  let N : ℕ := n * m ^ 4
  let E : Set (Ω × ℝ) := {z | z.2 ∈ Set.range
    (fun i : Fin N => (i : ℝ) * δ)}
  let B : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    1 / ((m : ℝ) ^ 3) <
      D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  let G : Set (Ω × ℝ) := {z | ∃ i ∈ Finset.range N,
    z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
    D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
      D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
        1 / ((m : ℝ) ^ 3) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b}
  let S : Set (Ω × ℝ) := {z |
    0 < z.2 ∧ z.2 < (n : ℝ) ∧
    x + X.X (Real.toNNReal z.2) z.1 -
      rightLimit D (Real.toNNReal z.2) z.1 = b ∧
    D n z.1 - D 0 z.1 ≤ (M : ℝ)}
  change S ⊆ E ∪ (B ∪ G)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hT : (n : ℝ) = (N : ℝ) * δ := by
    dsimp [N, δ]
    push_cast
    field_simp
  intro z hz
  obtain ⟨ht0, htn, hhit, hloc⟩ := hz
  rcases avram_gbB287_positive_mesh_open_cells_or_endpoints
      N δ z.2 hδ (le_of_lt ht0) (by simpa only [← hT] using htn) with
    ⟨i, hi, hcell⟩ | hendpoint
  · by_cases hSmall :
        D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 -
        D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) z.1 ≤
          1 / ((m : ℝ) ^ 3)
    · right; right
      exact ⟨i, Finset.mem_range.mpr hi, hcell, hSmall, hhit⟩
    · right; left
      exact ⟨i, Finset.mem_range.mpr hi, hcell,
        lt_of_not_ge hSmall, hhit, hloc⟩
  · left
    exact hendpoint
