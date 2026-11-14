-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB292_localized_hit_open_good_bad_boundary_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:12:59.982502+00:00
-- url     : https://prove2.me/submissions/0ce77921-6f65-4327-b912-0f6f19f374f8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB287_positive_mesh_open_cells_or_endpoints
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Finset AvramDividend.Classical
noncomputable section

/-- Every localised level hit on a finite mesh is in a good cell, bad cell, or on a boundary. -/
theorem solution
    {Ω : Type*} (R : Ω → ℝ → ℝ) (d : Ω → ℕ → ℝ) (b : ℝ)
    (N : ℕ) (δ ε T M : ℝ) (hδ : 0 < δ)
    (hT : T = (N : ℝ) * δ) :
    {z : Ω × ℝ | 0 < z.2 ∧ z.2 < T ∧
      R z.1 z.2 = b ∧ d z.1 N - d z.1 0 ≤ M} ⊆
    {z : Ω × ℝ | z.2 ∈ Set.range (fun i : Fin N => (i : ℝ) * δ)} ∪
      ({z : Ω × ℝ | ∃ i : ℕ, i < N ∧
        z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
        ε < d z.1 (i + 1) - d z.1 i ∧
        R z.1 z.2 = b ∧ d z.1 N - d z.1 0 ≤ M} ∪
      ⋃ i ∈ Finset.range N, {z : Ω × ℝ |
        z.2 ∈ Set.Ioo ((i : ℝ) * δ) (((i : ℝ) + 1) * δ) ∧
        d z.1 (i + 1) - d z.1 i ≤ ε ∧
        R z.1 z.2 = b ∧ d z.1 N - d z.1 0 ≤ M}) := by
  intro z hz
  obtain ⟨hpos, hbound, hhit, hloc⟩ := hz
  have hhorizon : z.2 < (N : ℝ) * δ := by
    calc
      z.2 < T := hbound
      _ = (N : ℝ) * δ := hT
  rcases avram_gbB287_positive_mesh_open_cells_or_endpoints
      N δ z.2 hδ (le_of_lt hpos) hhorizon with
    ⟨i, hi, hcell⟩ | hend
  · by_cases hgood : d z.1 (i + 1) - d z.1 i ≤ ε
    · right
      right
      exact Set.mem_iUnion.mpr
        ⟨i, Set.mem_iUnion.mpr
          ⟨Finset.mem_range.mpr hi, ⟨hcell, hgood, hhit, hloc⟩⟩⟩
    · right
      left
      exact ⟨i, hi, hcell, lt_of_not_ge hgood, hhit, hloc⟩
  · left
    exact hend
