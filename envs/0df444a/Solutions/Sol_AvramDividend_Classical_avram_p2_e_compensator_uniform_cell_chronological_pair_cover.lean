-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_cell_chronological_pair_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:59:56.713423+00:00
-- url     : https://prove2.me/submissions/cabc2b55-b2dc-4fd6-a386-37eb847d5b1a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_cell_ordered_pair_fibre

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal BigOperators

/-- All chronological physical finite-set pairs are covered by source grid crossing fibres. -/
theorem solution
    (F : Finset ℝ≥0) (δ : ℝ≥0) (m : ℕ) (idx : ℝ≥0 → ℕ)
    (hidx : ∀ u ∈ F, idx u < m)
    (hcell : ∀ u ∈ F,
      (idx u : ℝ≥0) * δ < u ∧
      u ≤ (((idx u + 1 : ℕ) : ℝ≥0) * δ))
    (hinj : Set.InjOn idx (F : Set ℝ≥0)) :
    (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2) =
      (Finset.univ : Finset (Fin m)).biUnion (fun i =>
        (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
          p.1 ≤ (i.val : ℝ≥0) * δ ∧
          (i.val : ℝ≥0) * δ < p.2 ∧
          p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hprod, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hprod
    have hcross := avram_p2_e_compensator_uniform_cell_ordered_pair_fibre
      F δ idx hcell hinj p.1 hu p.2 hv hlt
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨idx p.2, hidx p.2 hv⟩, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hprod, hcross⟩
  · intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprod, hcross⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr
      ⟨hprod, lt_of_le_of_lt hcross.1 hcross.2.1⟩
