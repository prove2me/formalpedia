-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_original_chronological_pair_ncard_eq_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:16:30.516408+00:00
-- url     : https://prove2.me/submissions/1a7c39ba-02f9-4724-80cf-96336b5401f9

import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Set.Card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
noncomputable section

theorem solution
    (S : Set ℝ≥0) (hS : S.Finite) :
    ((S ×ˢ S) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard =
    ((hS.toFinset ×ˢ hS.toFinset).filter
      (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  classical
  let F : Finset ℝ≥0 := hS.toFinset
  have hEq :
      (S ×ˢ S) ∩ {p : ℝ≥0 × ℝ≥0 | p.1 < p.2} =
        (↑((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2))
          : Set (ℝ≥0 × ℝ≥0)) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨ha, hb⟩, hp⟩
      exact ⟨⟨(hS.mem_toFinset).mpr ha,
        (hS.mem_toFinset).mpr hb⟩, hp⟩
    · rintro ⟨⟨ha, hb⟩, hp⟩
      exact ⟨⟨(hS.mem_toFinset).mp ha,
        (hS.mem_toFinset).mp hb⟩, hp⟩
  rw [hEq]
  exact Set.ncard_coe_finset _
