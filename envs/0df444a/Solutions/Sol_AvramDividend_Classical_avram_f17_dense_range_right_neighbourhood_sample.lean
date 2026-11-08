-- Prove2me | solution 1 for AvramDividend.Classical.avram_f17_dense_range_right_neighbourhood_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:55:48.091604+00:00
-- url     : https://prove2.me/submissions/ae2408ec-6e01-4989-b5b1-329c32bbe0a5

import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Bases
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (s t : ℝ≥0) (hst : s < t)
    (U : Set ℝ≥0) (hU : U ∈ 𝓝[Set.Ici s] s) :
    ∃ k, r k < t ∧ r k ∈ U := by
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hst).mp hU
  obtain ⟨v, hsv, hvu⟩ := exists_between hu.1
  have hopen : IsOpen (Set.Ioo s u) := isOpen_Ioo
  have hnonempty : (Set.Ioo s u).Nonempty := ⟨v, ⟨hsv, hvu⟩⟩
  obtain ⟨k, hk⟩ := hdense.exists_mem_open hopen hnonempty
  refine ⟨k, lt_of_lt_of_le hk.2 hu.2, ?_⟩
  exact hsub ⟨le_of_lt hk.1, hk.2⟩
