-- Prove2me | solution 1 for AvramDividend.Classical.avram_b117_generic_finite_marked_cells_one_cutoff_captures_all
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T20:51:34.677072+00:00
-- url     : https://prove2.me/submissions/70484145-b78f-4d35-8b26-8bbbc720aebc

import Mathlib.Data.Finset.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
noncomputable section

/-- A finite family of physically marked cells, each captured by a monotone cutoff eventually, is captured by one common cutoff. -/
theorem solution
    {ι : Type*} (S : Finset ι)
    (C : ℕ → ι → Prop)
    (hMono : ∀ i n m, n ≤ m → C n i → C m i)
    (hCover : ∀ i ∈ S, ∃ n : ℕ, C n i) :
    ∃ n : ℕ, ∀ i ∈ S, C n i := by
  classical
  have hAux : ∀ T : Finset ι,
      (∀ i ∈ T, ∃ n : ℕ, C n i) →
      ∃ n : ℕ, ∀ i ∈ T, C n i := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨0, by simp⟩
    | @insert a T ha ih =>
        intro hT
        have hTa : ∃ n : ℕ, C n a := hT a (by simp)
        have hTsmall : ∀ i ∈ T, ∃ n : ℕ, C n i := by
          intro i hi
          exact hT i (Finset.mem_insert_of_mem hi)
        obtain ⟨n, hn⟩ := ih hTsmall
        obtain ⟨m, hm⟩ := hTa
        refine ⟨max n m, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact hMono i m (max n m) (le_max_right _ _) hm
        · exact hMono i n (max n m) (le_max_left _ _) (hn i hi')
  exact hAux S hCover
