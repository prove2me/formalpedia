-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_pair_card_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:45:42.849192+00:00
-- url     : https://prove2.me/submissions/894eecc3-c515-427b-9306-f80ef310b884

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal BigOperators

/-- Disjoint physical future cells turn a chronological pair cover into a pair-count sum. -/
theorem solution
    (F : Finset ℝ≥0) (δ : ℝ≥0) (m : ℕ)
    (hcover :
      (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2) =
        (Finset.univ : Finset (Fin m)).biUnion (fun i =>
          (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
            p.1 ≤ (i.val : ℝ≥0) * δ ∧
            (i.val : ℝ≥0) * δ < p.2 ∧
            p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))))
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint
        (Ioc ((i.val : ℝ≥0) * δ) (((i.val + 1 : ℕ) : ℝ≥0) * δ))
        (Ioc ((j.val : ℝ≥0) * δ) (((j.val + 1 : ℕ) : ℝ≥0) * δ))) :
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
      ∑ i : Fin m,
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
          p.1 ≤ (i.val : ℝ≥0) * δ ∧
          (i.val : ℝ≥0) * δ < p.2 ∧
          p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))).card := by
  classical
  have hpw : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => (F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 ≤ (i.val : ℝ≥0) * δ ∧
        (i.val : ℝ≥0) * δ < p.2 ∧
        p.2 ≤ (((i.val + 1 : ℕ) : ℝ≥0) * δ))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hci := (Finset.mem_filter.mp hpi).2
    have hcj := (Finset.mem_filter.mp hpj).2
    exact (Set.disjoint_left.mp (hdisj i j hij))
      ⟨hci.2.1, hci.2.2⟩ ⟨hcj.2.1, hcj.2.2⟩
  rw [hcover]
  exact Finset.card_biUnion hpw
