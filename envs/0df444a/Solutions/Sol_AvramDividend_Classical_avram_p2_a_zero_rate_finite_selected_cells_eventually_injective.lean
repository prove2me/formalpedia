-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_finite_selected_cells_eventually_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:38:26.678749+00:00
-- url     : https://prove2.me/submissions/c4b403a6-3c1e-45a2-ae92-53606e6c956d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-- Finitely many pairwise eventually distinct selected cells become injective
simultaneously at one sufficiently fine original-grid resolution. -/
theorem solution
    {α : Type*} (s : Finset α) (i : α → ℕ → ℕ)
    (h : ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      ∀ᶠ n : ℕ in atTop, i u n ≠ i v n) :
    ∀ᶠ n : ℕ in atTop, Set.InjOn (fun u => i u n) (s : Set α) := by
  classical
  have hfin : ∀ q : Finset (α × α), q ⊆ s.product s →
      ∀ᶠ n : ℕ in atTop, ∀ p ∈ q,
        p.1 ≠ p.2 → i p.1 n ≠ i p.2 n := by
    intro q
    induction q using Finset.induction_on with
    | empty =>
        intro hsub
        exact Filter.Eventually.of_forall (by simp)
    | @insert p q hp ih =>
        intro hsub
        have hp_mem : p ∈ s.product s :=
          hsub (Finset.mem_insert_self p q)
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp_mem
        have hqsub : q ⊆ s.product s := by
          intro z hz
          exact hsub (Finset.mem_insert_of_mem hz)
        have hpair : ∀ᶠ n : ℕ in atTop,
            p.1 ≠ p.2 → i p.1 n ≠ i p.2 n := by
          by_cases hne : p.1 ≠ p.2
          · filter_upwards [h p.1 hp1 p.2 hp2 hne] with n hn
            exact fun _ => hn
          · exact Filter.Eventually.of_forall (fun _ hne' => (hne hne').elim)
        filter_upwards [hpair, ih hqsub] with n hp_event hq_event z hz hne
        rcases Finset.mem_insert.mp hz with rfl | hzq
        · exact hp_event hne
        · exact hq_event z hzq hne
  filter_upwards [hfin (s.product s) (by intro p hp; exact hp)] with n hn u hu v hv heq
  by_contra huv
  exact (hn (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩) huv) heq
