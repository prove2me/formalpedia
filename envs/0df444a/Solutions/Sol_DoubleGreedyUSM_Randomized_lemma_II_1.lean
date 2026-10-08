-- Prove2me | solution 1 for DoubleGreedyUSM.Randomized.lemma_II_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:30:55.359984+00:00
-- url     : https://prove2.me/submissions/87b93a62-0327-4027-afa5-45db1988a8ff

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

set_option autoImplicit false

namespace DoubleGreedyUSM.Randomized.P1d3977aa

open DoubleGreedyUSM.Randomized

theorem state_succ {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (l : List X) (i : ℕ) (h : i < l.length) :
    state f l (i + 1) = advance f (state f l i) (l[i]) := by
  unfold state
  rw [← List.take_concat_get' l i h, List.foldl_append]
  rfl

theorem inv {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (l : List X) (hl : l.Nodup) :
    ∀ i, i ≤ l.length → ∀ s : Finset X × Finset X, state f l i s ≠ 0 →
      s.1 ⊆ s.2 ∧ ∀ x ∈ l.drop i, x ∈ s.2 ∧ x ∉ s.1 := by
  intro i
  induction i with
  | zero =>
    intro _ s hs
    have : s = (∅, Finset.univ) := by
      by_contra hne
      apply hs
      simp [state, hne]
    subst this
    simp
  | succ i ih =>
    intro hi t ht
    have hi' : i < l.length := by omega
    rw [state_succ f l i hi'] at ht
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    have hμ : state f l i s ≠ 0 := left_ne_zero_of_mul hs
    have hn : nextMass f s (l[i]) t ≠ 0 := right_ne_zero_of_mul hs
    obtain ⟨hsub, hall⟩ := ih (by omega) s hμ
    have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi'
    have hnd : (l.drop i).Nodup := hl.sublist (List.drop_sublist _ _)
    rw [hdrop, List.nodup_cons] at hnd
    have hu := hall (l[i]) (by rw [hdrop]; exact List.mem_cons_self)
    have hrest : ∀ x ∈ l.drop (i + 1), x ∈ s.2 ∧ x ∉ s.1 ∧ x ≠ l[i] := by
      intro x hx
      have := hall x (by rw [hdrop]; exact List.mem_cons_of_mem _ hx)
      refine ⟨this.1, this.2, ?_⟩
      rintro rfl
      exact hnd.1 hx
    unfold nextMass at hn
    by_cases h1 : t = (insert (l[i]) s.1, s.2)
    · subst h1
      refine ⟨?_, ?_⟩
      · exact Finset.insert_subset hu.1 hsub
      · intro x hx
        obtain ⟨a, b, c⟩ := hrest x hx
        refine ⟨a, ?_⟩
        simp only [Finset.mem_insert, not_or]
        exact ⟨c, b⟩
    · by_cases h2 : t = (s.1, s.2.erase (l[i]))
      · subst h2
        refine ⟨?_, ?_⟩
        · intro y hy
          exact Finset.mem_erase.2 ⟨fun h => hu.2 (h ▸ hy), hsub hy⟩
        · intro x hx
          obtain ⟨a, b, c⟩ := hrest x hx
          exact ⟨Finset.mem_erase.2 ⟨c, a⟩, b⟩
      · exfalso
        apply hn
        simp [h1, h2]

end DoubleGreedyUSM.Randomized.P1d3977aa

open DoubleGreedyUSM.Randomized in
/-- Lemma II.1 (PDF p. 3), applied to each reachable state of Algorithm 2. -/
theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l) :
    ∀ i (hi : 1 ≤ i) (hin : i ≤ l.length) (s : Finset X × Finset X),
      DoubleGreedyUSM.Randomized.state f l (i - 1) s ≠ 0 →
      0 ≤ (f (insert (l[i - 1]'(by omega)) s.1) - f s.1) +
        (f (s.2.erase (l[i - 1]'(by omega))) - f s.2) := by
  intro i hi hin s hs
  have hlt : i - 1 < l.length := by omega
  obtain ⟨hsub, hall⟩ := DoubleGreedyUSM.Randomized.P1d3977aa.inv f l hl (i - 1) (by omega) s hs
  have hu := hall (l[i - 1]'(by omega))
    (by rw [List.drop_eq_getElem_cons hlt]; exact List.mem_cons_self)
  set u := l[i - 1]'(by omega) with hu_def
  have key := hf (insert u s.1) (s.2.erase u)
  have hU : insert u s.1 ∪ s.2.erase u = s.2 := by
    ext y
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((rfl | h) | ⟨_, h⟩)
      · exact hu.1
      · exact hsub h
      · exact h
    · intro hy
      by_cases hyu : y = u
      · exact Or.inl (Or.inl hyu)
      · exact Or.inr ⟨hyu, hy⟩
  have hI : insert u s.1 ∩ s.2.erase u = s.1 := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | h, hne, _⟩
      · exact absurd rfl hne
      · exact h
    · intro hy
      refine ⟨Or.inr hy, ?_, hsub hy⟩
      rintro rfl
      exact hu.2 hy
  rw [hU, hI] at key
  linarith
