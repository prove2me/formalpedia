-- Prove2me | solution 1 for CompDesignBFM.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:48:47.336095+00:00
-- url     : https://prove2.me/submissions/8fec6deb-1639-47e0-afdb-559f83a7ce39

import Mathlib
import Definitions.Def_CompDesignBFM_closure
import Definitions.Def_CompDesignBFM_IsXOS
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_BudgetClock_Subadditive_Setting

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv0 : v ∅ = 0) (hv : ∀ S, 0 ≤ v S) :
    (BudgetClock.Subadditive.IsSubadditive v →
      CompDesignBFM.closure v ∅ = 0 ∧ IsMonotoneSF (CompDesignBFM.closure v) ∧
        BudgetClock.Subadditive.IsSubadditive (CompDesignBFM.closure v)) ∧
    (IsXOS v → CompDesignBFM.closure v ∅ = 0 ∧ IsMonotoneSF (CompDesignBFM.closure v) ∧
      IsXOS (CompDesignBFM.closure v)) := by
  classical
  have hcl0 : CompDesignBFM.closure v ∅ = 0 := by
    unfold CompDesignBFM.closure
    simp [hv0]
  have hmono : IsMonotoneSF (CompDesignBFM.closure v) := by
    intro S T hST
    unfold CompDesignBFM.closure
    apply Finset.sup'_le
    intro U hU
    exact Finset.le_sup' v (Finset.mem_powerset.2
      (le_trans (Finset.mem_powerset.1 hU) hST))
  have hle : ∀ T S : Finset (Fin n), T ⊆ S → v T ≤ CompDesignBFM.closure v S := by
    intro T S hTS
    unfold CompDesignBFM.closure
    exact Finset.le_sup' v (Finset.mem_powerset.2 hTS)
  refine ⟨fun hsub => ⟨hcl0, hmono, ?_⟩, fun hx => ⟨hcl0, hmono, ?_⟩⟩
  · intro S T
    obtain ⟨U, hUmem, hUeq⟩ := Finset.exists_mem_eq_sup'
      (⟨∅, Finset.empty_mem_powerset (S ∪ T)⟩ : (S ∪ T).powerset.Nonempty) v
    have hU : U ⊆ S ∪ T := Finset.mem_powerset.1 hUmem
    have hclU : CompDesignBFM.closure v (S ∪ T) = v U := by
      unfold CompDesignBFM.closure; exact hUeq
    have hsplit : U = (U ∩ S) ∪ (U ∩ T) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.1 (hU hx) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h) <;> exact h.1
    rw [hclU]
    calc v U = v ((U ∩ S) ∪ (U ∩ T)) := by rw [← hsplit]
      _ ≤ v (U ∩ S) + v (U ∩ T) := hsub _ _
      _ ≤ _ := add_le_add (hle _ _ Finset.inter_subset_right) (hle _ _ Finset.inter_subset_right)
  · obtain ⟨I, hI⟩ := hx
    refine ⟨I.image (fun a j => max (a j) 0), fun S => ?_⟩
    -- positive part facts
    have hup : ∀ a ∈ I, ∑ i ∈ S, max (a i) 0 ≤ CompDesignBFM.closure v S := by
      intro a haI
      set Tp : Finset (Fin n) := S.filter (fun i => 0 < a i) with hT
      have h1 : ∑ i ∈ S, max (a i) 0 = ∑ i ∈ Tp, a i := by
        rw [hT, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : 0 < a i
        · simp [h, le_of_lt h]
        · simp [h, not_lt.1 h]
      have h2 : ∑ i ∈ Tp, a i ≤ v Tp := (hI Tp).2 ⟨a, haI, rfl⟩
      rw [h1]
      exact le_trans h2 (hle _ _ (Finset.filter_subset _ _))
    refine ⟨?_, ?_⟩
    · -- membership
      obtain ⟨T, hTmem, hTeq⟩ := Finset.exists_mem_eq_sup'
        (⟨∅, Finset.empty_mem_powerset S⟩ : S.powerset.Nonempty) v
      have hTS : T ⊆ S := Finset.mem_powerset.1 hTmem
      have hclT : CompDesignBFM.closure v S = v T := by
        unfold CompDesignBFM.closure; exact hTeq
      obtain ⟨⟨a, haI, ha⟩, _⟩ := hI T
      have ha' : ∑ i ∈ T, a i = v T := ha
      refine ⟨fun j => max (a j) 0, Finset.mem_image.2 ⟨a, haI, rfl⟩, ?_⟩
      show ∑ i ∈ S, max (a i) 0 = CompDesignBFM.closure v S
      apply le_antisymm (hup a haI)
      rw [hclT, ← ha']
      calc ∑ i ∈ T, a i ≤ ∑ i ∈ T, max (a i) 0 := Finset.sum_le_sum fun i _ => le_max_left _ _
        _ ≤ ∑ i ∈ S, max (a i) 0 :=
          Finset.sum_le_sum_of_subset_of_nonneg hTS (fun i _ _ => le_max_right _ _)
    · rintro _ ⟨a', ha', rfl⟩
      obtain ⟨a, haI, rfl⟩ := Finset.mem_image.1 ha'
      exact hup a haI
