-- Prove2me | solution 1 for BudgetedPCTSP.Rooted.laminar_sPlus
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:47:40.061987+00:00
-- url     : https://prove2.me/submissions/196a475c-8b77-4fe8-8782-24a555ee229a

import Mathlib
import Definitions.Def_BudgetedPCTSP_Rooted_Instance
import Definitions.Def_BudgetedPCTSP_Rooted_PDStep

open BudgetedPCTSP.Rooted

variable {V : Type} [Fintype V] [DecidableEq V]

private def LaminarInv (s : PDState V) : Prop :=
  (∀ C₁ ∈ s.comps, ∀ C₂ ∈ s.comps, C₁ ≠ C₂ → Disjoint C₁ C₂) ∧
  (∀ A ∈ s.everActive, ∀ B ∈ s.everActive, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) ∧
  (∀ A ∈ s.everActive, ∃ C ∈ s.comps, A ⊆ C)

private lemma laminarInv_init : LaminarInv (PDState.init : PDState V) := by
  have hsingle : ∀ C₁ ∈ (Finset.univ : Finset V).image (fun i => ({i} : Finset V)),
      ∀ C₂ ∈ (Finset.univ : Finset V).image (fun i => ({i} : Finset V)),
      C₁ ≠ C₂ → Disjoint C₁ C₂ := by
    intro C₁ hC₁ C₂ hC₂ hne
    rcases Finset.mem_image.mp hC₁ with ⟨i₁, _, rfl⟩
    rcases Finset.mem_image.mp hC₂ with ⟨i₂, _, rfl⟩
    have hi : i₁ ≠ i₂ := fun h => hne (by rw [h])
    exact Finset.disjoint_singleton.mpr hi
  refine ⟨hsingle, ?_, ?_⟩
  · intro A hA B hB
    by_cases hAB : A = B
    · exact Or.inl (by rw [hAB])
    · exact Or.inr (Or.inr (hsingle A hA B hB hAB))
  · intro A hA
    exact ⟨A, hA, Finset.Subset.rfl⟩

private lemma laminarInv_step {I : Instance V} {lam : ℝ} {s s' : PDState V}
    (h : LaminarInv s) (hstep : PDStep I lam s s') : LaminarInv s' := by
  rcases h with ⟨hdisj, hlam, hsub⟩
  cases hstep with
  | neutral Δ S _ _ _ =>
    exact ⟨hdisj, hlam, hsub⟩
  | edge Δ S₁ S₂ u v _ he _ =>
    have hS₁ : S₁ ∈ s.comps := he.2.1
    have hS₂ : S₂ ∈ s.comps := he.2.2.1
    set U := S₁ ∪ S₂
    set R := (s.comps.erase S₁).erase S₂
    have hR_sub : ∀ C ∈ R, C ∈ s.comps ∧ C ≠ S₁ ∧ C ≠ S₂ := by
      intro C hC
      rw [Finset.mem_erase, Finset.mem_erase] at hC
      exact ⟨hC.2.2, hC.2.1, hC.1⟩
    have hR_disj_U : ∀ C ∈ R, Disjoint C U := by
      intro C hC
      rcases hR_sub C hC with ⟨hC_in, hC1, hC2⟩
      exact Finset.disjoint_union_right.mpr
        ⟨hdisj C hC_in S₁ hS₁ hC1, hdisj C hC_in S₂ hS₂ hC2⟩
    have hA_U : ∀ A ∈ s.everActive, A ⊆ U ∨ Disjoint A U := by
      intro A hA
      rcases hsub A hA with ⟨C, hC, hAC⟩
      by_cases hC1 : C = S₁
      · subst hC1
        exact Or.inl (Finset.Subset.trans hAC Finset.subset_union_left)
      · by_cases hC2 : C = S₂
        · subst hC2
          exact Or.inl (Finset.Subset.trans hAC Finset.subset_union_right)
        · have hCR : C ∈ R := Finset.mem_erase.mpr ⟨hC2, Finset.mem_erase.mpr ⟨hC1, hC⟩⟩
          exact Or.inr (Finset.disjoint_of_subset_left hAC (hR_disj_U C hCR))
    refine ⟨?_, ?_, ?_⟩
    · intro C₁ hC₁ C₂ hC₂ hne
      rcases Finset.mem_insert.mp hC₁ with rfl | hC₁R <;>
        rcases Finset.mem_insert.mp hC₂ with rfl | hC₂R
      · exact (hne rfl).elim
      · exact (hR_disj_U C₂ hC₂R).symm
      · exact hR_disj_U C₁ hC₁R
      · exact hdisj C₁ (hR_sub C₁ hC₁R).1 C₂ (hR_sub C₂ hC₂R).1 hne
    · intro A hA B hB
      rcases Finset.mem_insert.mp hA with rfl | hA_old <;>
        rcases Finset.mem_insert.mp hB with rfl | hB_old
      · exact Or.inl Finset.Subset.rfl
      · rcases hA_U B hB_old with hBU | hdisjBU
        · exact Or.inr (Or.inl hBU)
        · exact Or.inr (Or.inr hdisjBU.symm)
      · rcases hA_U A hA_old with hAU | hdisjAU
        · exact Or.inl hAU
        · exact Or.inr (Or.inr hdisjAU)
      · exact hlam A hA_old B hB_old
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA_old
      · exact ⟨U, Finset.mem_insert_self U R, Finset.Subset.rfl⟩
      · rcases hsub A hA_old with ⟨C, hC, hAC⟩
        by_cases hC1 : C = S₁
        · subst hC1
          exact ⟨U, Finset.mem_insert_self U R, Finset.Subset.trans hAC Finset.subset_union_left⟩
        · by_cases hC2 : C = S₂
          · subst hC2
            exact ⟨U, Finset.mem_insert_self U R, Finset.Subset.trans hAC Finset.subset_union_right⟩
          · have hCR : C ∈ R := Finset.mem_erase.mpr ⟨hC2, Finset.mem_erase.mpr ⟨hC1, hC⟩⟩
            exact ⟨C, Finset.mem_insert_of_mem hCR, hAC⟩

private lemma laminarInv_of_reachable {I : Instance V} {lam : ℝ} {s : PDState V}
    (hs : IsReachable I lam s) : LaminarInv s := by
  induction hs with
  | refl => exact laminarInv_init
  | tail _ hstep ih => exact laminarInv_step ih hstep

theorem solution {V : Type} [Fintype V] [DecidableEq V] (I : Instance V) (lam : ℝ)
    (_hlam : 0 ≤ lam) (s : PDState V) (hs : IsCompleteRun I lam s) :
    ∀ A ∈ sPlus s, ∀ B ∈ sPlus s, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  have hlam := (laminarInv_of_reachable hs.1).2.1
  intro A hA B hB
  rcases Finset.mem_insert.mp hA with rfl | hA_in <;>
    rcases Finset.mem_insert.mp hB with rfl | hB_in
  · exact Or.inl (Finset.subset_univ _)
  · exact Or.inr (Or.inl (Finset.subset_univ _))
  · exact Or.inl (Finset.subset_univ _)
  · exact hlam A hA_in B hB_in
