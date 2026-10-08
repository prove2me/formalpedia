-- Prove2me | solution 1 for CHMSPricing.UnitDemand.menuMech_alloc_maxFeasDesiring
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:09:57.071772+00:00
-- url     : https://prove2.me/submissions/b83403f1-62ef-4454-876e-a720ea59f2fe

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech



namespace CHMSPricing.UnitDemand

section
variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

theorem mc_some {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    {j : J} (h : menuChoice 𝒥 owner p v A i = some j) :
    owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j := by
  unfold menuChoice at h
  split_ifs at h with hne
  · simp only [Option.some.injEq] at h
    have hmem := Finset.min'_mem _ (hne.image (Fintype.equivFin J))
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hmem
    have : j = a := by rw [← h, ← hae]; simp
    subst this
    unfold menuBest at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact ha.1

theorem mc_none {𝒥 : SetSystem J} {owner : J → Fin m} {p v : J → ℝ} {A : Finset J} {i : Fin m}
    (h : menuChoice 𝒥 owner p v A i = none) (j : J) (hj : owner j = i) (hp : p j ≤ v j) :
    ¬ 𝒥.Feasible (insert j A) := by
  intro hf
  unfold menuChoice at h
  split_ifs at h with hne
  apply hne
  classical
  unfold menuBest
  set C := Finset.univ.filter (fun j => owner j = i ∧ 𝒥.Feasible (insert j A) ∧ p j ≤ v j)
  have hC : C.Nonempty := ⟨j, by simp [C, hj, hf, hp]⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image C (fun j => v j - p j) hC
  refine ⟨a, ?_⟩
  simp only [Finset.mem_filter]
  refine ⟨ha, ?_⟩
  convert hmax

theorem step_sub (𝒥 : SetSystem J) (owner : J → Fin m) (p v : J → ℝ) (A : Finset J) (i : Fin m) :
    A ⊆ menuStep 𝒥 owner p v A i := by
  unfold menuStep
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem fold_sub (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (L : List (Fin m)) (A : Finset J) :
    A ⊆ L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A := by
  induction L generalizing A with
  | nil => exact le_rfl
  | cons k L ih =>
    simp only [List.foldl_cons]
    exact (step_sub _ _ _ _ _ _).trans (ih _)

theorem fold_inv (𝒥 : SetSystem J) (owner : J → Fin m) (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (L : List (Fin m)) (A : Finset J) (h1 : A ⊆ desiring p v) (h2 : 𝒥.Feasible A) :
    L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A ⊆ desiring p v ∧
    𝒥.Feasible (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A) := by
  induction L generalizing A with
  | nil => exact ⟨h1, h2⟩
  | cons k L ih =>
    simp only [List.foldl_cons]
    apply ih
    · unfold menuStep
      split
      · next j hj =>
        obtain ⟨_, _, hp⟩ := mc_some hj
        exact Finset.insert_subset (by simp [desiring, hp]) h1
      · exact h1
    · unfold menuStep
      split
      · next j hj => exact (mc_some hj).2.1
      · exact h2

theorem fold_max (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ)
    (L : List (Fin m)) (A : Finset J) (k : Fin m) (hk : k ∈ L) (i : J) (hi : i ∈ desiring p v)
    (hown : owner i = σ k)
    (hn : i ∉ L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A) :
    ¬ 𝒥.Feasible (insert i (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k)) A)) := by
  induction L generalizing A with
  | nil => simp at hk
  | cons k' L ih =>
    simp only [List.foldl_cons] at hn ⊢
    by_cases hkk : k = k'
    · subst hkk
      have hsub := fold_sub 𝒥 owner σ p v L (menuStep 𝒥 owner p v A (σ k))
      have hpi : p i ≤ v i := by simpa [desiring] using hi
      cases hc : menuChoice 𝒥 owner p v A (σ k) with
      | none =>
        have hnf := mc_none hc i hown hpi
        intro hf
        apply hnf
        refine 𝒥.feasible_mono ?_ hf
        apply Finset.insert_subset_insert
        refine le_trans ?_ hsub
        exact step_sub _ _ _ _ _ _
      | some j =>
        obtain ⟨hoj, _, _⟩ := mc_some hc
        have hjS : j ∈ menuStep 𝒥 owner p v A (σ k) := by
          unfold menuStep; rw [hc]; exact Finset.mem_insert_self _ _
        have hjR := hsub hjS
        have hij : i ≠ j := fun h => hn (h ▸ hjR)
        intro hf
        have := h𝒥 _ hf (σ k)
        have h2 : ({i, j} : Finset J) ⊆ (insert i (L.foldl (fun A k => menuStep 𝒥 owner p v A (σ k))
            (menuStep 𝒥 owner p v A (σ k)))).filter (fun j => owner j = σ k) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · simp [hown]
          · simp [hoj, hjR]
        have := (Finset.card_le_card h2).trans this
        rw [Finset.card_pair hij] at this
        omega
    · have hk' : k ∈ L := by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h hkk
        · exact h
      exact ih _ hk' hn

theorem mm_core {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ) :
    IsMaxFeasDesiring 𝒥 p v ((menuMech 𝒥 owner σ p).alloc v) := by
  have inv := fold_inv 𝒥 owner σ p v (List.finRange m) ∅ (Finset.empty_subset _) 𝒥.feasible_empty
  refine ⟨inv.1, inv.2, ?_⟩
  intro i hi hn
  exact fold_max 𝒥 owner h𝒥 σ p v (List.finRange m) ∅ (σ.symm (owner i)) (List.mem_finRange _)
    i hi (by simp) hn

end
end CHMSPricing.UnitDemand

open CHMSPricing.UnitDemand


theorem solution {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}
    (𝒥 : SetSystem J) (owner : J → Fin m) (h𝒥 : IsUnitDemand 𝒥 owner)
    (σ : Equiv.Perm (Fin m)) (p v : J → ℝ) :
    IsMaxFeasDesiring 𝒥 p v ((menuMech 𝒥 owner σ p).alloc v) := by
  exact mm_core 𝒥 owner h𝒥 σ p v
