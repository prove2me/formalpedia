-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.card_filter_union_subset_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:53.589907+00:00
-- url     : https://prove2.me/submissions/6f084060-ba24-4e7b-ab18-3b7f619587e0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section SubsetSum
variable {α : Type*} [DecidableEq α]
/-- Counting supersets: for `d`-subsets `F, F'` of a set `U` with `3d` elements, the number of
`2d`-subsets of `U` containing `F ∪ F'` is `C(d + |F ∩ F'|, d)`. -/
theorem solution (U : Finset α) {d : ℕ} (hU : U.card = 3 * d) {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card =
      (d + (F ∩ F').card).choose d := by
    classical
    have hFsub : F ⊆ U := (mem_powersetCard.mp hF).1
    have hF'sub : F' ⊆ U := (mem_powersetCard.mp hF').1
    have hFcard : F.card = d := (mem_powersetCard.mp hF).2
    have hF'card : F'.card = d := (mem_powersetCard.mp hF').2
    let K := F ∪ F'
    let r := (F ∩ F').card
    have hKsub : K ⊆ U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hFsub hx
      · exact hF'sub hx
    have hKcard : K.card = 2 * d - r := by
      have h := Finset.card_union_add_card_inter F F'
      dsimp [K, r]
      omega
    have hrle : r ≤ d := by
      have hi : (F ∩ F').card ≤ F.card :=
        Finset.card_le_card inter_subset_left
      dsimp [r]
      omega
    have hdiffcard : (U \ K).card = d + r := by
      have hc : (U \ K).card = U.card - (K ∩ U).card :=
        Finset.card_sdiff
      rw [inter_eq_left.mpr hKsub, hU, hKcard] at hc
      omega
    let S := (U.powersetCard (2 * d)).filter fun E => K ⊆ E
    let T := (U \ K).powersetCard r
    have hcard : S.card = T.card := by
      apply Finset.card_bij (fun E _ => E \ K)
      · intro E hE
        have hEp : E ∈ U.powersetCard (2 * d) :=
          (mem_filter.mp hE).1
        have hEK : K ⊆ E :=
          (mem_filter.mp hE).2
        apply mem_powersetCard.mpr
        constructor
        · intro x hx
          have hxE : x ∈ E := (Finset.mem_sdiff.mp hx).1
          have hxK : x ∉ K := (Finset.mem_sdiff.mp hx).2
          exact Finset.mem_sdiff.mpr
            ⟨(mem_powersetCard.mp hEp).1 hxE, hxK⟩
        · have hc : (E \ K).card = E.card - (K ∩ E).card :=
            Finset.card_sdiff
          rw [inter_eq_left.mpr hEK, (mem_powersetCard.mp hEp).2, hKcard] at hc
          omega
      · intro E hE E' hE' heq
        have hEK : K ⊆ E := (mem_filter.mp hE).2
        have hE'K : K ⊆ E' := (mem_filter.mp hE').2
        have h₁ : (E \ K) ∪ K = E := by
          ext x
          by_cases hx : x ∈ K
          · simp [hx, hEK hx]
          · simp [hx]
        have h₂ : (E' \ K) ∪ K = E' := by
          ext x
          by_cases hx : x ∈ K
          · simp [hx, hE'K hx]
          · simp [hx]
        rw [← h₁, ← h₂, heq]
      · intro X hX
        have hXp : X ∈ (U \ K).powersetCard r := hX
        have hXsub : X ⊆ U \ K :=
          (mem_powersetCard.mp hXp).1
        have hXKsub : X ∪ K ⊆ U := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_sdiff.mp (hXsub hx)).1
          · exact hKsub hx
        have hXdis : Disjoint X K := by
          rw [Finset.disjoint_left]
          intro x hxX hxK
          exact (Finset.mem_sdiff.mp (hXsub hxX)).2 hxK
        have hXKcard : (X ∪ K).card = 2 * d := by
          have hc := Finset.card_union_of_disjoint hXdis
          rw [(mem_powersetCard.mp hXp).2, hKcard] at hc
          omega
        refine ⟨X ∪ K, ?_, ?_⟩
        · apply mem_filter.mpr
          constructor
          · exact mem_powersetCard.mpr ⟨hXKsub, hXKcard⟩
          · exact Finset.subset_union_right
        · ext x
          by_cases hxK : x ∈ K
          · have hxnot : x ∉ X := by
              intro hxX
              exact (Finset.mem_sdiff.mp (hXsub hxX)).2 hxK
            simp [hxK, hxnot]
          · simp [hxK]
    calc
      ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card = S.card := by
        rfl
      _ = T.card := hcard
      _ = (U \ K).card.choose r := by
        simp [T]
      _ = (d + r).choose r := by
        rw [hdiffcard]
      _ = (d + r).choose d := by
        simpa [Nat.add_comm] using (@Nat.choose_symm_add r d)
