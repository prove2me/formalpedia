-- Prove2me | solution 1 for ComplementsRev.Approx.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:27:48.335326+00:00
-- url     : https://prove2.me/submissions/8ad3b2ed-f50f-41ba-9f33-dfe7cc679f5d

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

open ComplementsRev.Approx

namespace CRT46

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sweep_cons (a : Finset ι) (l : List (Finset ι)) (F : Finset (Finset ι)) :
    sweep (a :: l) F =
      sweep l (if a ∈ F ∧ a ⊆ (F.erase a).biUnion id then F.erase a else F) := rfl

lemma sweep_subset (l : List (Finset ι)) : ∀ F : Finset (Finset ι), sweep l F ⊆ F := by
  induction l with
  | nil => intro F; exact le_refl _
  | cons a l ih =>
    intro F
    rw [sweep_cons]
    refine (ih _).trans ?_
    split_ifs
    · exact Finset.erase_subset _ _
    · exact le_refl _

lemma sweep_union (l : List (Finset ι)) :
    ∀ F : Finset (Finset ι), (sweep l F).biUnion id = F.biUnion id := by
  induction l with
  | nil => intro F; rfl
  | cons a l ih =>
    intro F
    rw [sweep_cons, ih]
    split_ifs with h
    · apply le_antisymm
      · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset _ _)
      · intro x hx
        obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
        by_cases hTa : T = a
        · subst hTa; exact h.2 hxT
        · exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_erase.mpr ⟨hTa, hT⟩, hxT⟩
    · rfl

lemma sweep_good (l : List (Finset ι)) : ∀ F : Finset (Finset ι), ∀ T ∈ l,
    T ∈ sweep l F → ¬ T ⊆ ((sweep l F).erase T).biUnion id := by
  induction l with
  | nil => intro F T hT; simp at hT
  | cons a l ih =>
    intro F T hT hmem
    rw [sweep_cons] at hmem ⊢
    rcases List.mem_cons.mp hT with h | h
    · subst h
      set F' := (if T ∈ F ∧ T ⊆ (F.erase T).biUnion id then F.erase T else F) with hF'
      have hsub := sweep_subset l F'
      have hTF' : T ∈ F' := hsub hmem
      by_cases hc : T ∈ F ∧ T ⊆ (F.erase T).biUnion id
      · rw [hF', if_pos hc] at hTF'
        exact absurd hTF' (Finset.notMem_erase T F)
      · have hFF : F' = F := by rw [hF', if_neg hc]
        have hTF : T ∈ F := by rw [← hFF]; exact hTF'
        have hnot : ¬ T ⊆ (F.erase T).biUnion id := fun h' => hc ⟨hTF, h'⟩
        intro hcov
        apply hnot
        refine hcov.trans ?_
        refine Finset.biUnion_subset_biUnion_of_subset_left _ ?_
        refine Finset.erase_subset_erase _ ?_
        rw [← hFF]; exact hsub
    · exact ih _ T h hmem

def deg (E : Finset (Finset ι)) : ℕ :=
  Finset.univ.sup (fun i : ι => (E.filter (fun T => i ∈ T)).card)

lemma foldl_union (L : List (Finset (Finset ι))) :
    ∀ A : Finset (Finset ι), L.foldl (· ∪ ·) A = A ∪ L.foldl (· ∪ ·) ∅ := by
  induction L with
  | nil => intro A; simp
  | cons H L ih =>
    intro A
    simp only [List.foldl_cons]
    rw [ih (A ∪ H), ih (∅ ∪ H)]
    simp [Finset.union_assoc]

lemma main (σ : ℕ → Finset (Finset ι) → List (Finset ι))
    (hσ : ∀ round F, (σ round F).toFinset = F) (fuel : ℕ) :
    ∀ (r : ℕ) (E : Finset (Finset ι)), (∅ : Finset ι) ∉ E → E.card ≤ fuel →
    let L := partitionEdges σ r fuel E
    (∀ H ∈ L, H ⊆ E) ∧
    L.Pairwise (fun H K => Disjoint H K) ∧
    L.foldl (· ∪ ·) ∅ = E ∧
    (∀ H ∈ L, ∀ T ∈ H, ¬ T ⊆ (H.erase T).biUnion id) ∧
    L.length ≤ deg E := by
  induction fuel with
  | zero =>
    intro r E _ hc
    have hE : E = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
    subst hE
    simp [partitionEdges]
  | succ fuel ih =>
    intro r E hE hc
    by_cases h0 : E = ∅
    · subst h0; simp [partitionEdges]
    · have hdef : partitionEdges σ r (fuel + 1) E =
          sweep (σ r E) E :: partitionEdges σ (r + 1) fuel (E \ sweep (σ r E) E) := by
        simp [partitionEdges, h0]
      simp only [hdef]
      set H := sweep (σ r E) E with hH
      have hHE : H ⊆ E := sweep_subset _ _
      have hU : H.biUnion id = E.biUnion id := sweep_union _ _
      obtain ⟨T0, hT0⟩ := Finset.nonempty_iff_ne_empty.mpr h0
      have hT0ne : T0.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; rintro rfl; exact hE hT0
      obtain ⟨i0, hi0⟩ := hT0ne
      have hHne : H.Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty] at hn
        have : i0 ∈ E.biUnion id := Finset.mem_biUnion.mpr ⟨T0, hT0, hi0⟩
        rw [← hU, hn] at this
        simp at this
      have hcard : (E \ H).card ≤ fuel := by
        have := Finset.card_sdiff_add_card_eq_card hHE
        have := hHne.card_pos
        omega
      have hE' : (∅ : Finset ι) ∉ E \ H := fun h => hE (Finset.mem_sdiff.mp h).1
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih (r + 1) (E \ H) hE' hcard
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro K hK
        rcases List.mem_cons.mp hK with h | h
        · rw [h]; exact hHE
        · exact (h1 K h).trans Finset.sdiff_subset
      · refine List.Pairwise.cons ?_ h2
        intro K hK
        exact Finset.disjoint_of_subset_right (h1 K hK) Finset.disjoint_sdiff
      · simp only [List.foldl_cons]
        rw [foldl_union, h3]
        simp [Finset.union_sdiff_of_subset hHE]
      · intro K hK
        rcases List.mem_cons.mp hK with h | h
        · rw [h]
          intro T hT
          have hTl : T ∈ σ r E := by
            rw [← List.mem_toFinset, hσ]; exact hHE hT
          exact sweep_good _ E T hTl hT
        · exact h4 K h
      · simp only [List.length_cons]
        have hdegpos : 1 ≤ deg E := by
          unfold deg
          refine le_trans ?_ (Finset.le_sup (f := fun i : ι => (E.filter (fun T => i ∈ T)).card)
            (Finset.mem_univ i0))
          exact Finset.card_pos.mpr ⟨T0, Finset.mem_filter.mpr ⟨hT0, hi0⟩⟩
        have hstep : deg (E \ H) ≤ deg E - 1 := by
          unfold deg
          refine Finset.sup_le (fun i _ => ?_)
          by_cases hz : ((E \ H).filter (fun T => i ∈ T)).card = 0
          · rw [hz]; exact Nat.zero_le _
          · obtain ⟨T', hT'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
            obtain ⟨hT'EH, hiT'⟩ := Finset.mem_filter.mp hT'
            have hiU : i ∈ E.biUnion id :=
              Finset.mem_biUnion.mpr ⟨T', (Finset.mem_sdiff.mp hT'EH).1, hiT'⟩
            rw [← hU] at hiU
            obtain ⟨T'', hT''H, hiT''⟩ := Finset.mem_biUnion.mp hiU
            have hsub : insert T'' ((E \ H).filter (fun T => i ∈ T)) ⊆
                E.filter (fun T => i ∈ T) := by
              intro X hX
              rcases Finset.mem_insert.mp hX with hX | hX
              · subst hX; exact Finset.mem_filter.mpr ⟨hHE hT''H, hiT''⟩
              · obtain ⟨a, b⟩ := Finset.mem_filter.mp hX
                exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp a).1, b⟩
            have hnot : T'' ∉ (E \ H).filter (fun T => i ∈ T) := by
              intro hm
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).2 hT''H
            have hc1 := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem hnot] at hc1
            have hc2 : (E.filter (fun T => i ∈ T)).card ≤
                Finset.univ.sup (fun i : ι => (E.filter (fun T => i ∈ T)).card) :=
              Finset.le_sup (f := fun i : ι => (E.filter (fun T => i ∈ T)).card)
                (Finset.mem_univ i)
            omega
        omega

end CRT46

open CRT46 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Finset (Finset ι)) (hE : (∅ : Finset ι) ∉ E)
    (σ : ℕ → Finset (Finset ι) → List (Finset ι))
    (hσ : ∀ round F, (σ round F).toFinset = F)
    (hσ_nodup : ∀ round F, (σ round F).Nodup) :
    let L := partitionEdges σ 0 E.card E
    L.Pairwise (fun H K => Disjoint H K) ∧
    L.foldl (· ∪ ·) ∅ = E ∧
    (∀ H ∈ L, ∀ T ∈ H, ¬ T ⊆ (H.erase T).biUnion id) ∧
    L.length ≤ Finset.univ.sup (fun i : ι => (E.filter (fun T => i ∈ T)).card) := by
  obtain ⟨_, h2, h3, h4, h5⟩ := main σ hσ E.card 0 E hE le_rfl
  exact ⟨h2, h3, h4, h5⟩
