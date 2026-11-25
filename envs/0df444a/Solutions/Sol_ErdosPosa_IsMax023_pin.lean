-- Prove2me | solution 1 for ErdosPosa.IsMax023.pin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:03.757567+00:00
-- url     : https://prove2.me/submissions/a62a4f4c-39f4-409f-a8f0-09fc85b99681

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
public import Theorems.Thm_ErdosPosa_first_hit
public import Theorems.Thm_ErdosPosa_restr_le
public import Theorems.Thm_ErdosPosa_support_restr
public import Theorems.Thm_ErdosPosa_edges_restr
public import Theorems.Thm_ErdosPosa_support_closed
public import Theorems.Thm_ErdosPosa_not_H_adj
public import Theorems.Thm_ErdosPosa_IsMax023_exists_W
public import Theorems.Thm_ErdosPosa_Cyc_nonempty
public import Theorems.Thm_ErdosPosa_IsMax023_adj_W
public import Theorems.Thm_ErdosPosa_IsMax023_no_path_W
public import Theorems.Thm_ErdosPosa_MinCyc_reachable
public import Theorems.Thm_ErdosPosa_MinCyc_two_nbrs
public import Theorems.Thm_ErdosPosa_cyc_glue
public import Theorems.Thm_ErdosPosa_exists_minCyc
public import Theorems.Thm_ErdosPosa_not_adj_of_deg_zero
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
namespace IsMax023
theorem _root_.solution (hH : IsMax023 G H) {A : Set V} (hA : ∀ v ∈ A, deg H v ≠ 3) (hc : Cyc G A) :
    ∃ S ⊆ A, Cyc G S ∧ ∃ z ∈ S, ∀ T ⊆ A, MinCyc G T → (∃ x, x ∈ T ∧ x ∈ S) → z ∈ T := by
  classical
  have hdeg02 : ∀ v ∈ A, deg H v ≠ 2 → deg H v = 0 := by
    intro v hv h2
    rcases hH.2.1 v with h | h | h
    · exact h
    · exact absurd h h2
    · exact absurd h (hA v hv)
  by_cases h1 : ∃ S ⊆ A, Cyc G S ∧ ∀ w1 w2, w1 ∈ S → w2 ∈ S → deg H w1 = 2 → deg H w2 = 2 →
      w1 = w2
  · obtain ⟨S, hSA, hS, hS1⟩ := h1
    obtain ⟨S', hS'S, hS'⟩ := exists_minCyc hS
    obtain ⟨z, hzS', hz2⟩ := hH.exists_W hS'.1 (fun v hv => hA v (hSA (hS'S hv)))
    have hzonly : ∀ y ∈ S', y ≠ z → deg H y = 0 := by
      intro y hy hyz
      refine hdeg02 y (hSA (hS'S hy)) (fun h2 => hyz ?_)
      exact hS1 y z (hS'S hy) (hS'S hzS') h2 hz2
    refine ⟨S', hS'S.trans hSA, hS'.1, z, hzS', ?_⟩
    rintro T hTA hT ⟨x, hxT, hxS'⟩
    by_contra hzT
    have hxz : x ≠ z := fun h => hzT (h ▸ hxT)
    obtain ⟨w, hwT, hw2⟩ := hH.exists_W hT.1 (fun v hv => hA v (hTA hv))
    obtain ⟨p⟩ := hT.reachable hxT hwT
    obtain ⟨w', hw'2, q, hq1, hq2⟩ := first_hit (fun y => deg H y = 2) p hw2
    have hqT : ∀ y ∈ q.support, y ∈ T := fun y hy => support_restr p hxT y (hq2 y hy)
    have hw'T : w' ∈ T := hqT w' q.end_mem_support
    have hzw' : z ≠ w' := fun h => hzT (h ▸ hw'T)
    obtain ⟨q1⟩ := hS'.reachable hzS' hxS'
    have hq1S : ∀ y ∈ q1.support, y ∈ S' := support_restr q1 hzS'
    let W : G.Walk z w' := (q1.mapLe (restr_le _ _)).append (q.mapLe (restr_le _ _))
    refine hH.no_path_W hz2 hw'2 hzw' W ?_ ?_
    · intro y hy
      rw [Walk.mem_support_append_iff, Walk.support_mapLe_eq_support,
        Walk.support_mapLe_eq_support] at hy
      rcases hy with hy | hy
      · by_cases hyz : y = z
        · exact Or.inl hyz
        · exact Or.inr (Or.inr (hzonly y (hq1S y hy) hyz))
      · by_cases hyw : y = w'
        · exact Or.inr (Or.inl hyw)
        · exact Or.inr (Or.inr (hdeg02 y (hTA (hqT y hy)) (hq1 y hy hyw)))
    · intro e he
      rw [Walk.edges_append, Walk.edges_mapLe_eq_edges, Walk.edges_mapLe_eq_edges,
        List.mem_append] at he
      rcases he with he | he
      · obtain ⟨c, d, rfl, hcd, hc, hd⟩ := edges_restr q1 he
        refine not_H_adj (a := z) hcd ?_ ?_
        · by_cases h : c = z
          · exact Or.inl h
          · exact Or.inr (hzonly c hc h)
        · by_cases h : d = z
          · exact Or.inl h
          · exact Or.inr (hzonly d hd h)
      · obtain ⟨c, d, rfl, hcd, hc, hd⟩ := edges_restr q he
        have hcq : c ∈ q.support := q.fst_mem_support_of_mem_edges he
        have hdq : d ∈ q.support := q.snd_mem_support_of_mem_edges he
        refine not_H_adj (a := w') hcd ?_ ?_
        · by_cases h : c = w'
          · exact Or.inl h
          · exact Or.inr (hdeg02 c (hTA hc) (hq1 c hcq h))
        · by_cases h : d = w'
          · exact Or.inl h
          · exact Or.inr (hdeg02 d (hTA hd) (hq1 d hdq h))
  · push Not at h1
    -- every minimal cycle inside `A` consists of degree-2 vertices
    have hW : ∀ T ⊆ A, MinCyc G T → ∀ t ∈ T, deg H t = 2 := by
      intro T hTA hT r hrT
      by_contra hr2
      have hr0 : deg H r = 0 := hdeg02 r (hTA hrT) hr2
      let TR : Set V := {y | y ∈ T ∧ deg H y = 0}
      let C : Set V := {y | y ∈ TR ∧ (restr G TR).Reachable r y}
      have hrC : r ∈ C := ⟨⟨hrT, hr0⟩, Reachable.refl _⟩
      have hCT : C ⊆ T := fun y hy => hy.1.1
      have hN : ∀ w1 w2 c1 c2, deg H w1 = 2 → deg H w2 = 2 → c1 ∈ C → c2 ∈ C →
          G.Adj c1 w1 → G.Adj c2 w2 → w1 = w2 := by
        intro w1 w2 c1 c2 hw1 hw2 hc1 hc2 ha1 ha2
        by_contra hne
        obtain ⟨pc⟩ := hc1.2.symm.trans hc2.2
        have hpc : ∀ y ∈ pc.support, y ∈ TR := support_restr pc hc1.1
        let W : G.Walk w1 w2 :=
          Walk.cons ha1.symm ((pc.mapLe (restr_le _ _)).concat ha2)
        refine hH.no_path_W hw1 hw2 hne W ?_ ?_
        · intro y hy
          simp only [W, Walk.support_cons, Walk.support_concat,
            List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            Walk.support_mapLe_eq_support] at hy
          rcases hy with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (hpc y h).2)
          · exact Or.inr (Or.inl h)
        · intro e he
          simp only [W, Walk.edges_cons, Walk.edges_concat, List.concat_eq_append,
            List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            Walk.edges_mapLe_eq_edges] at he
          rcases he with rfl | he | rfl
          · exact fun h => not_adj_of_deg_zero hc1.1.2 h.symm
          · obtain ⟨c, d, rfl, hcd, hc, hd⟩ := edges_restr pc he
            exact not_adj_of_deg_zero hc.2
          · exact not_adj_of_deg_zero hc2.1.2
      obtain ⟨z, hzT, hzr, hz⟩ : ∃ z ∈ T, (z = r ∨ deg H z = 2) ∧
          ∀ w c, w ∈ T → deg H w = 2 → c ∈ C → G.Adj c w → w = z := by
        by_cases hex : ∃ w c, w ∈ T ∧ deg H w = 2 ∧ c ∈ C ∧ G.Adj c w
        · obtain ⟨w0, c0, hw0T, hw02, hc0, hcw0⟩ := hex
          exact ⟨w0, hw0T, Or.inr hw02, fun w c _ hw2 hc hcw => hN w w0 c c0 hw2 hw02 hc hc0
            hcw hcw0⟩
        · push Not at hex
          exact ⟨r, hrT, Or.inl rfl, fun w c hwT hw2 hc hcw => absurd hcw (hex w c hwT hw2 hc)⟩
      let X : Set V := insert z C
      let Y : Set V := T \ C
      have hXY : X ∪ Y = T := by
        ext y
        simp only [X, Y, Set.mem_union, Set.mem_insert_iff, Set.mem_sdiff]
        constructor
        · rintro ((rfl | h) | h)
          · exact hzT
          · exact hCT h
          · exact h.1
        · intro hy
          by_cases hyC : y ∈ C
          · exact Or.inl (Or.inr hyC)
          · exact Or.inr ⟨hy, hyC⟩
      have hglue := cyc_glue (X := X) (Y := Y) (H := G) (hXY ▸ hT.1) ?_ ?_
      · rcases hglue with hX | hY
        · have hXA : X ⊆ A := by
            intro y hy
            rcases hy with rfl | hy
            · exact hTA hzT
            · exact hTA (hCT hy)
          obtain ⟨w1, w2, hw1, hw2, h12, h22, hne⟩ := h1 X hXA hX
          have hXW : ∀ w ∈ X, deg H w = 2 → w = z := by
            intro w hw h2
            rcases hw with rfl | hw
            · rfl
            · rw [hw.1.2] at h2; exact absurd h2 (by norm_num)
          exact hne ((hXW w1 hw1 h12).trans (hXW w2 hw2 h22).symm)
        · have := hT.2 Y Set.sdiff_subset hY
          have hrY : r ∈ Y := this ▸ hrT
          exact hrY.2 hrC
      · intro a b haX haY hbY hbX hab
        have haC : a ∈ C := by
          rcases haX with rfl | h
          · by_contra hzC; exact haY ⟨hzT, hzC⟩
          · exact h
        have hbz : b ≠ z := fun h => hbX (Or.inl h)
        have hbC : b ∉ C := hbY.2
        rcases hH.2.1 b with hb | hb | hb
        · apply hbC
          refine ⟨⟨hbY.1, hb⟩, haC.2.trans ?_⟩
          exact Adj.reachable ⟨hab, haC.1, ⟨hbY.1, hb⟩⟩
        · exact hbz (hz b a hbY.1 hb haC hab)
        · exact hA b (hTA hbY.1) hb
      · intro a b haX haY hbX hbY
        have ha : a = z := by
          rcases haX with h | h
          · exact h
          · exact absurd h haY.2
        have hb : b = z := by
          rcases hbX with h | h
          · exact h
          · exact absurd h hbY.2
        rw [ha, hb]
    obtain ⟨S, hSA, hS⟩ := exists_minCyc hc
    obtain ⟨z, hzS⟩ := hS.1.nonempty
    have hS2 := hW S hSA hS
    have hclosed : ∀ s ∈ S, ∀ w, deg H w = 2 → G.Adj s w → w ∈ S := by
      intro s hs w hw2 hsw
      obtain ⟨y, y', hy, hy', hyy', hsy, hsy'⟩ := hS.two_nbrs hs
      have h1 : H.Adj s y := hH.adj_W (hS2 s hs) (hS2 y hy) hsy
      have h2 : H.Adj s y' := hH.adj_W (hS2 s hs) (hS2 y' hy') hsy'
      have h3 : H.Adj s w := hH.adj_W (hS2 s hs) hw2 hsw
      have hsub : ({y, y'} : Set V) ⊆ H.neighborSet s := by
        intro a ha
        rcases ha with rfl | rfl
        · exact h1
        · exact h2
      have heq : ({y, y'} : Set V) = H.neighborSet s := by
        apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
        rw [Set.ncard_pair hyy', ← deg, hS2 s hs]
      have : w ∈ ({y, y'} : Set V) := by rw [heq]; exact h3
      rcases this with rfl | rfl
      · exact hy
      · exact hy'
    refine ⟨S, hSA, hS.1, z, hzS, ?_⟩
    rintro T hTA hT ⟨x, hxT, hxS⟩
    have hTS : T ⊆ S := by
      intro t ht
      obtain ⟨p⟩ := hT.reachable hxT ht
      refine support_closed (G' := restr G T) ?_ p hxS
      intro a b hab ha
      exact hclosed a ha b (hW T hTA hT b hab.2.2) hab.1
    rw [hS.2 T hTS hT.1]
    exact hzS
end IsMax023
end ErdosPosa
