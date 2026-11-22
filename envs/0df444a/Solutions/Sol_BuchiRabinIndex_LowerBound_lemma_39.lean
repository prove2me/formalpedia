-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_39
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:38:45.293222+00:00
-- url     : https://prove2.me/submissions/d25c763e-c65c-49eb-a38d-757b2d42ad3c

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_38

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma39Aux
open BuchiRabinIndex.LowerBound
open scoped Classical

lemma treeData_ext {Q : Type} {A B : TreeData Q}
    (hn : A.nodes = B.nodes) (hl : ∀ x, A.label x = B.label x) : A = B := by
  cases A; cases B
  simp only [TreeData.mk.injEq]
  exact ⟨hn, funext hl⟩

lemma append_singleton_inj {α : Type} :
    ∀ {p1 p2 : List α} {a b : α}, p1 ++ [a] = p2 ++ [b] → p1 = p2 ∧ a = b
  | [], [], _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h => by have := congrArg List.length h; simp at this
  | _ :: _, [], _, _, h => by have := congrArg List.length h; simp at this
  | _ :: cs1, _ :: cs2, a, b, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, hrest⟩ := h
    obtain ⟨rfl, rfl⟩ := append_singleton_inj hrest
    exact ⟨rfl, rfl⟩

lemma getLastBang_append_singleton : ∀ (w : List ℕ) (k : ℕ), (w ++ [k]).getLast! = k
  | [], k => rfl
  | a :: ws, k => by
    rw [List.getLast!_eq_getLast?_getD]
    have hlast : (a :: (ws ++ [k])).getLast? = some k := by
      simpa using List.getLast?_append_of_ne_nil (a :: ws) (by simp : [k] ≠ [])
    simp [hlast]

lemma le_degree_of_mem {T : Finset Node} {w : Node} {k : ℕ} (hmem : w ++ [k] ∈ T) :
    k ≤ degree T w := by
  have hch : w ++ [k] ∈ children T w := Finset.mem_filter.mpr ⟨hmem, k, rfl⟩
  have hle : id ((w ++ [k]).getLast!) ≤ degree T w := by
    unfold degree
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hch)
  simpa [getLastBang_append_singleton] using hle

lemma preLt_nil_left (y : Node) : PreLt [] y ↔ y ≠ [] := by
  constructor
  · rintro (⟨_, hne⟩ | ⟨p, i, j, u, v, h1, _, _⟩)
    · exact hne.symm
    · simp at h1
  · intro hne
    exact Or.inl ⟨List.nil_prefix, hne.symm⟩

lemma preLt_nil_right (x : Node) : ¬ PreLt x [] := by
  rintro (⟨hp, hne⟩ | ⟨p, i, j, u, v, _, h2, _⟩)
  · rw [List.prefix_nil] at hp
    exact hne hp
  · simp at h2

lemma preLt_cons_iff (a b : ℕ) (xs ys : Node) :
    PreLt (a :: xs) (b :: ys) ↔ a < b ∨ (a = b ∧ PreLt xs ys) := by
  constructor
  · rintro (⟨hp, hne⟩ | ⟨p, i, j, u, v, h1, h2, hij⟩)
    · obtain ⟨ rfl, hp' ⟩ := List.cons_prefix_cons.mp hp
      exact Or.inr ⟨rfl, Or.inl ⟨hp', fun h => hne (by rw [h])⟩⟩
    · cases p with
      | nil =>
        simp at h1 h2
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨rfl, rfl⟩ := h2
        exact Or.inl hij
      | cons c ps =>
        simp only [List.cons_append, List.cons.injEq] at h1 h2
        obtain ⟨rfl, h1'⟩ := h1
        obtain ⟨hb, h2'⟩ := h2
        subst hb
        exact Or.inr ⟨rfl, Or.inr ⟨ps, i, j, u, v, h1', h2', hij⟩⟩
  · rintro (hab | ⟨rfl, hpre⟩)
    · exact Or.inr ⟨[], a, b, xs, ys, rfl, rfl, hab⟩
    · rcases hpre with ⟨hp, hne⟩ | ⟨p, i, j, u, v, h1, h2, hij⟩
      · exact Or.inl ⟨List.cons_prefix_cons.mpr ⟨rfl, hp⟩, fun h => hne (by simpa using h)⟩
      · exact Or.inr ⟨a :: p, i, j, u, v, by simp [h1], by simp [h2], hij⟩

lemma preLt_irrefl : ∀ x : Node, ¬ PreLt x x
  | [] => preLt_nil_right []
  | a :: xs => by
    rw [preLt_cons_iff]
    rintro (h | ⟨_, h⟩)
    · omega
    · exact preLt_irrefl xs h

lemma preLt_trans : ∀ {x y z : Node}, PreLt x y → PreLt y z → PreLt x z
  | [], _, [], _, hyz => absurd hyz (preLt_nil_right _)
  | [], _, _ :: _, _, _ => (preLt_nil_left _).mpr (by simp)
  | _ :: _, [], _, hxy, _ => absurd hxy (preLt_nil_right _)
  | _ :: _, _ :: _, [], _, hyz => absurd hyz (preLt_nil_right _)
  | a :: xs, b :: ys, c :: zs, hxy, hyz => by
    rw [preLt_cons_iff] at hxy hyz ⊢
    rcases hxy with hab | ⟨rfl, hxy'⟩ <;> rcases hyz with hbc | ⟨rfl, hyz'⟩
    · exact Or.inl (by omega)
    · exact Or.inl hab
    · exact Or.inl hbc
    · exact Or.inr ⟨rfl, preLt_trans hxy' hyz'⟩

lemma preLt_trichotomy : ∀ x y : Node, PreLt x y ∨ x = y ∨ PreLt y x
  | [], [] => Or.inr (Or.inl rfl)
  | [], b :: ys => Or.inl ((preLt_nil_left _).mpr (by simp))
  | a :: xs, [] => Or.inr (Or.inr ((preLt_nil_left _).mpr (by simp)))
  | a :: xs, b :: ys => by
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact Or.inl ((preLt_cons_iff _ _ _ _).mpr (Or.inl hab))
    · rcases preLt_trichotomy xs ys with h | rfl | h
      · exact Or.inl ((preLt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((preLt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩)))
    · exact Or.inr (Or.inr ((preLt_cons_iff _ _ _ _).mpr (Or.inl hba)))

lemma exists_last (T : Finset Node) (hne : T.Nonempty) : ∃ z, Last T z := by
  induction T using Finset.induction_on with
  | empty => simp at hne
  | @insert a s _ ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨z, hz_mem, hz_last⟩ := ih hs
      rcases preLt_trichotomy a z with haz | rfl | hza
      · refine ⟨z, Finset.mem_insert_of_mem hz_mem, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact Or.inr haz
        · exact hz_last y hys
      · refine ⟨a, Finset.mem_insert_self a s, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact Or.inl rfl
        · exact hz_last y hys
      · refine ⟨a, Finset.mem_insert_self a s, fun y hy => ?_⟩
        rcases Finset.mem_insert.mp hy with rfl | hys
        · exact Or.inl rfl
        · rcases hz_last y hys with rfl | hyz
          · exact Or.inr hza
          · exact Or.inr (preLt_trans hyz hza)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      exact ⟨a, Finset.mem_singleton_self a, fun y hy => Or.inl (Finset.mem_singleton.mp hy)⟩

lemma rank_lt_of_preLt {T : Finset Node} {x y : Node}
    (hx : x ∈ T) (hxy : PreLt x y) : rank T x < rank T y := by
  unfold rank
  apply Finset.card_lt_card
  rw [ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨huT, hux⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨huT, preLt_trans hux hxy⟩
  · intro heq
    have hx_in : x ∈ T.filter (PreLt · y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← heq, Finset.mem_filter] at hx_in
    exact preLt_irrefl x hx_in.2

lemma rank_injOn (T : Finset Node) : Set.InjOn (rank T) {x | x ∈ T} := by
  intro x hx y hy heq
  rcases preLt_trichotomy x y with h | h | h
  · have := rank_lt_of_preLt hx h; omega
  · exact h
  · have := rank_lt_of_preLt hy h; omega

lemma rank_lt_card {T : Finset Node} {x : Node} (hx : x ∈ T) : rank T x < T.card := by
  have hsub : T.filter (PreLt · x) ⊆ T.erase x := by
    intro u hu
    obtain ⟨huT, hux⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_erase.mpr ⟨fun h => preLt_irrefl x (h ▸ hux), huT⟩
  have hle : rank T x ≤ (T.erase x).card := Finset.card_le_card hsub
  have herase : (T.erase x).card + 1 = T.card := Finset.card_erase_add_one hx
  omega

lemma image_rank_eq_range (T : Finset Node) : T.image (rank T) = Finset.range T.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (rank_lt_card hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn (rank_injOn T)]

lemma own_ne_of_eq_childLabels {Q : Type} {H : TreeData Q} {x : Node} {q : Q}
    (hq : q ∈ own H x) (heq : childLabels H x = H.label x) : False := by
  rw [own, heq, Finset.sdiff_self] at hq
  simp at hq

lemma own_eq_label_of_leaf {Q : Type} {H : TreeData Q} {x : Node}
    (hleaf : Leaf H.nodes x) : own H x = H.label x := by
  simp [own, childLabels, hleaf.2]

lemma canonical_valid_and_own {n : ℕ} (hn : 1 ≤ n) {T : Finset Node}
    (hT : Ordered T) (hne : T.Nonempty) (hcard : T.card ≤ n) :
    Valid (canonicalData n T) ∧
    (∀ x ∈ T, own (canonicalData n T) x = {stateAt n hn (rank T x)}) ∧
    stateSet (canonicalData n T) = canonicalStates n T := by
  classical
  obtain ⟨u0, hu0⟩ := hne
  have hroot : [] ∈ T := hT.2.1 u0 hu0 [] List.nil_prefix
  let f : Node → Fin n := fun y => stateAt n hn (rank T y)
  have hf_val : ∀ y ∈ T, (f y).val = rank T y := by
    intro y hy
    have hlt : rank T y < n := Nat.lt_of_lt_of_le (rank_lt_card hy) hcard
    simp [f, stateAt, Nat.mod_eq_of_lt hlt]
  have hinj_f : Set.InjOn f {y | y ∈ T} := by
    intro y1 hy1 y2 hy2 heq
    have hv := congrArg Fin.val heq
    rw [hf_val y1 hy1, hf_val y2 hy2] at hv
    exact rank_injOn T hy1 hy2 hv
  have hl_in : ∀ x ∈ T,
      (canonicalData n T).label x = (T.filter fun y => x.IsPrefix y).image f := by
    intro x hx
    simp only [canonicalData, if_pos hx]
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨y, hyT, hxy, hqval⟩
      refine ⟨y, ⟨hyT, hxy⟩, Fin.ext ?_⟩
      rw [hf_val y hyT, hqval]
    · rintro ⟨y, ⟨hyT, hxy⟩, rfl⟩
      exact ⟨y, hyT, hxy, hf_val y hyT⟩
  have hl_out : ∀ x, x ∉ T → (canonicalData n T).label x = ∅ := by
    intro x hx
    simp [canonicalData, hx]
  have hchild_lbl : ∀ x ∈ T,
      childLabels (canonicalData n T) x = (T.filter fun y => x.IsPrefix y ∧ y ≠ x).image f := by
    intro x hx
    ext q
    simp only [childLabels, children, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨c, ⟨hcT, i, rfl⟩, hqc⟩
      rw [hl_in (x ++ [i]) hcT, Finset.mem_image] at hqc
      obtain ⟨y, hy_filt, rfl⟩ := hqc
      obtain ⟨hyT, ⟨rest, rfl⟩⟩ := Finset.mem_filter.mp hy_filt
      refine ⟨(x ++ [i]) ++ rest, ⟨hyT, ⟨[i] ++ rest, by simp⟩, ?_⟩, rfl⟩
      intro heq
      have := congrArg List.length heq
      simp at this
    · rintro ⟨y, ⟨hyT, ⟨w, rfl⟩, hne_yx⟩, rfl⟩
      cases w with
      | nil => exact absurd (by simp) hne_yx
      | cons i rest =>
        have hxi_T : x ++ [i] ∈ T := hT.2.1 _ hyT (x ++ [i]) ⟨rest, by simp⟩
        refine ⟨x ++ [i], ⟨hxi_T, i, rfl⟩, ?_⟩
        rw [hl_in (x ++ [i]) hxi_T, Finset.mem_image]
        exact ⟨x ++ i :: rest, Finset.mem_filter.mpr ⟨hyT, ⟨rest, by simp⟩⟩, rfl⟩
  have hown : ∀ x ∈ T, own (canonicalData n T) x = {f x} := by
    intro x hx
    rw [own, hl_in x hx, hchild_lbl x hx]
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨y, ⟨hyT, hxy⟩, rfl⟩, hnot⟩
      by_contra hne_q
      have hne_y : y ≠ x := fun h => hne_q (congrArg f h)
      exact hnot ⟨y, ⟨hyT, hxy, hne_y⟩, rfl⟩
    · rintro rfl
      refine ⟨⟨x, ⟨hx, List.prefix_refl x⟩, rfl⟩, ?_⟩
      rintro ⟨y, ⟨hyT, _, hne_y⟩, hfy⟩
      exact hne_y (hinj_f hyT hx hfy)
  have hv : Valid (canonicalData n T) := by
    refine ⟨hT, hroot, hl_out, ?_, ?_, ?_⟩
    · intro x hx
      rw [hl_in x hx]
      exact ⟨f x, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, List.prefix_refl x⟩, rfl⟩⟩
    · intro p i j hpi hpj hij
      rw [Finset.disjoint_left]
      intro q hqi hqj
      rw [hl_in (p ++ [i]) hpi, Finset.mem_image] at hqi
      rw [hl_in (p ++ [j]) hpj, Finset.mem_image] at hqj
      obtain ⟨y1, hy1, rfl⟩ := hqi
      obtain ⟨y2, hy2, hfy⟩ := hqj
      obtain ⟨hy1T, hp1⟩ := Finset.mem_filter.mp hy1
      obtain ⟨hy2T, hp2⟩ := Finset.mem_filter.mp hy2
      have hy_eq : y1 = y2 := hinj_f hy1T hy2T hfy.symm
      subst hy_eq
      obtain ⟨u1, hu1⟩ := hp1
      obtain ⟨u2, hu2⟩ := hp2
      have h12 : (p ++ [i]) ++ u1 = (p ++ [j]) ++ u2 := hu1.trans hu2.symm
      simp only [List.append_assoc, List.singleton_append] at h12
      have htail := List.append_cancel_left h12
      simp at htail
      exact hij htail.1
    · intro x hx
      refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · rw [hl_in x hx, hchild_lbl x hx]
        intro q hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨hyT, hxy, _⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyT, hxy⟩, rfl⟩
      · intro heq
        have hfx : f x ∈ own (canonicalData n T) x := by rw [hown x hx]; simp
        exact own_ne_of_eq_childLabels hfx heq
  have hst : stateSet (canonicalData n T) = canonicalStates n T := by
    ext q
    simp only [stateSet, canonicalData, if_pos hroot, canonicalStates,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hyT, _, hqval⟩
      rw [hqval]
      exact rank_lt_card hyT
    · intro hlt
      have hmem_rng : q.val ∈ Finset.range T.card := Finset.mem_range.mpr hlt
      rw [← image_rank_eq_range T, Finset.mem_image] at hmem_rng
      obtain ⟨y, hyT, hry⟩ := hmem_rng
      exact ⟨y, hyT, List.nil_prefix, hry.symm⟩
  exact ⟨hv, hown, hst⟩

lemma label_sub_of_prefix {Q : Type} {H : TreeData Q} (hv : Valid H) :
    ∀ (x : Node) (w : List ℕ), x ++ w ∈ H.nodes → H.label (x ++ w) ⊆ H.label x
  | x, [], _ => by simp
  | x, i :: rest, hmem => by
    have hxi_mem : x ++ [i] ∈ H.nodes :=
      hv.1.2.1 (x ++ (i :: rest)) hmem (x ++ [i]) ⟨rest, by simp⟩
    have h1 : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
      label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hmem)
    have h1' : H.label (x ++ i :: rest) ⊆ H.label (x ++ [i]) := by simpa using h1
    have hchild : x ++ [i] ∈ children H.nodes x := by simp [children, hxi_mem]
    have h2 : H.label (x ++ [i]) ⊆ childLabels H x :=
      Finset.subset_biUnion_of_mem H.label hchild
    have h3 : childLabels H x ⊆ H.label x :=
      (hv.2.2.2.2.2 x (hv.1.2.1 _ hxi_mem x ⟨[i], rfl⟩)).subset
    exact h1'.trans (h2.trans h3)

lemma label_eq_biUnion_own {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x : Node} (hx : x ∈ H.nodes) :
    H.label x = (H.nodes.filter fun y => x.IsPrefix y).biUnion (own H) := by
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · intro hq
    let S := H.nodes.filter (fun y => x.IsPrefix y ∧ q ∈ H.label y)
    have hxS : x ∈ S := Finset.mem_filter.mpr ⟨hx, List.prefix_refl x, hq⟩
    obtain ⟨y, hyS, hmax⟩ := Finset.exists_max_image S List.length ⟨x, hxS⟩
    obtain ⟨hyM, hxy, hqy⟩ := Finset.mem_filter.mp hyS
    refine ⟨y, ⟨hyM, hxy⟩, Finset.mem_sdiff.mpr ⟨hqy, ?_⟩⟩
    intro hch
    obtain ⟨c, hc_ch, hqc⟩ := Finset.mem_biUnion.mp hch
    obtain ⟨hcM, i, rfl⟩ := Finset.mem_filter.mp hc_ch
    have hx_yi : x.IsPrefix (y ++ [i]) := by
      obtain ⟨t, rfl⟩ := hxy
      exact ⟨t ++ [i], by simp⟩
    have hyi_S : y ++ [i] ∈ S := Finset.mem_filter.mpr ⟨hcM, hx_yi, hqc⟩
    have hle := hmax (y ++ [i]) hyi_S
    simp at hle
  · rintro ⟨y, ⟨hyM, ⟨w, rfl⟩⟩, hq_own⟩
    exact label_sub_of_prefix hv x w hyM (Finset.mem_sdiff.mp hq_own).1

lemma treeData_eq_of_valid_own {Q : Type} {A B : TreeData Q}
    (hvA : Valid A) (hvB : Valid B)
    (hnodes : A.nodes = B.nodes)
    (hown : ∀ u ∈ A.nodes, own A u = own B u) : A = B := by
  apply treeData_ext hnodes
  intro x
  by_cases hx : x ∈ A.nodes
  · have hxB : x ∈ B.nodes := hnodes ▸ hx
    rw [label_eq_biUnion_own hvA hx, label_eq_biUnion_own hvB hxB]
    have hfilt : A.nodes.filter (fun y => x.IsPrefix y) = B.nodes.filter (fun y => x.IsPrefix y) := by
      rw [hnodes]
    rw [hfilt]
    apply Finset.biUnion_congr rfl
    intro u hu
    exact hown u (hnodes.symm ▸ (Finset.mem_filter.mp hu).1)
  · have hxB : x ∉ B.nodes := hnodes ▸ hx
    rw [hvA.2.2.1 x hx, hvB.2.2.1 x hxB]

lemma mapData_eq_of_valid_own {Q : Type} {A B : TreeData Q} (π : Q → Q)
    (hvA : Valid A) (hvB : Valid B) (hnodes : A.nodes = B.nodes)
    (hown : ∀ u ∈ A.nodes, ∀ q, q ∈ own B u ↔ ∃ r ∈ own A u, π r = q) :
    mapData A π = B := by
  refine treeData_ext hnodes ?_
  intro x
  by_cases hx : x ∈ A.nodes
  · have hxB : x ∈ B.nodes := hnodes ▸ hx
    ext q
    dsimp only [mapData]
    rw [Finset.mem_image, label_eq_biUnion_own hvB hxB, Finset.mem_biUnion]
    constructor
    · rintro ⟨r, hr, rfl⟩
      rw [label_eq_biUnion_own hvA hx, Finset.mem_biUnion] at hr
      obtain ⟨u, hu_filt, hru⟩ := hr
      obtain ⟨huA, hxu⟩ := Finset.mem_filter.mp hu_filt
      exact ⟨u, Finset.mem_filter.mpr ⟨hnodes ▸ huA, hxu⟩, (hown u huA (π r)).mpr ⟨r, hru, rfl⟩⟩
    · rintro ⟨u, hu_filt, hqu⟩
      obtain ⟨huB, hxu⟩ := Finset.mem_filter.mp hu_filt
      have huA : u ∈ A.nodes := hnodes.symm ▸ huB
      obtain ⟨r, hru, rfl⟩ := (hown u huA q).mp hqu
      refine ⟨r, ?_, rfl⟩
      rw [label_eq_biUnion_own hvA hx, Finset.mem_biUnion]
      exact ⟨u, Finset.mem_filter.mpr ⟨huA, hxu⟩, hru⟩
  · have hxB : x ∉ B.nodes := hnodes ▸ hx
    dsimp only [mapData]
    rw [hvA.2.2.1 x hx, hvB.2.2.1 x hxB, Finset.image_empty]

lemma readWord_append {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ (u v : List Sigma) (H : Option (History Q)),
      readWord B H (u ++ v) = readWord B (readWord B H u) v
  | [], _, _ => rfl
  | σ :: u, v, H => readWord_append B u v (H.bind fun h => successor B h σ)

lemma reachable_step {Q Sigma : Type} {B : NBW Q Sigma}
    {H H' : History Q} {σ : Sigma}
    (hr : Reachable B H) (hs : successor B H σ = some H') :
    Reachable B H' := by
  obtain ⟨u, hu⟩ := hr
  refine ⟨u ++ [σ], ?_⟩
  rw [readWord_append, hu]
  simpa [readWord] using hs

lemma degree_erase_youngest {T : Finset Node} (hT : Ordered T)
    {w : Node} {i0 : ℕ} (hzT : w ++ [i0] ∈ T) (hi0 : 0 < i0) (hdeg : i0 = degree T w) :
    degree (T.erase (w ++ [i0])) w + 1 = i0 := by
  let T' := T.erase (w ++ [i0])
  by_cases h1 : i0 = 1
  · subst h1
    have hch_emp : children T' w = ∅ := by
      rw [children, Finset.filter_eq_empty_iff]
      rintro y hy ⟨j, rfl⟩
      obtain ⟨hne, hyT⟩ := Finset.mem_erase.mp hy
      have hj_pos : 0 < j := hT.1 _ hyT j (by simp)
      have hj_le : j ≤ degree T w := le_degree_of_mem hyT
      have hj1 : j = 1 := by omega
      subst hj1
      exact hne rfl
    dsimp only [T'] at hch_emp
    simp [degree, hch_emp]
  · have hi0_ge2 : 2 ≤ i0 := by omega
    have hprev_T : w ++ [i0 - 1] ∈ T :=
      hT.2.2 w i0 hzT (i0 - 1) (by omega) (by omega)
    have hprev_T' : w ++ [i0 - 1] ∈ T' := by
      refine Finset.mem_erase.mpr ⟨?_, hprev_T⟩
      intro heq
      obtain ⟨_, heq'⟩ := append_singleton_inj heq
      omega
    have hge : i0 - 1 ≤ degree T' w := le_degree_of_mem hprev_T'
    have hle : degree T' w ≤ i0 - 1 := by
      unfold degree
      apply Finset.sup_le
      intro b hb
      obtain ⟨y, hy_ch, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨hyT', j, rfl⟩ := Finset.mem_filter.mp hy_ch
      obtain ⟨hne, hyT⟩ := Finset.mem_erase.mp hyT'
      have hj_le : j ≤ degree T w := le_degree_of_mem hyT
      have hj_ne : j ≠ i0 := fun h => hne (by rw [h])
      rw [id, getLastBang_append_singleton]
      omega
    dsimp only [T'] at hge hle
    omega

lemma reach_by_card (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ T : Finset Node, Ordered T → T.card = k →
        ∃ H, Htree n T = some H ∧ Reachable (fullBuchi n hn) H := by
  classical
  intro k hk1 hkn
  induction k with
  | zero => omega
  | succ m ih =>
    intro T hT hcard_eq
    let F := fullBuchi n hn
    obtain ⟨hvT, hownT, hstT⟩ :=
      canonical_valid_and_own hn hT (Finset.card_pos.mp (by omega)) (by omega)
    let H : History (Fin n) := ⟨canonicalData n T, hvT⟩
    have hHtree : Htree n T = some H := by simp [Htree, asHistory, hvT, H]
    by_cases hm0 : m = 0
    · subst hm0
      have hroot : [] ∈ T := hvT.2.1
      have hT_eq : T = {[]} := by
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard_eq
        have : [] ∈ ({a} : Finset Node) := ha ▸ hroot
        rw [Finset.mem_singleton] at this
        subst a
        exact ha
      have hinit_eq : initialData F = canonicalData n T := by
        refine treeData_ext ?_ ?_
        · exact hT_eq.symm
        · intro x
          by_cases hx : x = []
          · subst hx
            change (if ([] : Node) = [] then F.initial else ∅) = stateSet (canonicalData n T)
            rw [if_pos rfl, hstT]
            ext q
            dsimp only [F, fullBuchi, canonicalStates]
            rw [Finset.mem_singleton, Finset.mem_filter, hcard_eq]
            constructor
            · rintro rfl
              exact ⟨Finset.mem_univ _, Nat.zero_lt_one⟩
            · rintro ⟨_, hlt⟩
              ext
              dsimp only
              omega
          · have hxT : x ∉ T := by rw [hT_eq, Finset.mem_singleton]; exact hx
            simp only [initialData, canonicalData, if_neg hx, if_neg hxT]
      have hinitH : initialHistory F = some H := by
        unfold initialHistory
        rw [hinit_eq]
        exact hHtree
      exact ⟨H, hHtree, ⟨[], by simpa [readWord] using hinitH⟩⟩
    · have hm1 : 1 ≤ m := by omega
      have hmn : m < n := by omega
      obtain ⟨z, hzLast⟩ := exists_last T (Finset.card_pos.mp (by omega))
      have hz_ne_nil : z ≠ [] := by
        rintro rfl
        have hsub : T ⊆ {[]} := by
          intro y hy
          rcases hzLast.2 y hy with rfl | hy0
          · simp
          · exact absurd hy0 (preLt_nil_right y)
        have hle1 : T.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
        omega
      have hf30 := (fact_30 [] [] (fun i hi => by simp at hi) (fun i hi => by simp at hi)).2.2.2.2.2.2.2.2
        T z hT hzLast
      have hleaf_z : Leaf T z := hf30.1
      have hyng_z : Youngest T z := hf30.2 hz_ne_nil
      obtain ⟨w, i0, hz_eq, hi0_pos, hi0_deg⟩ := hyng_z
      let T' := T.erase z
      have hwT : w ∈ T := hT.2.1 z hzLast.1 w ⟨[i0], hz_eq.symm⟩
      have hw_ne_z : w ≠ z := by
        intro heq
        rw [hz_eq] at heq
        have := congrArg List.length heq
        simp at this
      have hwT' : w ∈ T' := Finset.mem_erase.mpr ⟨hw_ne_z, hwT⟩
      have hT'_ord : Ordered T' := by
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          exact hT.1 x (Finset.mem_erase.mp hx).2
        · intro x hx q hqx
          obtain ⟨hxz, hxT⟩ := Finset.mem_erase.mp hx
          refine Finset.mem_erase.mpr ⟨?_, hT.2.1 x hxT q hqx⟩
          intro hqz
          subst q
          obtain ⟨t, rfl⟩ := hqx
          cases t with
          | nil => exact hxz (by simp)
          | cons k rest =>
            have hkT : z ++ [k] ∈ T := hT.2.1 _ hxT (z ++ [k]) ⟨rest, by simp⟩
            have hk_ch : z ++ [k] ∈ children T z := Finset.mem_filter.mpr ⟨hkT, k, rfl⟩
            rw [hleaf_z.2] at hk_ch
            simp at hk_ch
        · intro q k hqk j hj0 hjk
          obtain ⟨hqk_ne, hqkT⟩ := Finset.mem_erase.mp hqk
          refine Finset.mem_erase.mpr ⟨?_, hT.2.2 q k hqkT j hj0 hjk⟩
          intro heq
          rw [hz_eq] at heq
          obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
          have hk_le : k ≤ degree T q := le_degree_of_mem hqkT
          have hkj : k = j := by omega
          subst hkj
          exact hqk_ne hz_eq.symm
      have hT'_card : T'.card = m := by
        have := Finset.card_erase_add_one hzLast.1
        dsimp only [T']
        omega
      obtain ⟨H', hH'tree, hH'reach⟩ := ih hm1 (Nat.le_of_lt hmn) T' hT'_ord hT'_card
      obtain ⟨hvT', hownT', hstT'⟩ :=
        canonical_valid_and_own hn hT'_ord ⟨w, hwT'⟩ (by omega)
      have hH'_val : H'.val = canonicalData n T' := by
        simp only [Htree, asHistory, hvT', ↓reduceDIte, Option.some.injEq] at hH'tree
        exact congrArg Subtype.val hH'tree.symm
      have hH'_simple : Simple H' := by
        intro u hu
        rw [hH'_val] at hu ⊢
        rw [hownT' u hu]
        simp
      have hrank_T' : ∀ y ∈ T', rank T y = rank T' y := by
        intro y hy
        obtain ⟨hyz, hyT⟩ := Finset.mem_erase.mp hy
        have hy_lt_z : PreLt y z := (hzLast.2 y hyT).resolve_left hyz
        unfold rank
        congr 1
        ext u
        simp only [Finset.mem_filter, T', Finset.mem_erase]
        constructor
        · rintro ⟨huT, huy⟩
          refine ⟨⟨?_, huT⟩, huy⟩
          rintro rfl
          exact preLt_irrefl y (preLt_trans hy_lt_z huy)
        · rintro ⟨⟨_, huT⟩, huy⟩
          exact ⟨huT, huy⟩
      have hrank_z : rank T z = m := by
        have hfilt : T.filter (PreLt · z) = T' := by
          ext u
          simp only [Finset.mem_filter, T', Finset.mem_erase]
          constructor
          · rintro ⟨huT, huz⟩
            exact ⟨fun h => preLt_irrefl z (h ▸ huz), huT⟩
          · rintro ⟨huz, huT⟩
            exact ⟨huT, (hzLast.2 u huT).resolve_left huz⟩
        unfold rank
        rw [hfilt, hT'_card]
      let p := stateAt n hn (rank T' w)
      have hp_in : p ∈ stateSet H'.val := by
        rw [hH'_val, hstT', canonicalStates, Finset.mem_filter]
        have hrw : rank T' w < m := by rw [← hT'_card]; exact rank_lt_card hwT'
        exact ⟨Finset.mem_univ _, by simp [p, stateAt, Nat.mod_eq_of_lt (Nat.lt_trans hrw hmn), hrw, hT'_card]⟩
      have hqn_not : lastState n hn ∉ stateSet H'.val := by
        rw [hH'_val, hstT', canonicalStates, Finset.mem_filter]
        rintro ⟨_, hlt⟩
        simp [lastState, hT'_card] at hlt
        omega
      have howner_p : owner H'.val p = w := by
        rw [hH'_val]
        have hex : ∃ x ∈ (canonicalData n T').nodes, p ∈ own (canonicalData n T') x :=
          ⟨w, hwT', by rw [hownT' w hwT']; simp [p]⟩
        unfold owner
        rw [dif_pos hex]
        obtain ⟨huT', hpu⟩ := Classical.choose_spec hex
        rw [hownT' _ huT', Finset.mem_singleton] at hpu
        have hv_eq : (stateAt n hn (rank T' w)).val = (stateAt n hn (rank T' (Classical.choose hex))).val :=
          congrArg Fin.val hpu
        have hr1 : rank T' w < n := Nat.lt_trans (by rw [← hT'_card]; exact rank_lt_card hwT') hmn
        have hr2 : rank T' (Classical.choose hex) < n :=
          Nat.lt_trans (by rw [← hT'_card]; exact rank_lt_card huT') hmn
        simp only [stateAt, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr2] at hv_eq
        exact rank_injOn T' huT' hwT' hv_eq.symm
      have hdeg_T' : degree T' w + 1 = i0 := by
        have hzT : w ++ [i0] ∈ T := hz_eq ▸ hzLast.1
        simpa [T', hz_eq] using degree_erase_youngest hT hzT hi0_pos hi0_deg
      have hz_gen : owner H'.val p ++ [degree H'.val.nodes (owner H'.val p) + 1] = z := by
        have hnodes_H' : H'.val.nodes = T' := by rw [hH'_val]; rfl
        rw [howner_p, hnodes_H', hdeg_T', hz_eq]
      have hl38_gen := (lemma_38 n hn H' hH'_simple).1 p hp_in hqn_not
      obtain ⟨⟨H1, hsucc1, hH1_val, hH1_simple, _, _⟩, hown_gen, hlbl_gen_z⟩ := hl38_gen
      have hH1_reach : Reachable F H1 := reachable_step hH'reach hsucc1
      have hH1_nodes : H1.val.nodes = T := by
        rw [hH1_val]
        change insert (owner H'.val p ++ [degree H'.val.nodes (owner H'.val p) + 1]) H'.val.nodes = T
        rw [hz_gen, hH'_val]
        exact Finset.insert_erase hzLast.1
      have hleaf_H1_z : Leaf H1.val.nodes z := by rwa [hH1_nodes]
      have hown_H1_z : own H1.val z = {lastState n hn} := by
        rw [own_eq_label_of_leaf hleaf_H1_z, hH1_val, ← hz_gen]
        exact hlbl_gen_z
      by_cases hfull : m + 1 = n
      · have hH1_eq_H : H1 = H := by
          apply Subtype.ext
          apply treeData_eq_of_valid_own H1.property hvT hH1_nodes
          intro u hu
          rw [hH1_nodes] at hu
          by_cases huz : u = z
          · subst u
            rw [hown_H1_z, hownT z hzLast.1, hrank_z]
            have hm_eq : m = n - 1 := by omega
            congr 1
            ext
            simp [lastState, stateAt, hm_eq, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
          · have huT' : u ∈ H'.val.nodes := by
              rw [hH'_val]
              exact Finset.mem_erase.mpr ⟨huz, hu⟩
            rw [hH1_val, hown_gen u huT', hH'_val, hownT' u (Finset.mem_erase.mpr ⟨huz, hu⟩),
              hownT u hu, hrank_T' u (Finset.mem_erase.mpr ⟨huz, hu⟩)]
        exact ⟨H, hHtree, hH1_eq_H ▸ hH1_reach⟩
      · have hm_lt_pred : m < n - 1 := by omega
        let qm : Fin n := ⟨m, hmn⟩
        let π : Fin n → Fin n := fun q => if q = lastState n hn then qm else q
        have hst_H1 : stateSet H1.val ⊆ insert (lastState n hn) (canonicalStates n T') := by
          rw [hH1_val]
          intro q hq
          simp only [stateSet, generatedData, Finset.mem_union] at hq
          rcases hq with hq1 | hq2
          · have hq1' : q ∈ stateSet H'.val := hq1
            rw [hH'_val, hstT'] at hq1'
            exact Finset.mem_insert_of_mem hq1'
          · split_ifs at hq2
            · rw [Finset.mem_singleton] at hq2
              exact hq2 ▸ Finset.mem_insert_self _ _
            · simp at hq2
        have hinj_π : Set.InjOn π {q | q ∈ stateSet H1.val} := by
          intro q1 hq1 q2 hq2 heq
          have h1 := hst_H1 hq1
          have h2 := hst_H1 hq2
          simp only [Finset.mem_insert, canonicalStates, Finset.mem_filter, Finset.mem_univ,
            true_and, hT'_card] at h1 h2
          by_cases c1 : q1 = lastState n hn <;> by_cases c2 : q2 = lastState n hn
          · rw [c1, c2]
          · exfalso
            rcases h2 with rfl | h2lt
            · exact c2 rfl
            · simp only [π, c1, c2, ↓reduceIte] at heq
              have hv := congrArg Fin.val heq
              simp [qm] at hv
              omega
          · exfalso
            rcases h1 with rfl | h1lt
            · exact c1 rfl
            · simp only [π, c1, c2, ↓reduceIte] at heq
              have hv := congrArg Fin.val heq
              simp [qm] at hv
              omega
          · simpa [π, c1, c2] using heq
        have hno_qn : ∀ q ∈ stateSet H1.val, π q ≠ lastState n hn := by
          intro q hq
          have h1 := hst_H1 hq
          simp only [Finset.mem_insert, canonicalStates, Finset.mem_filter, Finset.mem_univ,
            true_and, hT'_card] at h1
          by_cases cq : q = lastState n hn
          · simp only [π, cq, ↓reduceIte, ne_eq, Fin.ext_iff, qm, lastState]
            omega
          · rcases h1 with rfl | hlt
            · exact absurd rfl cq
            · dsimp only [π]
              rw [if_neg cq]
              exact cq
        have hl38_perm := (lemma_38 n hn H1 hH1_simple).2.1 π hinj_π hno_qn
        obtain ⟨H2, hsucc2, hH2_val, _, _, _⟩ := hl38_perm
        have hH2_reach : Reachable F H2 := reachable_step hH1_reach hsucc2
        have hH2_eq_H : H2 = H := by
          apply Subtype.ext
          rw [hH2_val]
          apply mapData_eq_of_valid_own π H1.property hvT hH1_nodes
          intro u huH1 q
          have huT : u ∈ T := hH1_nodes ▸ huH1
          by_cases huz : u = z
          · subst u
            rw [hown_H1_z, hownT z hzLast.1, hrank_z, Finset.mem_singleton]
            constructor
            · rintro rfl
              refine ⟨lastState n hn, Finset.mem_singleton_self _, ?_⟩
              dsimp only [π]
              rw [if_pos rfl]
              ext
              simp [qm, stateAt, Nat.mod_eq_of_lt hmn]
            · rintro ⟨r, hr, rfl⟩
              rw [Finset.mem_singleton] at hr
              subst r
              dsimp only [π]
              rw [if_pos rfl]
              ext
              simp [qm, stateAt, Nat.mod_eq_of_lt hmn]
          · have huT' : u ∈ T' := Finset.mem_erase.mpr ⟨huz, huT⟩
            have huH' : u ∈ H'.val.nodes := by rwa [hH'_val]
            have hown_u : own H1.val u = {stateAt n hn (rank T' u)} := by
              rw [hH1_val, hown_gen u huH', hH'_val, hownT' u huT']
            have hne_qn : stateAt n hn (rank T' u) ≠ lastState n hn := by
              have hru : rank T' u < m := by rw [← hT'_card]; exact rank_lt_card huT'
              intro heq
              have hv := congrArg Fin.val heq
              simp [stateAt, lastState, Nat.mod_eq_of_lt (Nat.lt_trans hru hmn)] at hv
              omega
            rw [hown_u, hownT u huT, hrank_T' u huT', Finset.mem_singleton]
            constructor
            · rintro rfl
              refine ⟨stateAt n hn (rank T' u), Finset.mem_singleton_self _, ?_⟩
              dsimp only [π]
              rw [if_neg hne_qn]
            · rintro ⟨r, hr, rfl⟩
              rw [Finset.mem_singleton] at hr
              subst r
              dsimp only [π]
              rw [if_neg hne_qn]
        exact ⟨H, hHtree, hH2_eq_H ▸ hH2_reach⟩

end BuchiRabinIndex.LowerBound.Lemma39Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma39Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (T : Finset Node)
    (hT : Ordered T) (hne : T.Nonempty) (hcard : T.card ≤ n) :
    ∃ H, Htree n T = some H ∧ Reachable (fullBuchi n hn) H := by
  exact reach_by_card n hn T.card (Finset.card_pos.mpr hne) hcard T hT rfl
