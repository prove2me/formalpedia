-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_38
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:37:02.662823+00:00
-- url     : https://prove2.me/submissions/f129465e-b691-475c-99ab-381de7374355

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma38Aux
open BuchiRabinIndex.LowerBound
open scoped Classical
noncomputable section

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

lemma dropLast_append_singleton : ∀ (w : List ℕ) (k : ℕ), (w ++ [k]).dropLast = w
  | [], _ => rfl
  | _ :: ws, k => by
    simp [List.dropLast, dropLast_append_singleton ws k]

lemma getLastBang_append_singleton : ∀ (w : List ℕ) (k : ℕ), (w ++ [k]).getLast! = k
  | [], k => rfl
  | a :: ws, k => by
    rw [List.getLast!_eq_getLast?_getD]
    have hlast : (a :: (ws ++ [k])).getLast? = some k := by
      simpa using List.getLast?_append_of_ne_nil (a :: ws) (by simp : [k] ≠ [])
    simp [hlast]

lemma getElemBang_eq_getElem : ∀ (x : List ℕ) (k : ℕ) (hk : k < x.length), x[k]! = x[k]
  | [], _, hk => by simp at hk
  | _ :: _, 0, _ => rfl
  | _ :: xs, k + 1, hk => getElemBang_eq_getElem xs k (by simpa using hk)

lemma take_append_singleton_prefix :
    ∀ (x : List ℕ) (k : ℕ) (hk : k < x.length), (x.take k ++ [x[k]]).IsPrefix x
  | [], _, hk => by simp at hk
  | _ :: xs, 0, _ => ⟨xs, rfl⟩
  | a :: xs, k + 1, hk => by
    obtain ⟨t, ht⟩ := take_append_singleton_prefix xs k (by simpa using hk)
    exact ⟨t, by simpa using congrArg (a :: ·) ht⟩

lemma exists_mem_sup_nat (S : Finset ℕ) (hne : S.Nonempty) : S.sup id ∈ S := by
  induction S using Finset.induction_on with
  | empty => simp at hne
  | @insert a s _ ih =>
    by_cases hs : s.Nonempty
    · have hmem := ih hs
      rw [Finset.sup_insert]
      change max a (s.sup id) ∈ insert a s
      by_cases hle : a ≤ s.sup id
      · rw [Nat.max_eq_right hle]
        exact Finset.mem_insert_of_mem hmem
      · rw [Nat.max_eq_left (Nat.le_of_not_le hle)]
        exact Finset.mem_insert_self a s
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp

lemma le_degree_of_mem {T : Finset Node} {w : Node} {k : ℕ} (hmem : w ++ [k] ∈ T) :
    k ≤ degree T w := by
  have hch : w ++ [k] ∈ children T w := by
    rw [children, Finset.mem_filter]
    exact ⟨hmem, k, rfl⟩
  have hle : id ((w ++ [k]).getLast!) ≤ degree T w := by
    unfold degree
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hch)
  simpa [getLastBang_append_singleton] using hle

lemma mem_of_degree_pos {T : Finset Node} {w : Node} (hd : 0 < degree T w) :
    w ++ [degree T w] ∈ T := by
  have hne_ch : (children T w).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    simp [degree, hemp] at hd
  let img := (children T w).image (fun y => y.getLast!)
  have hmem_sup : img.sup id ∈ img := exists_mem_sup_nat img (hne_ch.image _)
  change degree T w ∈ img at hmem_sup
  obtain ⟨y, hy_ch, hy_eq⟩ := Finset.mem_image.mp hmem_sup
  rw [children, Finset.mem_filter] at hy_ch
  obtain ⟨hyT, k, rfl⟩ := hy_ch
  rw [getLastBang_append_singleton] at hy_eq
  rwa [← hy_eq]

lemma newChild_notMem {T : Finset Node} (w : Node) :
    w ++ [degree T w + 1] ∉ T := by
  intro hmem
  have := le_degree_of_mem hmem
  omega

def nextLabel {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) (x : Node) :
    Finset Q :=
  (H.label x).biUnion fun q => B.delta q σ

lemma expand_nodes {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) :
    (expand B H σ).nodes = H.nodes ∪ H.nodes.image (fun u => u ++ [degree H.nodes u + 1]) := rfl

lemma expand_label_old {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ H.nodes) :
    (expand B H σ).label x = nextLabel B H σ x := by
  simp [expand, nextLabel, hx]

lemma expand_label_new {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {u : Node} (hu : u ∈ H.nodes) :
    (expand B H σ).label (u ++ [degree H.nodes u + 1]) =
      nextLabel B H σ u ∩ B.accepting := by
  have hnot : u ++ [degree H.nodes u + 1] ∉ H.nodes := newChild_notMem u
  have hin : u ++ [degree H.nodes u + 1] ∈
      H.nodes ∪ H.nodes.image (fun x => x ++ [degree H.nodes x + 1]) :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  dsimp only [expand]
  rw [if_neg hnot, if_pos hin, dropLast_append_singleton]
  rfl

lemma expand_label_new_eq_empty {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {u : Node} (hu : u ∈ H.nodes) {q0 : Q} (hacc : B.accepting = {q0})
    (hnot : q0 ∉ nextLabel B H σ u) :
    (expand B H σ).label (u ++ [degree H.nodes u + 1]) = ∅ := by
  rw [expand_label_new B H σ hu, hacc, Finset.inter_singleton_of_notMem hnot]

lemma expand_label_new_eq_singleton {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {u : Node} (hu : u ∈ H.nodes) {q0 : Q} (hacc : B.accepting = {q0})
    (hin : q0 ∈ nextLabel B H σ u) :
    (expand B H σ).label (u ++ [degree H.nodes u + 1]) = {q0} := by
  rw [expand_label_new B H σ hu, hacc]
  ext r
  simp only [Finset.mem_inter, Finset.mem_singleton]
  exact ⟨fun h => h.2, fun hr => ⟨hr ▸ hin, hr⟩⟩

lemma mem_own_iff {Q : Type} (H : TreeData Q) (x : Node) (q : Q) :
    q ∈ own H x ↔ q ∈ H.label x ∧ q ∉ childLabels H x := Finset.mem_sdiff

lemma mem_childLabels_iff {Q : Type} (H : TreeData Q) (x : Node) (q : Q) :
    q ∈ childLabels H x ↔ ∃ y ∈ children H.nodes x, q ∈ H.label y := Finset.mem_biUnion

lemma mem_mapData_label {Q R : Type} (H : TreeData Q) (π : Q → R) (x : Node) (r : R) :
    r ∈ (mapData H π).label x ↔ ∃ q ∈ H.label x, π q = r := Finset.mem_image

lemma mapData_label_empty {Q R : Type} (H : TreeData Q) (π : Q → R) {x : Node}
    (hx : H.label x = ∅) : (mapData H π).label x = ∅ := by
  simp [mapData, hx]

lemma mapData_label_singleton {Q R : Type} (H : TreeData Q) (π : Q → R) {x : Node} {s : Q}
    (hx : H.label x = {s}) : (mapData H π).label x = {π s} := by
  simp [mapData, hx]

lemma mem_nextLabel_iff {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    (x : Node) (r : Q) :
    r ∈ nextLabel B H σ x ↔ ∃ q ∈ H.label x, r ∈ B.delta q σ := Finset.mem_biUnion

lemma expand_label_outside {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∉ (expand B H σ).nodes) :
    (expand B H σ).label x = ∅ := by
  have hxH : x ∉ H.nodes := fun hm => hx (Finset.mem_union_left _ hm)
  dsimp only [expand] at hx ⊢
  rw [if_neg hxH, if_neg hx]

lemma mem_removeEmpty_nodes {Q : Type} (A : TreeData Q) (x : Node) :
    x ∈ (removeEmpty A).nodes ↔ x ∈ A.nodes ∧ (A.label x).Nonempty := by
  simp [removeEmpty]

lemma removeEmpty_label {Q : Type} (A : TreeData Q)
    (hout : ∀ x, x ∉ A.nodes → A.label x = ∅) (x : Node) :
    (removeEmpty A).label x = A.label x := by
  dsimp only [removeEmpty]
  split_ifs with h
  · rfl
  · by_cases hx : x ∈ A.nodes
    · have hnot_ne : ¬ (A.label x).Nonempty := fun hne => h (Finset.mem_filter.mpr ⟨hx, hne⟩)
      exact (Finset.not_nonempty_iff_eq_empty.mp hnot_ne).symm
    · exact (hout x hx).symm

lemma compress_eq_self_of_ordered {T : Finset Node} (hT : Ordered T)
    {x : Node} (hx : x ∈ T) : compress T x = x := by
  have hpx : Positive x := hT.1 x hx
  apply List.ext_getElem
  · simp [compress]
  · intro k h1 h2
    simp only [compress, List.getElem_map, List.getElem_range]
    rw [getElemBang_eq_getElem x k h2]
    have hxk_pos : 0 < x[k] := hpx x[k] (List.getElem_mem h2)
    have hpref_mem : x.take k ++ [x[k]] ∈ T :=
      hT.2.1 x hx _ (take_append_singleton_prefix x k h2)
    have hfilt : (T.filter fun y => ∃ j, y = x.take k ++ [j] ∧ j < x[k]) =
        (Finset.Icc 1 (x[k] - 1)).image (fun j => x.take k ++ [j]) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨hyT, j, rfl, hj_lt⟩
        have hj_pos : 0 < j := hT.1 _ hyT j (by simp)
        exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
      · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
        exact ⟨hT.2.2 (x.take k) x[k] hpref_mem j (by omega) (by omega), j, rfl, by omega⟩
    rw [hfilt, Finset.card_image_of_injective _ (fun a b h => (append_singleton_inj h).2)]
    rw [Nat.card_Icc]
    omega

lemma compressed_eq_self {Q : Type} {K : TreeData Q}
    (hord : Ordered K.nodes) (hout : ∀ x, x ∉ K.nodes → K.label x = ∅) :
    compressed K = K := by
  apply treeData_ext
  · ext x
    simp only [compressed, Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [compress_eq_self_of_ordered hord hy]
    · intro hx
      exact ⟨x, hx, compress_eq_self_of_ordered hord hx⟩
  · intro x
    simp only [compressed]
    by_cases hx : x ∈ K.nodes
    · have hfilt : (K.nodes.filter fun y => compress K.nodes y = x) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hy, heq⟩
          rwa [compress_eq_self_of_ordered hord hy] at heq
        · rintro rfl
          exact ⟨hx, compress_eq_self_of_ordered hord hx⟩
      rw [hfilt, Finset.singleton_biUnion]
    · have hfilt : (K.nodes.filter fun y => compress K.nodes y = x) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro y hy heq
        rw [compress_eq_self_of_ordered hord hy] at heq
        exact hx (heq ▸ hy)
      rw [hfilt, Finset.biUnion_empty, hout x hx]

lemma prune_eq_self_of_resetNodes_empty {Q : Type} {K : TreeData Q}
    (hres : resetNodes K = ∅) (hout : ∀ x, x ∉ K.nodes → K.label x = ∅) :
    prune K = K := by
  have hT : (K.nodes.filter fun x => ¬ ∃ p ∈ resetNodes K, p.IsPrefix x ∧ p ≠ x) = K.nodes := by
    rw [hres]
    simp
  apply treeData_ext
  · simpa [prune] using hT
  · intro x
    dsimp only [prune]
    rw [hT]
    by_cases hx : x ∈ K.nodes
    · simp [hx]
    · simp [hx, hout x hx]

lemma resetNodes_eq_empty_of_valid {Q : Type} {K : TreeData Q} (hv : Valid K) :
    resetNodes K = ∅ := by
  rw [resetNodes, Finset.filter_eq_empty_iff]
  intro x hx heq
  exact (hv.2.2.2.2.2 x hx).ne heq.symm

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

lemma split_incomparable :
    ∀ (x y : List ℕ), ¬ x.IsPrefix y → ¬ y.IsPrefix x →
      ∃ p i j u v, i ≠ j ∧ x = p ++ i :: u ∧ y = p ++ j :: v
  | [], _, hxy, _ => absurd List.nil_prefix hxy
  | _, [], _, hyx => absurd List.nil_prefix hyx
  | a :: xs, b :: ys, hxy, hyx => by
    by_cases hab : a = b
    · subst hab
      have hxy' : ¬ xs.IsPrefix ys := fun h => hxy (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      have hyx' : ¬ ys.IsPrefix xs := fun h => hyx (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      obtain ⟨p, i, j, u, v, hij, h1, h2⟩ := split_incomparable xs ys hxy' hyx'
      exact ⟨a :: p, i, j, u, v, hij, by simp [h1], by simp [h2]⟩
    · exact ⟨[], a, b, xs, ys, hab, rfl, rfl⟩

lemma own_disjoint {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x y : Node} (hx : x ∈ H.nodes) (hy : y ∈ H.nodes) (hne : x ≠ y) :
    Disjoint (own H x) (own H y) := by
  rw [Finset.disjoint_left]
  intro q hqx hqy
  by_cases hpre1 : x.IsPrefix y
  · obtain ⟨w, rfl⟩ := hpre1
    cases w with
    | nil => exact hne (by simp)
    | cons i rest =>
      have hxi : x ++ [i] ∈ H.nodes := hv.1.2.1 _ hy (x ++ [i]) ⟨rest, by simp⟩
      have hsub : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
        label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hy)
      have hqy' : q ∈ H.label ((x ++ [i]) ++ rest) := by simpa using (Finset.mem_sdiff.mp hqy).1
      have hch : q ∈ childLabels H x :=
        Finset.mem_biUnion.mpr ⟨x ++ [i], by simp [children, hxi], hsub hqy'⟩
      exact (Finset.mem_sdiff.mp hqx).2 hch
  · by_cases hpre2 : y.IsPrefix x
    · obtain ⟨w, rfl⟩ := hpre2
      cases w with
      | nil => exact hne (by simp)
      | cons i rest =>
        have hyi : y ++ [i] ∈ H.nodes := hv.1.2.1 _ hx (y ++ [i]) ⟨rest, by simp⟩
        have hsub : H.label ((y ++ [i]) ++ rest) ⊆ H.label (y ++ [i]) :=
          label_sub_of_prefix hv (y ++ [i]) rest (by simpa using hx)
        have hqx' : q ∈ H.label ((y ++ [i]) ++ rest) := by simpa using (Finset.mem_sdiff.mp hqx).1
        have hch : q ∈ childLabels H y :=
          Finset.mem_biUnion.mpr ⟨y ++ [i], by simp [children, hyi], hsub hqx'⟩
        exact (Finset.mem_sdiff.mp hqy).2 hch
    · obtain ⟨p, i, j, u, v, hij, rfl, rfl⟩ := split_incomparable x y hpre1 hpre2
      have hpi : p ++ [i] ∈ H.nodes := hv.1.2.1 _ hx (p ++ [i]) ⟨u, by simp⟩
      have hpj : p ++ [j] ∈ H.nodes := hv.1.2.1 _ hy (p ++ [j]) ⟨v, by simp⟩
      have hqx' : q ∈ H.label ((p ++ [i]) ++ u) := by simpa using (Finset.mem_sdiff.mp hqx).1
      have hqy' : q ∈ H.label ((p ++ [j]) ++ v) := by simpa using (Finset.mem_sdiff.mp hqy).1
      have h1 : q ∈ H.label (p ++ [i]) :=
        label_sub_of_prefix hv (p ++ [i]) u (by simpa using hx) hqx'
      have h2 : q ∈ H.label (p ++ [j]) :=
        label_sub_of_prefix hv (p ++ [j]) v (by simpa using hy) hqy'
      exact Finset.disjoint_left.mp (hv.2.2.2.2.1 p i j hpi hpj hij) h1 h2

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

lemma label_sub_stateSet {Q : Type} {H : TreeData Q} (hv : Valid H) (x : Node) :
    H.label x ⊆ stateSet H := by
  by_cases hx : x ∈ H.nodes
  · simpa [stateSet] using label_sub_of_prefix hv [] x (by simpa using hx)
  · simp [hv.2.2.1 x hx]

lemma owner_spec {Q : Type} {H : TreeData Q} (hv : Valid H)
    {p : Q} (hp : p ∈ stateSet H) :
    owner H p ∈ H.nodes ∧ p ∈ own H (owner H p) := by
  have hroot : [] ∈ H.nodes := hv.2.1
  have hp' : p ∈ H.label [] := hp
  rw [label_eq_biUnion_own hv hroot] at hp'
  obtain ⟨y, hy_filt, hpy⟩ := Finset.mem_biUnion.mp hp'
  have hex : ∃ x ∈ H.nodes, p ∈ own H x := ⟨y, (Finset.mem_filter.mp hy_filt).1, hpy⟩
  unfold owner
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma own_mem_iff_eq_owner {Q : Type} {H : TreeData Q} (hv : Valid H)
    {p : Q} (hp : p ∈ stateSet H) {u : Node} (hu : u ∈ H.nodes) :
    p ∈ own H u ↔ u = owner H p := by
  obtain ⟨hwM, hpw⟩ := owner_spec hv hp
  constructor
  · intro hpu
    by_contra hne
    exact Finset.disjoint_left.mp (own_disjoint hv hu hwM hne) hpu hpw
  · rintro rfl
    exact hpw

lemma mem_label_iff_prefix_owner {Q : Type} {H : TreeData Q} (hv : Valid H)
    {p : Q} (hp : p ∈ stateSet H) (x : Node) :
    p ∈ H.label x ↔ x.IsPrefix (owner H p) := by
  obtain ⟨hwM, _⟩ := owner_spec hv hp
  by_cases hx : x ∈ H.nodes
  · rw [label_eq_biUnion_own hv hx, Finset.mem_biUnion]
    constructor
    · rintro ⟨y, hy_filt, hpy⟩
      obtain ⟨hyM, hxy⟩ := Finset.mem_filter.mp hy_filt
      rwa [(own_mem_iff_eq_owner hv hp hyM).mp hpy] at hxy
    · intro hxw
      exact ⟨owner H p, Finset.mem_filter.mpr ⟨hwM, hxw⟩, (owner_spec hv hp).2⟩
  · constructor
    · intro hpx
      rw [hv.2.2.1 x hx] at hpx
      simp at hpx
    · intro hxw
      exact absurd (hv.1.2.1 _ hwM x hxw) hx

lemma own_eq_label_of_leaf {Q : Type} {H : TreeData Q} {x : Node}
    (hleaf : Leaf H.nodes x) : own H x = H.label x := by
  simp [own, childLabels, hleaf.2]

def ownState {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H) (u : Node) : Fin n :=
  if hu : u ∈ H.val.nodes then Classical.choose (Finset.card_eq_one.mp (hH u hu)) else ⟨0, by omega⟩

lemma own_eq_singleton_ownState {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    {u : Node} (hu : u ∈ H.val.nodes) :
    own H.val u = {ownState hn H hH u} := by
  unfold ownState
  rw [dif_pos hu]
  exact Classical.choose_spec (Finset.card_eq_one.mp (hH u hu))

lemma ownState_mem_stateSet {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    {u : Node} (hu : u ∈ H.val.nodes) :
    ownState hn H hH u ∈ stateSet H.val := by
  have hmem : ownState hn H hH u ∈ own H.val u := by
    rw [own_eq_singleton_ownState hn H hH hu]
    simp
  exact label_sub_stateSet H.property u ((mem_own_iff H.val u _).mp hmem).1

lemma ownState_injOn {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H) :
    Set.InjOn (ownState hn H hH) {u | u ∈ H.val.nodes} := by
  intro u1 hu1 u2 hu2 heq
  by_contra hne
  have h1 : ownState hn H hH u1 ∈ own H.val u1 := by
    rw [own_eq_singleton_ownState hn H hH hu1]; simp
  have h2 : ownState hn H hH u1 ∈ own H.val u2 := by
    rw [heq, own_eq_singleton_ownState hn H hH hu2]; simp
  exact Finset.disjoint_left.mp (own_disjoint H.property hu1 hu2 hne) h1 h2

lemma mem_label_iff_own_poly {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x : Node} (hx : x ∈ H.nodes) (q : Q) :
    q ∈ H.label x ↔ ∃ y ∈ H.nodes, x.IsPrefix y ∧ q ∈ own H y := by
  rw [label_eq_biUnion_own hv hx, Finset.mem_biUnion]
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨y, ⟨hyM, hxy⟩, hqy⟩ => ⟨y, hyM, hxy, hqy⟩,
    fun ⟨y, hyM, hxy, hqy⟩ => ⟨y, ⟨hyM, hxy⟩, hqy⟩⟩

lemma mem_label_iff_ownState {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    {x : Node} (hx : x ∈ H.val.nodes) (q : Fin n) :
    q ∈ H.val.label x ↔ ∃ y ∈ H.val.nodes, x.IsPrefix y ∧ ownState hn H hH y = q := by
  rw [mem_label_iff_own_poly H.property hx q]
  constructor
  · rintro ⟨y, hyM, hxy, hqy⟩
    rw [own_eq_singleton_ownState hn H hH hyM, Finset.mem_singleton] at hqy
    exact ⟨y, hyM, hxy, hqy.symm⟩
  · rintro ⟨y, hyM, hxy, rfl⟩
    refine ⟨y, hyM, hxy, ?_⟩
    rw [own_eq_singleton_ownState hn H hH hyM]
    simp

lemma valid_and_own_of_fn {Q : Type} (K : TreeData Q) (f : Node → Q)
    (hord : Ordered K.nodes) (hroot : [] ∈ K.nodes)
    (hinj : Set.InjOn f {u | u ∈ K.nodes})
    (hl_in : ∀ x ∈ K.nodes, ∀ q, q ∈ K.label x ↔ ∃ y ∈ K.nodes, x.IsPrefix y ∧ f y = q)
    (hl_out : ∀ x, x ∉ K.nodes → K.label x = ∅) :
    Valid K ∧ (∀ x ∈ K.nodes, own K x = {f x}) := by
  have hchild_mem : ∀ x ∈ K.nodes, ∀ q,
      q ∈ childLabels K x ↔ ∃ y ∈ K.nodes, x.IsPrefix y ∧ y ≠ x ∧ f y = q := by
    intro x hx q
    simp only [childLabels, children, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨c, ⟨hcK, i, rfl⟩, hqc⟩
      obtain ⟨y, hyK, ⟨rest, rfl⟩, rfl⟩ := (hl_in (x ++ [i]) hcK q).mp hqc
      refine ⟨(x ++ [i]) ++ rest, hyK, ⟨[i] ++ rest, by simp⟩, ?_, rfl⟩
      intro heq
      have := congrArg List.length heq
      simp at this
    · rintro ⟨y, hyK, ⟨w, rfl⟩, hne, rfl⟩
      cases w with
      | nil => exact absurd (by simp) hne
      | cons i rest =>
        have hxi_K : x ++ [i] ∈ K.nodes := hord.2.1 _ hyK (x ++ [i]) ⟨rest, by simp⟩
        refine ⟨x ++ [i], ⟨hxi_K, i, rfl⟩, ?_⟩
        exact (hl_in (x ++ [i]) hxi_K (f (x ++ i :: rest))).mpr
          ⟨x ++ i :: rest, hyK, ⟨rest, by simp⟩, rfl⟩
  have hown : ∀ x ∈ K.nodes, own K x = {f x} := by
    intro x hx
    ext q
    rw [own, Finset.mem_sdiff, hl_in x hx q, hchild_mem x hx q, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨y, hyK, hxy, rfl⟩, hnot⟩
      by_contra hfq
      have hne : y ≠ x := fun h => hfq (congrArg f h)
      exact hnot ⟨y, hyK, hxy, hne, rfl⟩
    · rintro rfl
      refine ⟨⟨x, hx, List.prefix_refl x, rfl⟩, ?_⟩
      rintro ⟨y, hyK, _, hne, hfy⟩
      exact hne (hinj hyK hx hfy)
  refine ⟨⟨hord, hroot, hl_out, ?_, ?_, ?_⟩, hown⟩
  · intro x hx
    exact ⟨f x, (hl_in x hx (f x)).mpr ⟨x, hx, List.prefix_refl x, rfl⟩⟩
  · intro p i j hpi hpj hij
    rw [Finset.disjoint_left]
    intro q hqi hqj
    obtain ⟨y1, hy1K, hp1, rfl⟩ := (hl_in (p ++ [i]) hpi q).mp hqi
    obtain ⟨y2, hy2K, hp2, hfy⟩ := (hl_in (p ++ [j]) hpj (f y1)).mp hqj
    have hy_eq : y1 = y2 := hinj hy1K hy2K hfy.symm
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
    · intro q hq
      obtain ⟨y, hyK, hxy, _, rfl⟩ := (hchild_mem x hx q).mp hq
      exact (hl_in x hx (f y)).mpr ⟨y, hyK, hxy, rfl⟩
    · intro heq
      have hfx : f x ∈ own K x := by rw [hown x hx]; simp
      rw [own, heq, Finset.sdiff_self] at hfx
      simp at hfx

lemma stage4_eq_of_next {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n))
    (σ : Letter n) (K : TreeData (Fin n))
    (hvK : Valid K) (hsub : K.nodes ⊆ H.val.nodes)
    (hnext : ∀ x : Node, nextLabel (fullBuchi n hn) H.val σ x = K.label x)
    (hno_acc : lastState n hn ∉ K.label []) :
    stage4 (fullBuchi n hn) H.val σ = K ∧
    resetNodes (stage3 (fullBuchi n hn) H.val σ) = ∅ := by
  classical
  have hqn_not_K : ∀ x : Node, lastState n hn ∉ K.label x :=
    fun x hmem => hno_acc (label_sub_stateSet hvK x hmem)
  have hE_lbl : ∀ x : Node, (expand (fullBuchi n hn) H.val σ).label x = K.label x := by
    intro x
    by_cases hx : x ∈ H.val.nodes
    · rw [expand_label_old _ _ _ hx, hnext x]
    · rw [hvK.2.2.1 x (fun hK => hx (hsub hK))]
      by_cases hxE : x ∈ (expand (fullBuchi n hn) H.val σ).nodes
      · rw [expand_nodes, Finset.mem_union] at hxE
        rcases hxE with hxH | hxImg
        · exact absurd hxH hx
        · obtain ⟨u, huH, rfl⟩ := Finset.mem_image.mp hxImg
          apply expand_label_new_eq_empty _ _ _ huH rfl
          rw [hnext u]
          exact hqn_not_K u
      · exact expand_label_outside _ _ _ hxE
  have hH_lbl : ∀ x : Node, (horizontal (expand (fullBuchi n hn) H.val σ)).label x = K.label x := by
    intro x
    dsimp only [horizontal]
    rw [hE_lbl x, Finset.filter_eq_self]
    rintro q hq ⟨p, i, v, j, rfl, hj0, hji, hpjE, hqpj⟩
    rw [hE_lbl (p ++ [j])] at hqpj
    have hxK : p ++ i :: v ∈ K.nodes := by
      by_contra hnot
      rw [hvK.2.2.1 _ hnot] at hq
      simp at hq
    have hpjK : p ++ [j] ∈ K.nodes := by
      by_contra hnot
      rw [hvK.2.2.1 _ hnot] at hqpj
      simp at hqpj
    have hpiK : p ++ [i] ∈ K.nodes := hvK.1.2.1 _ hxK (p ++ [i]) ⟨v, by simp⟩
    have hxK' : (p ++ [i]) ++ v ∈ K.nodes := by simpa using hxK
    have hq' : q ∈ K.label ((p ++ [i]) ++ v) := by simpa using hq
    have hqpi : q ∈ K.label (p ++ [i]) := label_sub_of_prefix hvK (p ++ [i]) v hxK' hq'
    exact Finset.disjoint_left.mp (hvK.2.2.2.2.1 p i j hpiK hpjK (by omega)) hqpi hqpj
  have hH_out : ∀ x, x ∉ (horizontal (expand (fullBuchi n hn) H.val σ)).nodes →
      (horizontal (expand (fullBuchi n hn) H.val σ)).label x = ∅ := by
    intro x hx
    rw [hH_lbl x]
    exact hvK.2.2.1 x (fun hK => hx (Finset.mem_union_left _ (hsub hK)))
  have hS3_nodes : (stage3 (fullBuchi n hn) H.val σ).nodes = K.nodes := by
    ext x
    rw [stage3, mem_removeEmpty_nodes, hH_lbl x]
    constructor
    · rintro ⟨_, hne⟩
      by_contra hnot
      rw [hvK.2.2.1 x hnot] at hne
      simp at hne
    · intro hxK
      exact ⟨Finset.mem_union_left _ (hsub hxK), hvK.2.2.2.1 x hxK⟩
  have hS3 : stage3 (fullBuchi n hn) H.val σ = K := by
    apply treeData_ext hS3_nodes
    intro x
    rw [stage3, removeEmpty_label _ hH_out x, hH_lbl x]
  have hres : resetNodes (stage3 (fullBuchi n hn) H.val σ) = ∅ := by
    rw [hS3]
    exact resetNodes_eq_empty_of_valid hvK
  refine ⟨?_, hres⟩
  unfold stage4
  rw [hS3]
  exact prune_eq_self_of_resetNodes_empty (resetNodes_eq_empty_of_valid hvK) hvK.2.2.1

lemma effect_from_stage4 {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n))
    (σ : Letter n) (K : TreeData (Fin n)) (a : Finset Node)
    (hvK : Valid K) (hown_card : ∀ x ∈ K.nodes, (own K x).card = 1)
    (hs4 : stage4 (fullBuchi n hn) H.val σ = K)
    (hacc : acceptingNodes (fullBuchi n hn) H σ = a) :
    Effect hn H σ K a (H.val.nodes \ K.nodes) := by
  have hcomp : compressed (stage4 (fullBuchi n hn) H.val σ) = K := by
    rw [hs4]
    exact compressed_eq_self hvK.1 hvK.2.2.1
  have hsucc : successor (fullBuchi n hn) H σ = some ⟨K, hvK⟩ := by
    unfold successor
    rw [hcomp]
    simp [asHistory, hvK]
  refine ⟨⟨K, hvK⟩, hsucc, rfl, hown_card, hacc, ?_⟩
  ext x
  simp only [unstable, hs4, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hxH, hxK | hc⟩
    · exact ⟨hxH, hxK⟩
    · by_cases hxK : x ∈ K.nodes
      · exact absurd (compress_eq_self_of_ordered hvK.1 hxK) hc
      · exact ⟨hxH, hxK⟩
  · rintro ⟨hxH, hxK⟩
    exact ⟨hxH, Or.inl hxK⟩

lemma ordered_insert_newChild {M : Finset Node} (hM : Ordered M)
    {w : Node} (hw : w ∈ M) :
    Ordered (insert (w ++ [degree M w + 1]) M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxM
    · intro k hk
      simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with hkw | rfl
      · exact hM.1 w hw k hkw
      · omega
    · exact hM.1 x hxM
  · intro x hx p hp
    rcases Finset.mem_insert.mp hx with rfl | hxM
    · obtain ⟨t, ht⟩ := hp
      cases t using List.reverseRecOn with
      | nil =>
        simp at ht
        subst ht
        exact Finset.mem_insert_self _ M
      | append_singleton rest b =>
        rw [← List.append_assoc] at ht
        obtain ⟨hp_rest, _⟩ := append_singleton_inj ht
        exact Finset.mem_insert_of_mem (hM.2.1 w hw p ⟨rest, hp_rest⟩)
    · exact Finset.mem_insert_of_mem (hM.2.1 x hxM p hp)
  · intro p i hpi j hj0 hji
    rcases Finset.mem_insert.mp hpi with heq | hpiM
    · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      by_cases hjeq : j = degree M p + 1
      · subst hjeq
        exact Finset.mem_insert_self _ M
      · have hj_le : j ≤ degree M p := by omega
        have hd_pos : 0 < degree M p := by omega
        have hpd : p ++ [degree M p] ∈ M := mem_of_degree_pos hd_pos
        exact Finset.mem_insert_of_mem (hM.2.2 p (degree M p) hpd j hj0 hj_le)
    · exact Finset.mem_insert_of_mem (hM.2.2 p i hpiM j hj0 hji)

lemma ordered_erase_leaf_youngest {M : Finset Node} (hM : Ordered M)
    {z : Node} (hleaf : Leaf M z) (hyng : Youngest M z) :
    Ordered (M.erase z) ∧ [] ∈ M.erase z := by
  obtain ⟨p0, i0, rfl, hi0_pos, hi0_deg⟩ := hyng
  have hz_ne_nil : p0 ++ [i0] ≠ [] := by simp
  refine ⟨⟨?_, ?_, ?_⟩, Finset.mem_erase.mpr ⟨hz_ne_nil.symm, ?_⟩⟩
  · intro x hx
    exact hM.1 x (Finset.mem_erase.mp hx).2
  · intro x hx q hqx
    obtain ⟨hxz, hxM⟩ := Finset.mem_erase.mp hx
    have hqM : q ∈ M := hM.2.1 x hxM q hqx
    refine Finset.mem_erase.mpr ⟨?_, hqM⟩
    intro hqz
    subst hqz
    obtain ⟨t, rfl⟩ := hqx
    cases t with
    | nil => exact hxz (by simp)
    | cons k rest =>
      have hk_mem : (p0 ++ [i0]) ++ [k] ∈ M :=
        hM.2.1 _ hxM ((p0 ++ [i0]) ++ [k]) ⟨rest, by simp⟩
      have hk_ch : (p0 ++ [i0]) ++ [k] ∈ children M (p0 ++ [i0]) := by
        rw [children, Finset.mem_filter]
        exact ⟨hk_mem, k, rfl⟩
      rw [hleaf.2] at hk_ch
      simp at hk_ch
  · intro q k hqk j hj0 hjk
    obtain ⟨hqk_ne, hqkM⟩ := Finset.mem_erase.mp hqk
    have hqjM : q ++ [j] ∈ M := hM.2.2 q k hqkM j hj0 hjk
    refine Finset.mem_erase.mpr ⟨?_, hqjM⟩
    intro heq
    obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
    have hk_le : k ≤ degree M q := le_degree_of_mem hqkM
    have hkj : k = j := by omega
    subst hkj
    exact hqk_ne rfl
  · exact hM.2.1 (p0 ++ [i0]) hleaf.1 [] List.nil_prefix

lemma mapData_valid_and_own {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    (π : Fin n → Fin n) (hinj : Set.InjOn π {q | q ∈ stateSet H.val}) :
    Valid (mapData H.val π) ∧
    (∀ u ∈ H.val.nodes, own (mapData H.val π) u = {π (ownState hn H hH u)}) := by
  classical
  let f : Node → Fin n := fun u => π (ownState hn H hH u)
  apply valid_and_own_of_fn (mapData H.val π) f H.property.1 H.property.2.1
  · intro u1 hu1 u2 hu2 hfeq
    have hs1 : ownState hn H hH u1 ∈ stateSet H.val := ownState_mem_stateSet hn H hH hu1
    have hs2 : ownState hn H hH u2 ∈ stateSet H.val := ownState_mem_stateSet hn H hH hu2
    exact ownState_injOn hn H hH hu1 hu2 (hinj hs1 hs2 hfeq)
  · intro x hx q
    rw [mem_mapData_label]
    constructor
    · rintro ⟨r, hrx, rfl⟩
      obtain ⟨y, hyM, hxy, rfl⟩ := (mem_label_iff_ownState hn H hH hx r).mp hrx
      exact ⟨y, hyM, hxy, rfl⟩
    · rintro ⟨y, hyM, hxy, rfl⟩
      exact ⟨ownState hn H hH y, (mem_label_iff_ownState hn H hH hx _).mpr ⟨y, hyM, hxy, rfl⟩, rfl⟩
  · intro x hx
    exact mapData_label_empty H.val π (H.property.2.2.1 x hx)

lemma delta_permLetter {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n))
    (π : Fin n → Fin n) (u : Node) :
    nextLabel (fullBuchi n hn) H.val (permLetter (stateSet H.val) π) u =
      (mapData H.val π).label u := by
  have hLP : H.val.label u ⊆ stateSet H.val := label_sub_stateSet H.property u
  ext r
  rw [mem_nextLabel_iff, mem_mapData_label]
  simp only [fullBuchi, permLetter, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨q, hqL, p, _, heq⟩
    obtain ⟨hpq, hpr⟩ := Prod.mk.inj heq
    subst p
    exact ⟨q, hqL, hpr⟩
  · rintro ⟨q, hqL, rfl⟩
    exact ⟨q, hqL, q, hLP hqL, rfl⟩

lemma case_gen (n : ℕ) (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    {p : Fin n} (hp : p ∈ stateSet H.val) (hqn : lastState n hn ∉ stateSet H.val) :
    Effect hn H (genLetter hn (stateSet H.val) p) (generatedData hn H.val p) ∅ ∅ ∧
    (∀ x ∈ H.val.nodes, own (generatedData hn H.val p) x = own H.val x) ∧
    (generatedData hn H.val p).label
      (owner H.val p ++ [degree H.val.nodes (owner H.val p) + 1]) = {lastState n hn} := by
  classical
  let w := owner H.val p
  let z := w ++ [degree H.val.nodes w + 1]
  obtain ⟨hwM, _⟩ := owner_spec H.property hp
  have hz_notM : z ∉ H.val.nodes := newChild_notMem w
  have hordK : Ordered (generatedData hn H.val p).nodes := ordered_insert_newChild H.property.1 hwM
  have hrootK : [] ∈ (generatedData hn H.val p).nodes := Finset.mem_insert_of_mem H.property.2.1
  let f : Node → Fin n := fun u => if u = z then lastState n hn else ownState hn H hH u
  have hinj_f : Set.InjOn f {u | u ∈ (generatedData hn H.val p).nodes} := by
    intro u1 hu1 u2 hu2 hfeq
    change u1 ∈ insert z H.val.nodes at hu1
    change u2 ∈ insert z H.val.nodes at hu2
    rcases Finset.mem_insert.mp hu1 with h1z | hu1M <;> rcases Finset.mem_insert.mp hu2 with h2z | hu2M
    · rw [h1z, h2z]
    · subst h1z
      have hne2 : u2 ≠ z := fun h => hz_notM (h ▸ hu2M)
      dsimp only [f] at hfeq
      rw [if_pos rfl, if_neg hne2] at hfeq
      exact absurd (hfeq ▸ ownState_mem_stateSet hn H hH hu2M) hqn
    · subst h2z
      have hne1 : u1 ≠ z := fun h => hz_notM (h ▸ hu1M)
      dsimp only [f] at hfeq
      rw [if_neg hne1, if_pos rfl] at hfeq
      exact absurd (hfeq.symm ▸ ownState_mem_stateSet hn H hH hu1M) hqn
    · have hne1 : u1 ≠ z := fun h => hz_notM (h ▸ hu1M)
      have hne2 : u2 ≠ z := fun h => hz_notM (h ▸ hu2M)
      dsimp only [f] at hfeq
      rw [if_neg hne1, if_neg hne2] at hfeq
      exact ownState_injOn hn H hH hu1M hu2M hfeq
  have hlK_in : ∀ x ∈ (generatedData hn H.val p).nodes, ∀ q,
      q ∈ (generatedData hn H.val p).label x ↔
        ∃ y ∈ (generatedData hn H.val p).nodes, x.IsPrefix y ∧ f y = q := by
    intro x hx q
    change x ∈ insert z H.val.nodes at hx
    dsimp only [generatedData]
    change q ∈ H.val.label x ∪ (if x.IsPrefix z then {lastState n hn} else ∅) ↔
      ∃ y ∈ insert z H.val.nodes, x.IsPrefix y ∧ f y = q
    rcases Finset.mem_insert.mp hx with hxz | hxM
    · subst hxz
      rw [H.property.2.2.1 z hz_notM, Finset.empty_union, if_pos (List.prefix_refl z),
        Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨z, Finset.mem_insert_self _ _, List.prefix_refl z, by simp [f]⟩
      · rintro ⟨y, hy_ins, hzy, rfl⟩
        rcases Finset.mem_insert.mp hy_ins with hyz | hyM
        · subst hyz; simp [f]
        · exact absurd (H.property.1.2.1 y hyM z hzy) hz_notM
    · rw [Finset.mem_union, mem_label_iff_ownState hn H hH hxM q]
      constructor
      · rintro (⟨y, hyM, hxy, rfl⟩ | hqz)
        · have hyz : y ≠ z := fun h => hz_notM (h ▸ hyM)
          exact ⟨y, Finset.mem_insert_of_mem hyM, hxy, by simp [f, hyz]⟩
        · split_ifs at hqz with hxz
          · rw [Finset.mem_singleton] at hqz
            subst hqz
            exact ⟨z, Finset.mem_insert_self _ _, hxz, by simp [f]⟩
          · simp at hqz
      · rintro ⟨y, hy_ins, hxy, rfl⟩
        rcases Finset.mem_insert.mp hy_ins with hyz | hyM
        · subst hyz
          right
          simp [f, hxy]
        · left
          have hyz : y ≠ z := fun h => hz_notM (h ▸ hyM)
          exact ⟨y, hyM, hxy, by simp [f, hyz]⟩
  have hlK_out : ∀ x, x ∉ (generatedData hn H.val p).nodes → (generatedData hn H.val p).label x = ∅ := by
    intro x hx
    have hxM : x ∉ H.val.nodes := fun hm => hx (Finset.mem_insert_of_mem hm)
    have hxz : ¬ x.IsPrefix z :=
      fun hp => hx (hordK.2.1 z (Finset.mem_insert_self _ _) x hp)
    dsimp only [generatedData]
    change H.val.label x ∪ (if x.IsPrefix z then {lastState n hn} else ∅) = ∅
    rw [H.property.2.2.1 x hxM, if_neg hxz, Finset.empty_union]
  obtain ⟨hvK, hownK⟩ := valid_and_own_of_fn (generatedData hn H.val p) f hordK hrootK hinj_f hlK_in hlK_out
  have hprefix_wz : ∀ u ∈ H.val.nodes, (u.IsPrefix w ↔ u.IsPrefix z) := by
    intro u huM
    constructor
    · rintro ⟨t, htw⟩
      exact ⟨t ++ [degree H.val.nodes w + 1], by dsimp only [z]; rw [← htw, List.append_assoc]⟩
    · rintro ⟨t, ht⟩
      cases t using List.reverseRecOn with
      | nil =>
        simp at ht
        exact absurd (ht ▸ huM) hz_notM
      | append_singleton rest b =>
        dsimp only [z] at ht
        rw [← List.append_assoc] at ht
        obtain ⟨huw, _⟩ := append_singleton_inj ht
        exact ⟨rest, huw⟩
  have hnext_M : ∀ u ∈ H.val.nodes,
      nextLabel (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p) u =
        (generatedData hn H.val p).label u := by
    intro u huM
    have hu_sub : H.val.label u ⊆ stateSet H.val := label_sub_stateSet H.property u
    have hp_iff : p ∈ H.val.label u ↔ u.IsPrefix z := by
      rw [mem_label_iff_prefix_owner H.property hp u]
      exact hprefix_wz u huM
    ext r
    rw [mem_nextLabel_iff]
    dsimp only [generatedData]
    change (∃ q ∈ H.val.label u, r ∈ (fullBuchi n hn).delta q (genLetter hn (stateSet H.val) p)) ↔
      r ∈ H.val.label u ∪ (if u.IsPrefix z then {lastState n hn} else ∅)
    simp only [fullBuchi, genLetter, idLetter, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image, Finset.mem_union]
    constructor
    · rintro ⟨q, hqu, heq | ⟨q', _, heq⟩⟩
      · obtain ⟨hq_eq, hr_eq⟩ := Prod.mk.inj heq
        subst q; subst r
        right
        rw [if_pos (hp_iff.mp hqu)]
        simp [lastState]
      · obtain ⟨hq_eq, hr_eq⟩ := Prod.mk.inj heq
        subst q'; subst r
        exact Or.inl hqu
    · rintro (hru | hrz)
      · exact ⟨r, hru, Or.inr ⟨r, hu_sub hru, rfl⟩⟩
      · split_ifs at hrz with huz
        · rw [Finset.mem_singleton] at hrz
          subst r
          exact ⟨p, hp_iff.mpr huz, Or.inl rfl⟩
        · simp at hrz
  have hE_new : ∀ u ∈ H.val.nodes,
      (expand (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p)).label
        (u ++ [degree H.val.nodes u + 1]) = if u.IsPrefix w then {lastState n hn} else ∅ := by
    intro u huM
    have hqn_not_u : lastState n hn ∉ H.val.label u :=
      fun h => hqn (label_sub_stateSet H.property u h)
    by_cases huw : u.IsPrefix w
    · rw [if_pos huw]
      apply expand_label_new_eq_singleton _ _ _ huM rfl
      rw [hnext_M u huM]
      have huz : u.IsPrefix z := (hprefix_wz u huM).mp huw
      dsimp only [generatedData]
      change lastState n hn ∈ H.val.label u ∪ (if u.IsPrefix z then {lastState n hn} else ∅)
      rw [if_pos huz]
      simp
    · rw [if_neg huw]
      apply expand_label_new_eq_empty _ _ _ huM rfl
      rw [hnext_M u huM]
      have huz : ¬ u.IsPrefix z := fun h => huw ((hprefix_wz u huM).mpr h)
      dsimp only [generatedData]
      change lastState n hn ∉ H.val.label u ∪ (if u.IsPrefix z then {lastState n hn} else ∅)
      rw [if_neg huz, Finset.union_empty]
      exact hqn_not_u
  let E := expand (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p)
  have hH_lbl : ∀ x : Node, (horizontal E).label x = (generatedData hn H.val p).label x := by
    intro x
    by_cases hxM : x ∈ H.val.nodes
    · dsimp only [horizontal, E]
      rw [expand_label_old _ _ _ hxM, hnext_M x hxM, Finset.filter_eq_self]
      rintro q hq ⟨p0, i, v, j, rfl, hj0, hji, hpjE, hqpj⟩
      have hpiM : p0 ++ [i] ∈ H.val.nodes := H.property.1.2.1 _ hxM (p0 ++ [i]) ⟨v, by simp⟩
      have hi_le : i ≤ degree H.val.nodes p0 := le_degree_of_mem hpiM
      have hpjM : p0 ++ [j] ∈ H.val.nodes := by
        rw [expand_nodes, Finset.mem_union] at hpjE
        rcases hpjE with hm | himg
        · exact hm
        · obtain ⟨u, _, heq⟩ := Finset.mem_image.mp himg
          obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
          omega
      rw [expand_label_old _ _ _ hpjM, hnext_M (p0 ++ [j]) hpjM] at hqpj
      have hpiK : p0 ++ [i] ∈ (generatedData hn H.val p).nodes := Finset.mem_insert_of_mem hpiM
      have hpjK : p0 ++ [j] ∈ (generatedData hn H.val p).nodes := Finset.mem_insert_of_mem hpjM
      have hxK' : (p0 ++ [i]) ++ v ∈ (generatedData hn H.val p).nodes :=
        Finset.mem_insert_of_mem (by simpa using hxM)
      have hq' : q ∈ (generatedData hn H.val p).label ((p0 ++ [i]) ++ v) := by simpa using hq
      have hqpi : q ∈ (generatedData hn H.val p).label (p0 ++ [i]) :=
        label_sub_of_prefix hvK (p0 ++ [i]) v hxK' hq'
      exact Finset.disjoint_left.mp (hvK.2.2.2.2.1 p0 i j hpiK hpjK (by omega)) hqpi hqpj
    · by_cases hxz : x = z
      · subst hxz
        have hzK_lbl : (generatedData hn H.val p).label z = {lastState n hn} := by
          dsimp only [generatedData]
          change H.val.label z ∪ (if z.IsPrefix z then {lastState n hn} else ∅) = {lastState n hn}
          rw [H.property.2.2.1 z hz_notM, if_pos (List.prefix_refl z), Finset.empty_union]
        have hzE_lbl : E.label z = {lastState n hn} := by
          dsimp only [E, z]
          rw [hE_new w hwM, if_pos (List.prefix_refl w)]
        dsimp only [horizontal]
        rw [hzE_lbl, hzK_lbl, Finset.filter_eq_self]
        rintro q hq ⟨p0, i, v, j, hzeq, hj0, hji, hpjE, hqpj⟩
        rw [Finset.mem_singleton] at hq
        subst hq
        cases v using List.reverseRecOn with
        | nil =>
          dsimp only [z] at hzeq
          obtain ⟨hw_eq, hi_eq⟩ := append_singleton_inj hzeq
          subst p0
          have hpjM : w ++ [j] ∈ H.val.nodes := by
            dsimp only [E] at hpjE
            rw [expand_nodes, Finset.mem_union] at hpjE
            rcases hpjE with hm | himg
            · exact hm
            · obtain ⟨u, _, heq⟩ := Finset.mem_image.mp himg
              obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
              omega
          dsimp only [E] at hqpj
          rw [expand_label_old _ _ _ hpjM, hnext_M (w ++ [j]) hpjM] at hqpj
          dsimp only [generatedData] at hqpj
          change lastState n hn ∈ H.val.label (w ++ [j]) ∪
            (if (w ++ [j]).IsPrefix z then {lastState n hn} else ∅) at hqpj
          rcases Finset.mem_union.mp hqpj with h1 | h2
          · exact hqn (label_sub_stateSet H.property _ h1)
          · split_ifs at h2 with hpjz
            · have hpjw : (w ++ [j]).IsPrefix w := (hprefix_wz (w ++ [j]) hpjM).mpr hpjz
              have := hpjw.length_le
              simp at this
            · simp at h2
        | append_singleton rest b =>
          rw [show p0 ++ i :: (rest ++ [b]) = (p0 ++ i :: rest) ++ [b] by simp] at hzeq
          dsimp only [z] at hzeq
          obtain ⟨hw_eq, _⟩ := append_singleton_inj hzeq
          have hpi_pref_w : (p0 ++ [i]).IsPrefix w := ⟨rest, by simpa using hw_eq.symm⟩
          have hpiM : p0 ++ [i] ∈ H.val.nodes := H.property.1.2.1 w hwM (p0 ++ [i]) hpi_pref_w
          have hi_le : i ≤ degree H.val.nodes p0 := le_degree_of_mem hpiM
          have hpjM : p0 ++ [j] ∈ H.val.nodes := by
            dsimp only [E] at hpjE
            rw [expand_nodes, Finset.mem_union] at hpjE
            rcases hpjE with hm | himg
            · exact hm
            · obtain ⟨u, _, heq⟩ := Finset.mem_image.mp himg
              obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
              omega
          dsimp only [E] at hqpj
          rw [expand_label_old _ _ _ hpjM, hnext_M (p0 ++ [j]) hpjM] at hqpj
          have hpi_pref_z : (p0 ++ [i]).IsPrefix z := (hprefix_wz (p0 ++ [i]) hpiM).mp hpi_pref_w
          have hqpi : lastState n hn ∈ (generatedData hn H.val p).label (p0 ++ [i]) := by
            dsimp only [generatedData]
            change lastState n hn ∈ H.val.label (p0 ++ [i]) ∪
              (if (p0 ++ [i]).IsPrefix z then {lastState n hn} else ∅)
            rw [if_pos hpi_pref_z]
            simp
          exact Finset.disjoint_left.mp
            (hvK.2.2.2.2.1 p0 i j (Finset.mem_insert_of_mem hpiM) (Finset.mem_insert_of_mem hpjM) (by omega))
            hqpi hqpj
      · have hxK : x ∉ (generatedData hn H.val p).nodes := by
          change x ∉ insert z H.val.nodes
          simp [hxz, hxM]
        rw [hvK.2.2.1 x hxK]
        by_cases hxE : x ∈ E.nodes
        · dsimp only [E] at hxE
          rw [expand_nodes, Finset.mem_union] at hxE
          rcases hxE with hm | himg
          · exact absurd hm hxM
          · obtain ⟨u, huM, rfl⟩ := Finset.mem_image.mp himg
            have huw_ne : u ≠ w := fun h => hxz (by subst h; rfl)
            by_cases huw : u.IsPrefix w
            · obtain ⟨rest, hrest⟩ := huw
              cases rest with
              | nil =>
                simp at hrest
                exact absurd hrest huw_ne
              | cons k tail =>
                have huk_pref_w : (u ++ [k]).IsPrefix w := ⟨tail, by simpa using hrest⟩
                have hukM : u ++ [k] ∈ H.val.nodes := H.property.1.2.1 w hwM (u ++ [k]) huk_pref_w
                have hk_pos : 0 < k := H.property.1.1 _ hukM k (by simp)
                have hk_le : k ≤ degree H.val.nodes u := le_degree_of_mem hukM
                have hqn_uk : lastState n hn ∈ E.label (u ++ [k]) := by
                  dsimp only [E]
                  rw [expand_label_old _ _ _ hukM, hnext_M (u ++ [k]) hukM]
                  have huk_pref_z : (u ++ [k]).IsPrefix z := (hprefix_wz (u ++ [k]) hukM).mp huk_pref_w
                  dsimp only [generatedData]
                  change lastState n hn ∈ H.val.label (u ++ [k]) ∪
                    (if (u ++ [k]).IsPrefix z then {lastState n hn} else ∅)
                  rw [if_pos huk_pref_z]
                  simp
                dsimp only [horizontal, E]
                rw [hE_new u huM, if_pos ⟨k :: tail, hrest⟩, Finset.filter_eq_empty_iff]
                intro r hr
                rw [Finset.mem_singleton] at hr
                subst hr
                intro hnot_ex
                exact hnot_ex ⟨u, degree H.val.nodes u + 1, [], k, rfl, hk_pos, by omega,
                  Finset.mem_union_left _ hukM, hqn_uk⟩
            · dsimp only [horizontal, E]
              rw [hE_new u huM, if_neg huw]
              simp
        · dsimp only [horizontal, E] at hxE ⊢
          rw [expand_label_outside _ _ _ hxE]
          simp
  have hH_out : ∀ x, x ∉ (horizontal E).nodes → (horizontal E).label x = ∅ := by
    intro x hx
    rw [hH_lbl x]
    apply hvK.2.2.1 x
    intro hxK
    apply hx
    rcases Finset.mem_insert.mp hxK with rfl | hxM
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hwM, rfl⟩)
    · exact Finset.mem_union_left _ hxM
  have hS3_nodes : (stage3 (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p)).nodes =
      (generatedData hn H.val p).nodes := by
    ext x
    rw [stage3, mem_removeEmpty_nodes]
    change x ∈ E.nodes ∧ ((horizontal E).label x).Nonempty ↔ x ∈ (generatedData hn H.val p).nodes
    rw [hH_lbl x]
    constructor
    · rintro ⟨_, hne⟩
      by_contra hnot
      rw [hvK.2.2.1 x hnot] at hne
      simp at hne
    · intro hxK
      refine ⟨?_, hvK.2.2.2.1 x hxK⟩
      rcases Finset.mem_insert.mp hxK with rfl | hxM
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hwM, rfl⟩)
      · exact Finset.mem_union_left _ hxM
  have hS3 : stage3 (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p) =
      generatedData hn H.val p := by
    apply treeData_ext hS3_nodes
    intro x
    rw [stage3, removeEmpty_label _ hH_out x, hH_lbl x]
  have hres : resetNodes (stage3 (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p)) = ∅ := by
    rw [hS3]
    exact resetNodes_eq_empty_of_valid hvK
  have hs4 : stage4 (fullBuchi n hn) H.val (genLetter hn (stateSet H.val) p) =
      generatedData hn H.val p := by
    unfold stage4
    rw [hS3]
    exact prune_eq_self_of_resetNodes_empty (resetNodes_eq_empty_of_valid hvK) hvK.2.2.1
  have hacc : acceptingNodes (fullBuchi n hn) H (genLetter hn (stateSet H.val) p) = ∅ := by
    simp [acceptingNodes, hres]
  have hsdiff : H.val.nodes \ (generatedData hn H.val p).nodes = ∅ := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    intro u hu
    exact Finset.mem_insert_of_mem hu
  have heff0 := effect_from_stage4 hn H (genLetter hn (stateSet H.val) p)
    (generatedData hn H.val p) ∅ hvK (fun u hu => by rw [hownK u hu]; simp) hs4 hacc
  rw [hsdiff] at heff0
  refine ⟨heff0, ?_, ?_⟩
  · intro x hxM
    have hxz : x ≠ z := fun h => hz_notM (h ▸ hxM)
    rw [hownK x (Finset.mem_insert_of_mem hxM), own_eq_singleton_ownState hn H hH hxM]
    simp [f, hxz]
  · dsimp only [generatedData]
    change H.val.label z ∪ (if z.IsPrefix z then {lastState n hn} else ∅) = {lastState n hn}
    rw [H.property.2.2.1 z hz_notM, if_pos (List.prefix_refl z), Finset.empty_union]

lemma case_perm_acc (n : ℕ) (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    {x0 : Node} {s : Fin n} {π : Fin n → Fin n}
    (hleaf : Leaf H.val.nodes x0) (hlbl_x0 : H.val.label x0 = {s})
    (hinj : Set.InjOn π {q | q ∈ stateSet H.val}) (hπs : π s = lastState n hn) :
    Effect hn H (permLetter (stateSet H.val) π) (mapData H.val π) {x0} ∅ := by
  classical
  obtain ⟨hvK, hownK⟩ := mapData_valid_and_own hn H hH π hinj
  have hx0M : x0 ∈ H.val.nodes := hleaf.1
  have hsP : s ∈ stateSet H.val := by
    have : s ∈ H.val.label x0 := by simp [hlbl_x0]
    exact label_sub_stateSet H.property x0 this
  have howner_s : owner H.val s = x0 := by
    have hs_own : s ∈ own H.val x0 := by
      rw [own_eq_label_of_leaf hleaf, hlbl_x0]; simp
    exact ((own_mem_iff_eq_owner H.property hsP hx0M).mp hs_own).symm
  have hqn_K_iff : ∀ u : Node, lastState n hn ∈ (mapData H.val π).label u ↔ u.IsPrefix x0 := by
    intro u
    rw [mem_mapData_label]
    constructor
    · rintro ⟨q, hqu, hπq⟩
      have hqP : q ∈ stateSet H.val := label_sub_stateSet H.property u hqu
      have hqs : q = s := hinj hqP hsP (hπq.trans hπs.symm)
      subst q
      rw [← howner_s]
      exact (mem_label_iff_prefix_owner H.property hsP u).mp hqu
    · intro hux0
      refine ⟨s, ?_, hπs⟩
      rw [mem_label_iff_prefix_owner H.property hsP u, howner_s]
      exact hux0
  have hnext : ∀ u : Node,
      nextLabel (fullBuchi n hn) H.val (permLetter (stateSet H.val) π) u =
        (mapData H.val π).label u :=
    fun u => delta_permLetter hn H π u
  let E := expand (fullBuchi n hn) H.val (permLetter (stateSet H.val) π)
  have hE_new : ∀ u ∈ H.val.nodes,
      E.label (u ++ [degree H.val.nodes u + 1]) =
        if u.IsPrefix x0 then {lastState n hn} else ∅ := by
    intro u huM
    dsimp only [E]
    by_cases hux0 : u.IsPrefix x0
    · rw [if_pos hux0]
      apply expand_label_new_eq_singleton _ _ _ huM rfl
      rw [hnext u]
      exact (hqn_K_iff u).mpr hux0
    · rw [if_neg hux0]
      apply expand_label_new_eq_empty _ _ _ huM rfl
      rw [hnext u]
      exact fun h => hux0 ((hqn_K_iff u).mp h)
  let z0 := x0 ++ [degree H.val.nodes x0 + 1]
  have hz0_notM : z0 ∉ H.val.nodes := newChild_notMem x0
  have hdeg_x0 : degree H.val.nodes x0 = 0 := by simp [degree, hleaf.2]
  have hH_old : ∀ u ∈ H.val.nodes, (horizontal E).label u = (mapData H.val π).label u := by
    intro u huM
    dsimp only [horizontal, E]
    rw [expand_label_old _ _ _ huM, hnext u, Finset.filter_eq_self]
    rintro q hq ⟨p0, i, v, j, rfl, hj0, hji, hpjE, hqpj⟩
    have hpiM : p0 ++ [i] ∈ H.val.nodes := H.property.1.2.1 _ huM (p0 ++ [i]) ⟨v, by simp⟩
    have hi_le : i ≤ degree H.val.nodes p0 := le_degree_of_mem hpiM
    have hpjM : p0 ++ [j] ∈ H.val.nodes := by
      rw [expand_nodes, Finset.mem_union] at hpjE
      rcases hpjE with hm | himg
      · exact hm
      · obtain ⟨w, _, heq⟩ := Finset.mem_image.mp himg
        obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
        omega
    rw [expand_label_old _ _ _ hpjM, hnext (p0 ++ [j])] at hqpj
    have huK' : (p0 ++ [i]) ++ v ∈ (mapData H.val π).nodes := by simpa [mapData] using huM
    have hq' : q ∈ (mapData H.val π).label ((p0 ++ [i]) ++ v) := by simpa using hq
    have hqpi : q ∈ (mapData H.val π).label (p0 ++ [i]) :=
      label_sub_of_prefix hvK (p0 ++ [i]) v huK' hq'
    exact Finset.disjoint_left.mp (hvK.2.2.2.2.1 p0 i j hpiM hpjM (by omega)) hqpi hqpj
  have hH_z0 : (horizontal E).label z0 = {lastState n hn} := by
    have hz0E : E.label z0 = {lastState n hn} := by
      dsimp only [z0]
      rw [hE_new x0 hx0M, if_pos (List.prefix_refl x0)]
    dsimp only [horizontal]
    rw [hz0E, Finset.filter_eq_self]
    rintro q hq ⟨p0, i, v, j, hzeq, hj0, hji, hpjE, hqpj⟩
    rw [Finset.mem_singleton] at hq
    subst hq
    cases v using List.reverseRecOn with
    | nil =>
      dsimp only [z0] at hzeq
      obtain ⟨hx0_eq, hi_eq⟩ := append_singleton_inj hzeq
      subst p0
      rw [hdeg_x0] at hi_eq
      omega
    | append_singleton rest b =>
      rw [show p0 ++ i :: (rest ++ [b]) = (p0 ++ i :: rest) ++ [b] by simp] at hzeq
      dsimp only [z0] at hzeq
      obtain ⟨hx0_eq, _⟩ := append_singleton_inj hzeq
      have hpi_pref_x0 : (p0 ++ [i]).IsPrefix x0 := ⟨rest, by simpa using hx0_eq.symm⟩
      have hpiM : p0 ++ [i] ∈ H.val.nodes := H.property.1.2.1 x0 hx0M (p0 ++ [i]) hpi_pref_x0
      have hi_le : i ≤ degree H.val.nodes p0 := le_degree_of_mem hpiM
      have hpjM : p0 ++ [j] ∈ H.val.nodes := by
        dsimp only [E] at hpjE
        rw [expand_nodes, Finset.mem_union] at hpjE
        rcases hpjE with hm | himg
        · exact hm
        · obtain ⟨w, _, heq⟩ := Finset.mem_image.mp himg
          obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
          omega
      dsimp only [E] at hqpj
      rw [expand_label_old _ _ _ hpjM, hnext (p0 ++ [j])] at hqpj
      have hqpi : lastState n hn ∈ (mapData H.val π).label (p0 ++ [i]) :=
        (hqn_K_iff (p0 ++ [i])).mpr hpi_pref_x0
      exact Finset.disjoint_left.mp (hvK.2.2.2.2.1 p0 i j hpiM hpjM (by omega)) hqpi hqpj
  have hH_other : ∀ x, x ∉ insert z0 H.val.nodes → (horizontal E).label x = ∅ := by
    intro x hx
    simp only [Finset.mem_insert, not_or] at hx
    obtain ⟨hxz0, hxM⟩ := hx
    by_cases hxE : x ∈ E.nodes
    · dsimp only [E] at hxE
      rw [expand_nodes, Finset.mem_union] at hxE
      rcases hxE with hm | himg
      · exact absurd hm hxM
      · obtain ⟨u, huM, rfl⟩ := Finset.mem_image.mp himg
        have hux0_ne : u ≠ x0 := fun h => hxz0 (by subst h; rfl)
        by_cases hux0 : u.IsPrefix x0
        · obtain ⟨rest, hrest⟩ := hux0
          cases rest with
          | nil =>
            simp at hrest
            exact absurd hrest hux0_ne
          | cons k tail =>
            have huk_pref_x0 : (u ++ [k]).IsPrefix x0 := ⟨tail, by simpa using hrest⟩
            have hukM : u ++ [k] ∈ H.val.nodes := H.property.1.2.1 x0 hx0M (u ++ [k]) huk_pref_x0
            have hk_pos : 0 < k := H.property.1.1 _ hukM k (by simp)
            have hk_le : k ≤ degree H.val.nodes u := le_degree_of_mem hukM
            have hqn_uk : lastState n hn ∈ E.label (u ++ [k]) := by
              dsimp only [E]
              rw [expand_label_old _ _ _ hukM, hnext (u ++ [k])]
              exact (hqn_K_iff (u ++ [k])).mpr huk_pref_x0
            dsimp only [horizontal]
            rw [hE_new u huM, if_pos ⟨k :: tail, hrest⟩, Finset.filter_eq_empty_iff]
            intro r hr
            rw [Finset.mem_singleton] at hr
            subst hr
            intro hnot_ex
            exact hnot_ex ⟨u, degree H.val.nodes u + 1, [], k, rfl, hk_pos, by omega,
              Finset.mem_union_left _ hukM, hqn_uk⟩
        · dsimp only [horizontal]
          rw [hE_new u huM, if_neg hux0]
          simp
    · dsimp only [horizontal, E] at hxE ⊢
      rw [expand_label_outside _ _ _ hxE]
      simp
  have hH_out : ∀ x, x ∉ (horizontal E).nodes → (horizontal E).label x = ∅ := by
    intro x hx
    apply hH_other x
    intro hx_ins
    apply hx
    rcases Finset.mem_insert.mp hx_ins with rfl | hxM
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x0, hx0M, rfl⟩)
    · exact Finset.mem_union_left _ hxM
  let S3 := stage3 (fullBuchi n hn) H.val (permLetter (stateSet H.val) π)
  have hS3_nodes : S3.nodes = insert z0 H.val.nodes := by
    ext x
    change x ∈ (removeEmpty (horizontal E)).nodes ↔ x ∈ insert z0 H.val.nodes
    rw [mem_removeEmpty_nodes]
    constructor
    · rintro ⟨_, hne⟩
      by_contra hnot
      rw [hH_other x hnot] at hne
      simp at hne
    · intro hx_ins
      rcases Finset.mem_insert.mp hx_ins with rfl | hxM
      · refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x0, hx0M, rfl⟩), ?_⟩
        rw [hH_z0]
        simp
      · refine ⟨Finset.mem_union_left _ hxM, ?_⟩
        rw [hH_old x hxM]
        exact hvK.2.2.2.1 x hxM
  have hS3_lbl : ∀ x, S3.label x = (horizontal E).label x :=
    fun x => removeEmpty_label (horizontal E) hH_out x
  have hS3_old : ∀ u ∈ H.val.nodes, S3.label u = (mapData H.val π).label u :=
    fun u huM => (hS3_lbl u).trans (hH_old u huM)
  have hS3_z0 : S3.label z0 = {lastState n hn} := (hS3_lbl z0).trans hH_z0
  have hres : resetNodes S3 = {x0} := by
    ext x
    simp only [resetNodes, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxS3, heq⟩
      rw [hS3_nodes, Finset.mem_insert] at hxS3
      rcases hxS3 with hxz0 | hxM
      · subst hxz0
        exfalso
        have hcl_z0 : childLabels S3 z0 = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro q hq
          obtain ⟨y, hy_ch, _⟩ := (mem_childLabels_iff S3 z0 q).mp hq
          obtain ⟨hyS3, k, rfl⟩ := Finset.mem_filter.mp hy_ch
          rw [hS3_nodes, Finset.mem_insert] at hyS3
          rcases hyS3 with heq' | hyM
          · have := congrArg List.length heq'
            simp at this
          · exact hz0_notM (H.property.1.2.1 _ hyM z0 ⟨[k], rfl⟩)
        rw [hS3_z0, hcl_z0] at heq
        simp at heq
      · by_contra hne_x0
        have hch_eq : children S3.nodes x = children H.val.nodes x := by
          ext y
          simp only [children, hS3_nodes, Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hyz0 | hyM, k, hyk⟩
            · subst y
              obtain ⟨hx_eq, _⟩ := append_singleton_inj hyk.symm
              exact absurd hx_eq hne_x0
            · exact ⟨hyM, k, hyk⟩
          · rintro ⟨hyM, k, hyk⟩
            exact ⟨Or.inr hyM, k, hyk⟩
        have hcl_eq : childLabels S3 x = childLabels (mapData H.val π) x := by
          ext q
          rw [mem_childLabels_iff, mem_childLabels_iff]
          change (∃ a ∈ children S3.nodes x, q ∈ S3.label a) ↔
            (∃ a ∈ children H.val.nodes x, q ∈ (mapData H.val π).label a)
          rw [hch_eq]
          refine exists_congr fun a => and_congr_right fun ha => ?_
          rw [hS3_old a (Finset.mem_filter.mp ha).1]
        rw [hS3_old x hxM, hcl_eq] at heq
        exact (hvK.2.2.2.2.2 x hxM).ne heq.symm
    · intro hxx0
      subst x
      refine ⟨by rw [hS3_nodes]; exact Finset.mem_insert_of_mem hx0M, ?_⟩
      have hKx0 : (mapData H.val π).label x0 = {lastState n hn} := by
        rw [mapData_label_singleton H.val π hlbl_x0, hπs]
      have hch_x0 : children S3.nodes x0 = {z0} := by
        ext y
        simp only [children, hS3_nodes, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hyz0 | hyM, k, hyk⟩
          · exact hyz0
          · exfalso
            have hy_ch : y ∈ children H.val.nodes x0 := Finset.mem_filter.mpr ⟨hyM, k, hyk⟩
            rw [hleaf.2] at hy_ch
            simp at hy_ch
        · intro hyz0
          subst y
          exact ⟨Or.inl rfl, degree H.val.nodes x0 + 1, rfl⟩
      have hcl_x0 : childLabels S3 x0 = {lastState n hn} := by
        ext q
        rw [mem_childLabels_iff, hch_x0]
        simp only [Finset.mem_singleton, exists_eq_left]
        rw [hS3_z0, Finset.mem_singleton]
      rw [hS3_old x0 hx0M, hKx0, hcl_x0]
  have hs4_nodes : (stage4 (fullBuchi n hn) H.val (permLetter (stateSet H.val) π)).nodes =
      (mapData H.val π).nodes := by
    ext y
    dsimp only [stage4, prune, mapData]
    rw [Finset.mem_filter]
    change y ∈ S3.nodes ∧ (¬ ∃ p ∈ resetNodes S3, p.IsPrefix y ∧ p ≠ y) ↔ y ∈ H.val.nodes
    rw [hS3_nodes, hres]
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨hyz0 | hyM, hnot⟩
      · subst y
        exfalso
        apply hnot ⟨⟨[degree H.val.nodes x0 + 1], rfl⟩, ?_⟩
        intro heq
        have hlen := congrArg List.length heq
        dsimp only [z0] at hlen
        simp at hlen
      · exact hyM
    · intro hyM
      refine ⟨Or.inr hyM, ?_⟩
      rintro ⟨⟨t, rfl⟩, hne⟩
      cases t with
      | nil => exact hne (by simp)
      | cons k rest =>
        have hkM : x0 ++ [k] ∈ H.val.nodes := H.property.1.2.1 _ hyM (x0 ++ [k]) ⟨rest, by simp⟩
        have hk_ch : x0 ++ [k] ∈ children H.val.nodes x0 := Finset.mem_filter.mpr ⟨hkM, k, rfl⟩
        rw [hleaf.2] at hk_ch
        simp at hk_ch
  have hs4 : stage4 (fullBuchi n hn) H.val (permLetter (stateSet H.val) π) = mapData H.val π := by
    apply treeData_ext hs4_nodes
    intro x
    dsimp only [stage4, prune]
    split_ifs with hx4
    · have hxM : x ∈ H.val.nodes := by
        have hx4' : x ∈ (stage4 (fullBuchi n hn) H.val (permLetter (stateSet H.val) π)).nodes := hx4
        rwa [hs4_nodes] at hx4'
      exact hS3_old x hxM
    · have hxM : x ∉ H.val.nodes := by
        intro hm
        apply hx4
        have hm' : x ∈ (mapData H.val π).nodes := hm
        rwa [← hs4_nodes] at hm'
      exact (mapData_label_empty H.val π (H.property.2.2.1 x hxM)).symm
  have hacc : acceptingNodes (fullBuchi n hn) H (permLetter (stateSet H.val) π) = {x0} := by
    ext x
    simp only [acceptingNodes, hs4, Finset.mem_filter, Finset.mem_singleton]
    change (x ∈ H.val.nodes ∧ x ∈ resetNodes S3 ∧ x ∈ H.val.nodes ∧ compress H.val.nodes x = x) ↔ x = x0
    rw [hres, Finset.mem_singleton]
    constructor
    · exact fun h => h.2.1
    · intro hxx0
      subst x
      exact ⟨hx0M, rfl, hx0M, compress_eq_self_of_ordered H.property.1 hx0M⟩
  have hsdiff : H.val.nodes \ (mapData H.val π).nodes = ∅ := Finset.sdiff_self _
  have heff0 := effect_from_stage4 hn H (permLetter (stateSet H.val) π)
    (mapData H.val π) {x0} hvK (fun u hu => by rw [hownK u hu]; simp) hs4 hacc
  rwa [hsdiff] at heff0

lemma case_del (n : ℕ) (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H)
    {z : Node} {s : Fin n}
    (hleaf : Leaf H.val.nodes z) (hyng : Youngest H.val.nodes z) (hlbl_z : H.val.label z = {s}) :
    (lastState n hn ∉ (stateSet H.val).erase s →
      Effect hn H (delLetter (stateSet H.val) s) (deletedData H.val z s) ∅ {z} ∧
      ∀ x ∈ H.val.nodes, x ≠ z → own (deletedData H.val z s) x = own H.val x) ∧
    (∀ x, x ≠ z → Leaf H.val.nodes x → H.val.label x = {lastState n hn} →
      lastState n hn ∈ (stateSet H.val).erase s →
      Effect hn H (delPrimeLetter hn (stateSet H.val) s)
        (deletedPrimeData hn H.val z s) ∅ {z} ∧
      own (deletedPrimeData hn H.val z s) x = {s} ∧
      ∀ u ∈ H.val.nodes, u ≠ z → u ≠ x →
        own (deletedPrimeData hn H.val z s) u = own H.val u) := by
  classical
  obtain ⟨hordKd, hrootKd⟩ := ordered_erase_leaf_youngest H.property.1 hleaf hyng
  have hz_ne_nil : z ≠ [] := fun h => (Finset.mem_erase.mp hrootKd).1 h.symm
  have hs_own_z : ownState hn H hH z = s := by
    have h1 := own_eq_singleton_ownState hn H hH hleaf.1
    rw [own_eq_label_of_leaf hleaf, hlbl_z] at h1
    exact Finset.singleton_injective h1.symm
  have hlKd_in : ∀ u ∈ (deletedData H.val z s).nodes, ∀ q,
      q ∈ (deletedData H.val z s).label u ↔
        ∃ y ∈ (deletedData H.val z s).nodes, u.IsPrefix y ∧ ownState hn H hH y = q := by
    intro u huKd q
    obtain ⟨huz, huM⟩ := Finset.mem_erase.mp huKd
    dsimp only [deletedData]
    rw [if_neg huz, Finset.mem_erase, mem_label_iff_ownState hn H hH huM q]
    constructor
    · rintro ⟨hq_ne_s, y, hyM, huy, rfl⟩
      have hyz : y ≠ z := fun h => hq_ne_s (h ▸ hs_own_z)
      exact ⟨y, Finset.mem_erase.mpr ⟨hyz, hyM⟩, huy, rfl⟩
    · rintro ⟨y, hyKd, huy, rfl⟩
      obtain ⟨hyz, hyM⟩ := Finset.mem_erase.mp hyKd
      refine ⟨?_, y, hyM, huy, rfl⟩
      intro heq
      exact hyz (ownState_injOn hn H hH hyM hleaf.1 (heq.trans hs_own_z.symm))
  have hlKd_out : ∀ u, u ∉ (deletedData H.val z s).nodes → (deletedData H.val z s).label u = ∅ := by
    intro u huKd
    dsimp only [deletedData]
    by_cases huz : u = z
    · simp [huz]
    · have huM : u ∉ H.val.nodes := fun hm => huKd (Finset.mem_erase.mpr ⟨huz, hm⟩)
      simp [huz, H.property.2.2.1 u huM]
  have hinjKd : Set.InjOn (ownState hn H hH) {u | u ∈ (deletedData H.val z s).nodes} :=
    fun u1 hu1 u2 hu2 heq =>
      ownState_injOn hn H hH (Finset.mem_erase.mp hu1).2 (Finset.mem_erase.mp hu2).2 heq
  obtain ⟨hvKd, hownKd⟩ := valid_and_own_of_fn (deletedData H.val z s) (ownState hn H hH)
    hordKd hrootKd hinjKd hlKd_in hlKd_out
  have hsdiff_z : H.val.nodes \ (H.val.nodes.erase z) = {z} := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨huM, hnot⟩
      by_contra huz
      exact hnot ⟨huz, huM⟩
    · rintro rfl
      exact ⟨hleaf.1, by simp⟩
  refine ⟨?_, ?_⟩
  · intro hqn_not
    have hnext_d : ∀ u : Node,
        nextLabel (fullBuchi n hn) H.val (delLetter (stateSet H.val) s) u =
          (deletedData H.val z s).label u := by
      intro u
      have hu_sub : H.val.label u ⊆ stateSet H.val := label_sub_stateSet H.property u
      have herase : nextLabel (fullBuchi n hn) H.val (delLetter (stateSet H.val) s) u =
          (H.val.label u).erase s := by
        ext r
        rw [mem_nextLabel_iff]
        simp only [fullBuchi, delLetter, idLetter, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨q, hqu, p, ⟨hpne, _⟩, heq⟩
          obtain ⟨hpq, hpr⟩ := Prod.mk.inj heq
          subst p; subst r
          exact ⟨hpne, hqu⟩
        · rintro ⟨hrne, hru⟩
          exact ⟨r, hru, r, ⟨hrne, hu_sub hru⟩, rfl⟩
      rw [herase]
      dsimp only [deletedData]
      by_cases huz : u = z
      · subst u
        simp [hlbl_z]
      · simp [huz]
    have hqn_Kd_root : lastState n hn ∉ (deletedData H.val z s).label [] := by
      simpa [deletedData, hz_ne_nil.symm, stateSet] using hqn_not
    obtain ⟨hs4, hres⟩ := stage4_eq_of_next hn H (delLetter (stateSet H.val) s)
      (deletedData H.val z s) hvKd (Finset.erase_subset z H.val.nodes) hnext_d hqn_Kd_root
    have hacc : acceptingNodes (fullBuchi n hn) H (delLetter (stateSet H.val) s) = ∅ := by
      ext u
      simp only [acceptingNodes, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ hu_res
      rw [hres] at hu_res
      simp at hu_res
    have heff0 := effect_from_stage4 hn H (delLetter (stateSet H.val) s)
      (deletedData H.val z s) ∅ hvKd (fun u hu => by rw [hownKd u hu]; simp) hs4 hacc
    have heff : Effect hn H (delLetter (stateSet H.val) s) (deletedData H.val z s) ∅ {z} := by
      simpa [deletedData, hsdiff_z] using heff0
    refine ⟨heff, ?_⟩
    intro x hxM hxz
    rw [hownKd x (Finset.mem_erase.mpr ⟨hxz, hxM⟩), own_eq_singleton_ownState hn H hH hxM]
  · intro x hxz hleaf_x hlbl_x hqn_in
    let ρ_swap : Fin n → Fin n := fun p => if p = lastState n hn then s else p
    have hqn_ne_s : lastState n hn ≠ s := (Finset.mem_erase.mp hqn_in).1
    have hinj_swap : Set.InjOn ρ_swap {q | q ∈ stateSet (deletedData H.val z s)} := by
      intro q1 hq1 q2 hq2 heq
      change q1 ∈ (deletedData H.val z s).label [] at hq1
      change q2 ∈ (deletedData H.val z s).label [] at hq2
      dsimp only [deletedData] at hq1 hq2
      rw [if_neg hz_ne_nil.symm, Finset.mem_erase] at hq1 hq2
      by_cases h1 : q1 = lastState n hn <;> by_cases h2 : q2 = lastState n hn
      · rw [h1, h2]
      · dsimp only [ρ_swap] at heq
        rw [if_pos h1, if_neg h2] at heq
        exact absurd heq.symm hq2.1
      · dsimp only [ρ_swap] at heq
        rw [if_neg h1, if_pos h2] at heq
        exact absurd heq hq1.1
      · dsimp only [ρ_swap] at heq
        rwa [if_neg h1, if_neg h2] at heq
    let H_Kd : History (Fin n) := ⟨deletedData H.val z s, hvKd⟩
    have hH_Kd : Simple H_Kd := fun u hu => by rw [hownKd u hu]; simp
    obtain ⟨hvKdp, hownKdp⟩ := mapData_valid_and_own hn H_Kd hH_Kd ρ_swap hinj_swap
    have hnext_dp : ∀ u : Node,
        nextLabel (fullBuchi n hn) H.val (delPrimeLetter hn (stateSet H.val) s) u =
          (deletedPrimeData hn H.val z s).label u := by
      intro u
      have hu_sub : H.val.label u ⊆ stateSet H.val := label_sub_stateSet H.property u
      ext r
      rw [mem_nextLabel_iff, deletedPrimeData, mem_mapData_label]
      dsimp only [deletedData]
      by_cases huz : u = z
      · subst u
        rw [if_pos rfl]
        constructor
        · rintro ⟨q, hqz, hdel⟩
          rw [hlbl_z, Finset.mem_singleton] at hqz
          subst q
          simp only [fullBuchi, delPrimeLetter, idLetter, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_insert, Finset.mem_image, Finset.mem_erase] at hdel
          rcases hdel with heq | ⟨p, ⟨_, hp_s, _⟩, heq⟩
          · obtain ⟨hq_eq, _⟩ := Prod.mk.inj heq
            exact absurd hq_eq.symm hqn_ne_s
          · obtain ⟨hpq, _⟩ := Prod.mk.inj heq
            exact absurd hpq hp_s
        · rintro ⟨q, hq, _⟩
          simp at hq
      · rw [if_neg huz]
        simp only [fullBuchi, delPrimeLetter, idLetter, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨q, hqu, heq | ⟨p, ⟨hp_qn, hp_s, _⟩, heq⟩⟩
          · obtain ⟨hq_eq, hr_eq⟩ := Prod.mk.inj heq
            subst q; subst r
            exact ⟨lastState n hn, ⟨hqn_ne_s, hqu⟩, by simp⟩
          · obtain ⟨hpq, hpr⟩ := Prod.mk.inj heq
            subst p; subst r
            exact ⟨q, ⟨hp_s, hqu⟩, by simp [hp_qn]⟩
        · rintro ⟨q, ⟨hq_s, hqu⟩, rfl⟩
          by_cases hqqn : q = lastState n hn
          · subst q
            exact ⟨lastState n hn, hqu, Or.inl (by simp)⟩
          · exact ⟨q, hqu, Or.inr ⟨q, ⟨hqqn, hq_s, hu_sub hqu⟩, by simp [hqqn]⟩⟩
    have hqn_not_Kdp : lastState n hn ∉ (deletedPrimeData hn H.val z s).label [] := by
      rw [deletedPrimeData, mem_mapData_label]
      rintro ⟨q, _, hρq⟩
      by_cases hqqn : q = lastState n hn
      · rw [if_pos hqqn] at hρq
        exact hqn_ne_s hρq.symm
      · rw [if_neg hqqn] at hρq
        exact hqqn hρq
    obtain ⟨hs4, hres⟩ := stage4_eq_of_next hn H (delPrimeLetter hn (stateSet H.val) s)
      (deletedPrimeData hn H.val z s) hvKdp (Finset.erase_subset z H.val.nodes) hnext_dp hqn_not_Kdp
    have hacc : acceptingNodes (fullBuchi n hn) H (delPrimeLetter hn (stateSet H.val) s) = ∅ := by
      ext u
      simp only [acceptingNodes, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ hu_res
      rw [hres] at hu_res
      simp at hu_res
    have heff0 := effect_from_stage4 hn H (delPrimeLetter hn (stateSet H.val) s)
      (deletedPrimeData hn H.val z s) ∅ hvKdp
      (fun u hu => by change (own (mapData H_Kd.val ρ_swap) u).card = 1; rw [hownKdp u hu]; simp)
      hs4 hacc
    have heff : Effect hn H (delPrimeLetter hn (stateSet H.val) s)
        (deletedPrimeData hn H.val z s) ∅ {z} := by
      simpa [deletedPrimeData, mapData, deletedData, hsdiff_z] using heff0
    have hown_Kd_eq : ∀ u ∈ H_Kd.val.nodes, ownState hn H_Kd hH_Kd u = ownState hn H hH u := by
      intro u huKd
      have h1 := own_eq_singleton_ownState hn H_Kd hH_Kd huKd
      change own (deletedData H.val z s) u = _ at h1
      rw [hownKd u huKd] at h1
      exact (Finset.singleton_injective h1).symm
    have hxKd : x ∈ H_Kd.val.nodes := Finset.mem_erase.mpr ⟨hxz, hleaf_x.1⟩
    have hown_x : ownState hn H hH x = lastState n hn := by
      have h1 := own_eq_singleton_ownState hn H hH hleaf_x.1
      rw [own_eq_label_of_leaf hleaf_x, hlbl_x] at h1
      exact Finset.singleton_injective h1.symm
    refine ⟨heff, ?_, ?_⟩
    · change own (mapData H_Kd.val ρ_swap) x = {s}
      rw [hownKdp x hxKd, hown_Kd_eq x hxKd, hown_x]
      simp [ρ_swap]
    · intro u huM huz hux
      have huKd : u ∈ H_Kd.val.nodes := Finset.mem_erase.mpr ⟨huz, huM⟩
      have hu_ne_qn : ownState hn H hH u ≠ lastState n hn := by
        intro heq
        exact hux (ownState_injOn hn H hH huM hleaf_x.1 (heq.trans hown_x.symm))
      change own (mapData H_Kd.val ρ_swap) u = own H.val u
      rw [hownKdp u huKd, hown_Kd_eq u huKd, own_eq_singleton_ownState hn H hH huM]
      simp [ρ_swap, hu_ne_qn]

end
end BuchiRabinIndex.LowerBound.Lemma38Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma38Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (H : History (Fin n)) (hH : Simple H) :
    (∀ p ∈ stateSet H.val, lastState n hn ∉ stateSet H.val →
      Effect hn H (genLetter hn (stateSet H.val) p) (generatedData hn H.val p) ∅ ∅ ∧
      (∀ x ∈ H.val.nodes, own (generatedData hn H.val p) x = own H.val x) ∧
      (generatedData hn H.val p).label
        (owner H.val p ++ [degree H.val.nodes (owner H.val p) + 1]) = {lastState n hn}) ∧
    (∀ π : Fin n → Fin n,
      Set.InjOn π {q | q ∈ stateSet H.val} →
      (∀ q ∈ stateSet H.val, π q ≠ lastState n hn) →
      Effect hn H (permLetter (stateSet H.val) π) (mapData H.val π) ∅ ∅) ∧
    (∀ x s (π : Fin n → Fin n), Leaf H.val.nodes x → H.val.label x = {s} →
      Set.InjOn π {q | q ∈ stateSet H.val} → π s = lastState n hn →
      Effect hn H (permLetter (stateSet H.val) π) (mapData H.val π) {x} ∅) ∧
    (∀ z s, Leaf H.val.nodes z → Youngest H.val.nodes z → H.val.label z = {s} →
      (lastState n hn ∉ (stateSet H.val).erase s →
        Effect hn H (delLetter (stateSet H.val) s) (deletedData H.val z s) ∅ {z} ∧
        ∀ x ∈ H.val.nodes, x ≠ z → own (deletedData H.val z s) x = own H.val x) ∧
      (∀ x, x ≠ z → Leaf H.val.nodes x → H.val.label x = {lastState n hn} →
        lastState n hn ∈ (stateSet H.val).erase s →
        Effect hn H (delPrimeLetter hn (stateSet H.val) s)
          (deletedPrimeData hn H.val z s) ∅ {z} ∧
        own (deletedPrimeData hn H.val z s) x = {s} ∧
        ∀ u ∈ H.val.nodes, u ≠ z → u ≠ x →
          own (deletedPrimeData hn H.val z s) u = own H.val u)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp hqn
    exact case_gen n hn H hH hp hqn
  · intro π hinj hno_qn
    obtain ⟨hvK, hownK⟩ := mapData_valid_and_own hn H hH π hinj
    have hnext : ∀ u : Node,
        nextLabel (fullBuchi n hn) H.val (permLetter (stateSet H.val) π) u =
          (mapData H.val π).label u :=
      fun u => delta_permLetter hn H π u
    have hqn_not_K : lastState n hn ∉ (mapData H.val π).label [] := by
      rw [mem_mapData_label]
      rintro ⟨q, hq, heq⟩
      exact hno_qn q hq heq
    obtain ⟨hs4, hres⟩ := stage4_eq_of_next hn H (permLetter (stateSet H.val) π)
      (mapData H.val π) hvK (Set.Subset.refl _) hnext hqn_not_K
    have hacc : acceptingNodes (fullBuchi n hn) H (permLetter (stateSet H.val) π) = ∅ := by
      ext u
      simp only [acceptingNodes, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ hu_res
      rw [hres] at hu_res
      simp at hu_res
    have hsdiff : H.val.nodes \ (mapData H.val π).nodes = ∅ := Finset.sdiff_self _
    have heff0 := effect_from_stage4 hn H (permLetter (stateSet H.val) π)
      (mapData H.val π) ∅ hvK (fun u hu => by rw [hownK u hu]; simp) hs4 hacc
    rwa [hsdiff] at heff0
  · intro x s π hleaf hlbl hinj hπs
    exact case_perm_acc n hn H hH hleaf hlbl hinj hπs
  · intro z s hleaf hyng hlbl
    exact case_del n hn H hH hleaf hyng hlbl
