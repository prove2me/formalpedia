-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:52:18.150897+00:00
-- url     : https://prove2.me/submissions/76cf864a-6a03-4c99-9812-a1f0e858ff4e

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma9Aux
noncomputable section
open BuchiRabinIndex.LowerBound
open scoped Classical

/-! ### List & Node combinatorics -/

lemma getLast!_concat : ∀ (x : Node) (i : ℕ), (x ++ [i]).getLast! = i
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: xs, i => getLast!_concat (b :: xs) i

lemma dropLast_concat : ∀ (x : Node) (i : ℕ), (x ++ [i]).dropLast = x
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: xs, i => congrArg (a :: ·) (dropLast_concat (b :: xs) i)

lemma append_singleton_inj {x y : Node} {i j : ℕ} (h : x ++ [i] = y ++ [j]) : x = y ∧ i = j := by
  have hx : x = y := by
    have := congrArg List.dropLast h
    rwa [dropLast_concat, dropLast_concat] at this
  subst hx
  exact ⟨rfl, by simpa using h⟩

lemma eq_of_prefix_of_length_eq {a b : Node} (h : a.IsPrefix b) (hl : a.length = b.length) :
    a = b := by
  obtain ⟨t, rfl⟩ := h
  have ht0 : t.length = 0 := by simp only [List.length_append] at hl; omega
  rcases List.eq_nil_of_length_eq_zero ht0 with rfl
  simp

lemma prefix_of_proper_prefix_concat {p x : Node} {i : ℕ}
    (hp : p.IsPrefix (x ++ [i])) (hne : p ≠ x ++ [i]) : p.IsPrefix x := by
  have hlen : p.length ≤ x.length := by
    have h1 := hp.length_le
    simp only [List.length_append, List.length_singleton] at h1
    by_cases h2 : p.length = x.length + 1
    · exact absurd (eq_of_prefix_of_length_eq hp (by simp [h2])) hne
    · omega
  obtain ⟨t, ht⟩ := hp
  have htk := congrArg (List.take p.length) ht
  rw [List.take_left, List.take_append_of_le_length hlen] at htk
  rw [htk]
  exact List.take_prefix _ _

lemma le_degree_of_mem {T : Finset Node} {x : Node} {i : ℕ} (h : x ++ [i] ∈ T) :
    i ≤ degree T x := by
  unfold degree
  have hch : x ++ [i] ∈ children T x := by simp [children, h]
  have himg : i ∈ (children T x).image (fun y => y.getLast!) := by
    refine Finset.mem_image.mpr ⟨x ++ [i], hch, getLast!_concat x i⟩
  exact Finset.le_sup (f := id) himg

lemma not_mem_succ_degree (T : Finset Node) (x : Node) :
    x ++ [degree T x + 1] ∉ T := by
  intro h
  have := le_degree_of_mem h
  omega

lemma mem_degree_of_pos {T : Finset Node} {x : Node} (hpos : 0 < degree T x) :
    x ++ [degree T x] ∈ T := by
  have hne : ((children T x).image (fun y => y.getLast!)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    unfold degree at hpos
    rw [hemp] at hpos
    simp at hpos
  obtain ⟨m, hm_mem, hm_eq⟩ := Finset.exists_mem_eq_sup _ hne id
  have hdeg : degree T x = m := hm_eq
  rw [hdeg]
  obtain ⟨y, hy_ch, hy_last⟩ := Finset.mem_image.mp hm_mem
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hyT, j, rfl⟩ := hy_ch
  rw [getLast!_concat] at hy_last
  rwa [← hy_last]

/-! ### Valid History Trees & Own States -/

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

lemma nodes_card_le {Q : Type} [Fintype Q] (H : History Q) :
    H.val.nodes.card ≤ Fintype.card Q := by
  have hv := H.property
  have hdisj : (H.val.nodes : Set Node).PairwiseDisjoint (own H.val) :=
    fun x hx y hy hne => own_disjoint hv hx hy hne
  have hpos : ∀ x ∈ H.val.nodes, 1 ≤ (own H.val x).card := by
    intro x hx
    rw [Finset.one_le_card]
    have hss := hv.2.2.2.2.2 x hx
    rw [own, Finset.sdiff_nonempty]
    exact fun h => hss.not_subset h
  calc H.val.nodes.card
      = ∑ _x ∈ H.val.nodes, 1 := by simp
    _ ≤ ∑ x ∈ H.val.nodes, (own H.val x).card := Finset.sum_le_sum hpos
    _ = (H.val.nodes.biUnion (own H.val)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card Q := Finset.card_univ

lemma length_lt_card_of_mem {Q : Type} [Fintype Q] (H : History Q)
    {p : Node} (hp : p ∈ H.val.nodes) : p.length < Fintype.card Q := by
  let S := (Finset.range (p.length + 1)).image (fun k => p.take k)
  have hsub : S ⊆ H.val.nodes := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    exact H.property.1.2.1 p hp (p.take k) (List.take_prefix k p)
  have hinj : Set.InjOn (fun k => p.take k) (Finset.range (p.length + 1)) := by
    intro k1 hk1 k2 hk2 heq
    simp only [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    have hl := congrArg List.length heq
    rw [List.length_take_of_le (by omega), List.length_take_of_le (by omega)] at hl
    exact hl
  have hcardS : S.card = p.length + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hle : S.card ≤ Fintype.card Q :=
    (Finset.card_le_card hsub).trans (nodes_card_le H)
  omega

lemma exists_own_of_mem_label {Q : Type} {H : TreeData Q} (_hv : Valid H)
    {u : Node} (hu : u ∈ H.nodes) {q : Q} (hq : q ∈ H.label u) :
    ∃ x ∈ H.nodes, u.IsPrefix x ∧ q ∈ own H x := by
  let S := H.nodes.filter (fun z => u.IsPrefix z ∧ q ∈ H.label z)
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨hu, List.prefix_refl u, hq⟩
  obtain ⟨x, hxS, hm_sup⟩ := Finset.exists_mem_eq_sup S ⟨u, huS⟩ List.length
  have hx_mem : x ∈ H.nodes := (Finset.mem_filter.mp hxS).1
  have hux : u.IsPrefix x := (Finset.mem_filter.mp hxS).2.1
  have hqx : q ∈ H.label x := (Finset.mem_filter.mp hxS).2.2
  refine ⟨x, hx_mem, hux, Finset.mem_sdiff.mpr ⟨hqx, ?_⟩⟩
  intro hch
  obtain ⟨y, hy_ch, hqy⟩ := Finset.mem_biUnion.mp hch
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hy_mem, j, rfl⟩ := hy_ch
  have huy : u.IsPrefix (x ++ [j]) := hux.trans ⟨[j], rfl⟩
  have hyS : x ++ [j] ∈ S := Finset.mem_filter.mpr ⟨hy_mem, huy, hqy⟩
  have hle : (x ++ [j]).length ≤ S.sup List.length := Finset.le_sup (f := List.length) hyS
  rw [hm_sup] at hle
  simp at hle

lemma mem_label_iff_prefix_own {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x u : Node} {q : Q} (hx : x ∈ H.nodes) (hown : q ∈ own H x) (hu : u ∈ H.nodes) :
    q ∈ H.label u ↔ u.IsPrefix x := by
  constructor
  · intro hqu
    obtain ⟨y, hy, huy, hown_y⟩ := exists_own_of_mem_label hv hu hqu
    have hyx : y = x := by
      by_contra hne
      exact Finset.disjoint_left.mp (own_disjoint hv hy hx hne) hown_y hown
    rwa [← hyx]
  · rintro ⟨w, rfl⟩
    exact label_sub_of_prefix hv u w hx (Finset.mem_sdiff.mp hown).1

/-! ### Step 1 (`expand`) -/

lemma expand_mem_iff {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) (y : Node) :
    y ∈ (expand B H σ).nodes ↔
      y ∈ H.nodes ∨ ∃ x ∈ H.nodes, y = x ++ [degree H.nodes x + 1] := by
  simp only [expand, Finset.mem_union, Finset.mem_image]
  exact or_congr_right ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩

lemma expand_label_old {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ H.nodes) :
    (expand B H σ).label x = (H.label x).biUnion (fun q => B.delta q σ) := by
  simp [expand, hx]

lemma expand_label_new {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ H.nodes) :
    (expand B H σ).label (x ++ [degree H.nodes x + 1]) =
      ((H.label x).biUnion (fun q => B.delta q σ)) ∩ B.accepting := by
  have hnot : x ++ [degree H.nodes x + 1] ∉ H.nodes := not_mem_succ_degree H.nodes x
  have hmem : x ++ [degree H.nodes x + 1] ∈ (expand B H σ).nodes := by
    rw [expand_mem_iff]; exact Or.inr ⟨x, hx, rfl⟩
  unfold expand
  simp only [hnot, ↓reduceIte, dropLast_concat]
  rw [if_pos (by simpa [expand] using hmem)]

lemma expand_ordered {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hord : Ordered H.nodes) (σ : Sigma) :
    Ordered (expand B H σ).nodes := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rcases (expand_mem_iff B H σ y).mp hy with hyH | ⟨x, hxH, rfl⟩
    · exact hord.1 y hyH
    · intro k hk
      rcases List.mem_append.mp hk with hkx | hkd
      · exact hord.1 x hxH k hkx
      · simp at hkd; omega
  · intro y hy p hp
    rcases (expand_mem_iff B H σ y).mp hy with hyH | ⟨x, hxH, rfl⟩
    · rw [expand_mem_iff]; exact Or.inl (hord.2.1 y hyH p hp)
    · by_cases hpeq : p = x ++ [degree H.nodes x + 1]
      · subst hpeq; exact hy
      · rw [expand_mem_iff]
        exact Or.inl (hord.2.1 x hxH p (prefix_of_proper_prefix_concat hp hpeq))
  · intro p i hpi j hj0 hjle
    rcases (expand_mem_iff B H σ (p ++ [i])).mp hpi with hpiH | ⟨x, hxH, heq⟩
    · rw [expand_mem_iff]; exact Or.inl (hord.2.2 p i hpiH j hj0 hjle)
    · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      by_cases hjeq : j = degree H.nodes p + 1
      · subst hjeq; exact hpi
      · have hjle' : j ≤ degree H.nodes p := by omega
        have hdpos : 0 < degree H.nodes p := by omega
        have hdeg_mem : p ++ [degree H.nodes p] ∈ H.nodes := mem_degree_of_pos hdpos
        rw [expand_mem_iff]
        exact Or.inl (hord.2.2 p (degree H.nodes p) hdeg_mem j hj0 hjle')

lemma expand_label_sub_child {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x : Node} {i : ℕ}
    (h : x ++ [i] ∈ (expand B H σ).nodes) :
    (expand B H σ).label (x ++ [i]) ⊆ (expand B H σ).label x := by
  rcases (expand_mem_iff B H σ (x ++ [i])).mp h with hH | ⟨z, hzH, heq⟩
  · have hxH : x ∈ H.nodes := hv.1.2.1 (x ++ [i]) hH x ⟨[i], rfl⟩
    rw [expand_label_old B H σ hH, expand_label_old B H σ hxH]
    have hsub : H.label (x ++ [i]) ⊆ H.label x := label_sub_of_prefix hv x [i] hH
    intro q hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_biUnion.mpr ⟨p, hsub hp, hpq⟩
  · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
    rw [expand_label_new B H σ hzH, expand_label_old B H σ hzH]
    exact Finset.inter_subset_left

/-! ### Step 2 (`horizontal`) & Step 3 (`stage3`) -/

lemma horizontal_label_nil {Q : Type} (K : TreeData Q) :
    (horizontal K).label [] = K.label [] := by
  simp [horizontal]

lemma horizontal_label_outside {Q : Type} {K : TreeData Q}
    (hout : ∀ x, x ∉ K.nodes → K.label x = ∅) {x : Node} (hx : x ∉ (horizontal K).nodes) :
    (horizontal K).label x = ∅ := by
  have hxK : x ∉ K.nodes := hx
  simp [horizontal, hout x hxK]

lemma horizontal_disjoint {Q : Type} {K : TreeData Q} (hord : Ordered K.nodes)
    {p : Node} {i j : ℕ} (hi : p ++ [i] ∈ K.nodes) (hj : p ++ [j] ∈ K.nodes) (hne : i ≠ j) :
    Disjoint ((horizontal K).label (p ++ [i])) ((horizontal K).label (p ++ [j])) := by
  rw [Finset.disjoint_left]
  intro q hqi hqj
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · simp only [horizontal, Finset.mem_filter] at hqi hqj
    have hi0 : 0 < i := hord.1 (p ++ [i]) hi i (by simp)
    exact hqj.2 ⟨p, j, [], i, rfl, hi0, hlt, hi, hqi.1⟩
  · simp only [horizontal, Finset.mem_filter] at hqi hqj
    have hj0 : 0 < j := hord.1 (p ++ [j]) hj j (by simp)
    exact hqi.2 ⟨p, i, [], j, rfl, hj0, hgt, hj, hqj.1⟩

lemma horizontal_label_sub_child {Q : Type} {K : TreeData Q}
    (hsub : ∀ x i, x ++ [i] ∈ K.nodes → K.label (x ++ [i]) ⊆ K.label x)
    {x : Node} {i : ℕ} (h : x ++ [i] ∈ K.nodes) :
    (horizontal K).label (x ++ [i]) ⊆ (horizontal K).label x := by
  intro q hq
  simp only [horizontal, Finset.mem_filter] at hq ⊢
  refine ⟨hsub x i h hq.1, ?_⟩
  rintro ⟨p, k, v, j, rfl, hj0, hjk, hpj, hqpj⟩
  exact hq.2 ⟨p, k, v ++ [i], j, by simp, hj0, hjk, hpj, hqpj⟩

lemma horizontal_child_exists {Q : Type} {K : TreeData Q} (hord : Ordered K.nodes)
    {p : Node} {i : ℕ} {q : Q}
    (hpq : q ∈ (horizontal K).label p) (hpi : p ++ [i] ∈ K.nodes)
    (hq : q ∈ K.label (p ++ [i])) :
    ∃ j, 0 < j ∧ j ≤ i ∧ p ++ [j] ∈ K.nodes ∧ q ∈ (horizontal K).label (p ++ [j]) := by
  have hi0 : 0 < i := hord.1 (p ++ [i]) hpi i (by simp)
  let S := (Finset.Icc 1 i).filter (fun j => p ++ [j] ∈ K.nodes ∧ q ∈ K.label (p ++ [j]))
  have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi0, le_rfl⟩, hpi, hq⟩
  let j0 := S.min' ⟨i, hiS⟩
  have hj0S : j0 ∈ S := Finset.min'_mem S ⟨i, hiS⟩
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hj0S
  obtain ⟨⟨hj01, hj0i⟩, hpj0, hqpj0⟩ := hj0S
  refine ⟨j0, hj01, hj0i, hpj0, ?_⟩
  simp only [horizontal, Finset.mem_filter]
  refine ⟨hqpj0, ?_⟩
  rintro ⟨p', k, v, j', heq, hj'0, hj'k, hp'j', hqp'j'⟩
  cases v using List.reverseRecOn with
  | nil =>
    have heq' : p ++ [j0] = p' ++ [k] := heq
    obtain ⟨rfl, rfl⟩ := append_singleton_inj heq'
    have hj'S : j' ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hj'0, by omega⟩, hp'j', hqp'j'⟩
    have hmin := Finset.min'_le S j' hj'S
    change j0 ≤ j' at hmin
    omega
  | append_singleton w last =>
    have heq' : p ++ [j0] = (p' ++ k :: w) ++ [last] := by simpa using heq
    obtain ⟨hp_eq, _⟩ := append_singleton_inj heq'
    simp only [horizontal, Finset.mem_filter] at hpq
    exact hpq.2 ⟨p', k, w, j', hp_eq, hj'0, hj'k, hp'j', hqp'j'⟩

lemma horizontal_dichotomy {Q : Type} {K : TreeData Q} (hord : Ordered K.nodes)
    (hsub : ∀ x i, x ++ [i] ∈ K.nodes → K.label (x ++ [i]) ⊆ K.label x) :
    ∀ x ∈ K.nodes, ∀ q ∈ K.label x,
      q ∈ (horizontal K).label x ∨
      ∃ p k v j, x = p ++ k :: v ∧ 0 < j ∧ j < k ∧
        p ++ [j] ∈ K.nodes ∧ q ∈ (horizontal K).label (p ++ [j]) := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro _ q hq
    left
    rwa [horizontal_label_nil]
  | append_singleton y i ih =>
    intro hyi q hq
    have hy : y ∈ K.nodes := hord.2.1 (y ++ [i]) hyi y ⟨[i], rfl⟩
    have hqy : q ∈ K.label y := hsub y i hyi hq
    rcases ih hy q hqy with hqy_hor | ⟨p, k, v, j, rfl, hj0, hjk, hpj, hqpj⟩
    · obtain ⟨j, hj0, hjle, hyj, hqyj⟩ := horizontal_child_exists hord hqy_hor hyi hq
      by_cases hjeq : j = i
      · subst hjeq
        exact Or.inl hqyj
      · exact Or.inr ⟨y, i, [], j, rfl, hj0, by omega, hyj, hqyj⟩
    · exact Or.inr ⟨p, k, v ++ [i], j, by simp, hj0, hjk, hpj, hqpj⟩

/-! ### Step 3 (`stage3`) & Step 4 (`stage4`) -/

lemma stage3_mem_iff {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) (x : Node) :
    x ∈ (stage3 B H σ).nodes ↔
      x ∈ (expand B H σ).nodes ∧ ((horizontal (expand B H σ)).label x).Nonempty := by
  simp [stage3, removeEmpty, horizontal]

lemma stage3_label_of_mem {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ (stage3 B H σ).nodes) :
    (stage3 B H σ).label x = (horizontal (expand B H σ)).label x := by
  change (if x ∈ (stage3 B H σ).nodes then (horizontal (expand B H σ)).label x else ∅) = _
  exact if_pos hx

lemma stage3_prefix_closed {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x p : Node}
    (hx : x ∈ (stage3 B H σ).nodes) (hp : p.IsPrefix x) :
    p ∈ (stage3 B H σ).nodes := by
  have hord1 := expand_ordered B hv.1 σ
  have hsub1 := fun u i (h : u ++ [i] ∈ (expand B H σ).nodes) => expand_label_sub_child B hv σ h
  obtain ⟨w, rfl⟩ := hp
  induction w using List.reverseRecOn with
  | nil => simpa using hx
  | append_singleton u i ih =>
    have hx' : (p ++ u) ++ [i] ∈ (stage3 B H σ).nodes := by simpa using hx
    obtain ⟨hmem1, hne2⟩ := (stage3_mem_iff B H σ ((p ++ u) ++ [i])).mp hx'
    have hpu1 : p ++ u ∈ (expand B H σ).nodes := hord1.2.1 _ hmem1 (p ++ u) ⟨[i], rfl⟩
    have hsub2 := horizontal_label_sub_child hsub1 hmem1
    exact ih ((stage3_mem_iff B H σ (p ++ u)).mpr ⟨hpu1, hne2.mono hsub2⟩)

lemma stage3_childLabels_sub {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) (x : Node) :
    childLabels (stage3 B H σ) x ⊆ (stage3 B H σ).label x := by
  intro q hq
  obtain ⟨y, hy_ch, hqy⟩ := Finset.mem_biUnion.mp hq
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hy3, i, rfl⟩ := hy_ch
  have hx3 : x ∈ (stage3 B H σ).nodes := stage3_prefix_closed B hv σ hy3 ⟨[i], rfl⟩
  rw [stage3_label_of_mem B H σ hy3] at hqy
  rw [stage3_label_of_mem B H σ hx3]
  have hy1 : x ++ [i] ∈ (expand B H σ).nodes := ((stage3_mem_iff B H σ _).mp hy3).1
  exact horizontal_label_sub_child (fun u j h => expand_label_sub_child B hv σ h) hy1 hqy

lemma stage4_mem_iff {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) (x : Node) :
    x ∈ (stage4 B H σ).nodes ↔
      x ∈ (stage3 B H σ).nodes ∧ ¬ ∃ p ∈ resetNodes (stage3 B H σ), p.IsPrefix x ∧ p ≠ x := by
  simp [stage4, prune]

lemma stage4_prefix_closed {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x q : Node}
    (hx : x ∈ (stage4 B H σ).nodes) (hq : q.IsPrefix x) :
    q ∈ (stage4 B H σ).nodes := by
  obtain ⟨hx3, hno⟩ := (stage4_mem_iff B H σ x).mp hx
  refine (stage4_mem_iff B H σ q).mpr ⟨stage3_prefix_closed B hv σ hx3 hq, ?_⟩
  rintro ⟨p, hp_res, hpq, hpne⟩
  apply hno
  refine ⟨p, hp_res, hpq.trans hq, ?_⟩
  intro hpx
  subst hpx
  exact hpne (eq_of_prefix_of_length_eq hpq (le_antisymm hpq.length_le hq.length_le))

lemma stage4_positive {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x : Node} (hx : x ∈ (stage4 B H σ).nodes) :
    Positive x := by
  have hx3 := ((stage4_mem_iff B H σ x).mp hx).1
  have hx1 := ((stage3_mem_iff B H σ x).mp hx3).1
  exact (expand_ordered B hv.1 σ).1 x hx1

lemma stage4_label_of_mem {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ (stage4 B H σ).nodes) :
    (stage4 B H σ).label x = (stage3 B H σ).label x := by
  change (if x ∈ (stage4 B H σ).nodes then (stage3 B H σ).label x else ∅) = _
  exact if_pos hx

lemma stage4_children_of_reset {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hres : x ∈ resetNodes (stage3 B H σ)) :
    children (stage4 B H σ).nodes x = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  simp only [children, Finset.mem_filter] at hy
  obtain ⟨hy4, i, rfl⟩ := hy
  obtain ⟨_, hno⟩ := (stage4_mem_iff B H σ (x ++ [i])).mp hy4
  exact hno ⟨x, hres, ⟨[i], rfl⟩, by simp⟩

lemma stage4_childLabels_ssubset {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x : Node} (hx : x ∈ (stage4 B H σ).nodes) :
    childLabels (stage4 B H σ) x ⊂ (stage4 B H σ).label x := by
  obtain ⟨hx3, hno⟩ := (stage4_mem_iff B H σ x).mp hx
  rw [stage4_label_of_mem B H σ hx]
  by_cases hres : x ∈ resetNodes (stage3 B H σ)
  · have hch0 := stage4_children_of_reset B H σ hres
    have hcl0 : childLabels (stage4 B H σ) x = ∅ := by simp [childLabels, hch0]
    rw [hcl0, Finset.empty_ssubset]
    rw [stage3_label_of_mem B H σ hx3]
    exact ((stage3_mem_iff B H σ x).mp hx3).2
  · have hch_eq : children (stage4 B H σ).nodes x = children (stage3 B H σ).nodes x := by
      ext y
      simp only [children, Finset.mem_filter]
      refine ⟨fun ⟨hy4, hi⟩ => ⟨((stage4_mem_iff B H σ y).mp hy4).1, hi⟩, ?_⟩
      rintro ⟨hy3, i, rfl⟩
      refine ⟨(stage4_mem_iff B H σ (x ++ [i])).mpr ⟨hy3, ?_⟩, i, rfl⟩
      rintro ⟨p, hpres, hpxi, hpne⟩
      have hpx : p.IsPrefix x := prefix_of_proper_prefix_concat hpxi hpne
      by_cases hpeqx : p = x
      · subst hpeqx; exact hres hpres
      · exact hno ⟨p, hpres, hpx, hpeqx⟩
    have hcl_eq : childLabels (stage4 B H σ) x = childLabels (stage3 B H σ) x := by
      unfold childLabels
      rw [hch_eq]
      refine Finset.biUnion_congr rfl fun y hy => ?_
      rw [ ← hch_eq] at hy
      exact stage4_label_of_mem B H σ (Finset.mem_filter.mp hy).1
    rw [hcl_eq]
    have hsub := stage3_childLabels_sub B hv σ x
    refine ssubset_of_subset_of_ne hsub fun heq => hres ?_
    exact Finset.mem_filter.mpr ⟨hx3, heq.symm⟩

lemma exists_stage4_anc {Q Sigma : Type} (B : NBW Q Sigma) {H : TreeData Q}
    (_hv : Valid H) (σ : Sigma) {u : Node} (hu : u ∈ (stage3 B H σ).nodes) :
    (u ∈ (stage4 B H σ).nodes) ∨
    (∃ v ∈ (stage4 B H σ).nodes, v ∈ resetNodes (stage3 B H σ) ∧ v.IsPrefix u ∧ v ≠ u) := by
  by_cases hu4 : u ∈ (stage4 B H σ).nodes
  · exact Or.inl hu4
  · right
    rw [stage4_mem_iff, not_and] at hu4
    have hex := hu4 hu
    rw [Classical.not_not] at hex
    let S := (Finset.range u.length).filter (fun k => u.take k ∈ resetNodes (stage3 B H σ))
    have hSne : S.Nonempty := by
      obtain ⟨p, hpres, hpu, hpne⟩ := hex
      have hplen : p.length < u.length :=
        lt_of_le_of_ne hpu.length_le (fun hl => hpne (eq_of_prefix_of_length_eq hpu hl))
      have htk : u.take p.length = p := by
        obtain ⟨t, rfl⟩ := hpu
        exact List.take_left
      refine ⟨p.length, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplen, ?_⟩⟩
      rwa [htk]
    let k0 := S.min' hSne
    have hk0S : k0 ∈ S := Finset.min'_mem S hSne
    simp only [S, Finset.mem_filter, Finset.mem_range] at hk0S
    obtain ⟨hk0_lt, hk0_res⟩ := hk0S
    let v := u.take k0
    have hvu : v.IsPrefix u := List.take_prefix k0 u
    have hvne : v ≠ u := by
      intro heq
      have hl := congrArg List.length heq
      rw [List.length_take_of_le (Nat.le_of_lt hk0_lt)] at hl
      omega
    have hv3 : v ∈ (stage3 B H σ).nodes := (Finset.mem_filter.mp hk0_res).1
    have hv4 : v ∈ (stage4 B H σ).nodes := by
      refine (stage4_mem_iff B H σ v).mpr ⟨hv3, ?_⟩
      rintro ⟨p, hpres, hpv, hpne⟩
      have hplen : p.length < k0 := by
        have hvlen : v.length = k0 := List.length_take_of_le (Nat.le_of_lt hk0_lt)
        have hle := hpv.length_le
        rw [hvlen] at hle
        exact lt_of_le_of_ne hle (fun hl => hpne (eq_of_prefix_of_length_eq hpv (hl.trans hvlen.symm)))
      have htk : u.take p.length = p := by
        obtain ⟨t, rfl⟩ := hpv.trans hvu
        exact List.take_left
      have hpS : p.length ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans hplen hk0_lt), ?_⟩
        rwa [htk]
      have hmin := Finset.min'_le S p.length hpS
      change k0 ≤ p.length at hmin
      omega
    exact ⟨v, hv4, hk0_res, hvu, hvne⟩

/-! ### Step 5 (`compress` & `compressed`) -/

def childRank (T : Finset Node) (x : Node) (i : ℕ) : ℕ :=
  (T.filter fun y => ∃ j, y = x ++ [j] ∧ j < i).card + 1

lemma compress_nil (T : Finset Node) : compress T [] = [] := rfl

lemma getElem!_append_left {x y : List ℕ} {k : ℕ} (hk : k < x.length) :
    (x ++ y)[k]! = x[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  have hk' : k < (x ++ y).length := by simp; omega
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk, List.getElem_append_left hk]

lemma getElem!_append_singleton_last (x : Node) (i : ℕ) :
    (x ++ [i])[x.length]! = i := by
  rw [List.getElem!_eq_getElem?_getD]
  have hk' : x.length < (x ++ [i]).length := by simp
  rw [List.getElem?_eq_getElem hk', List.getElem_append_right le_rfl]
  simp

lemma compress_concat (T : Finset Node) (x : Node) (i : ℕ) :
    compress T (x ++ [i]) = compress T x ++ [childRank T x i] := by
  unfold compress childRank
  simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton]
  congr 1
  · refine List.map_congr_left fun k hk => ?_
    have hlt : k < x.length := List.mem_range.mp hk
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt), getElem!_append_left hlt]
  · rw [List.take_left, getElem!_append_singleton_last]

lemma compress_length (T : Finset Node) (x : Node) :
    (compress T x).length = x.length := by
  simp [compress]

lemma compress_prefix (T : Finset Node) {p x : Node} (hp : p.IsPrefix x) :
    (compress T p).IsPrefix (compress T x) := by
  obtain ⟨w, rfl⟩ := hp
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u i ih =>
    rw [← List.append_assoc, compress_concat]
    exact ih.trans ⟨[childRank T (p ++ u) i], rfl⟩

lemma childRank_eq_card_range (T : Finset Node) (x : Node) (i : ℕ) :
    childRank T x i = ((Finset.range i).filter (fun j => x ++ [j] ∈ T)).card + 1 := by
  unfold childRank
  congr 1
  have himg : (T.filter fun y => ∃ j, y = x ++ [j] ∧ j < i) =
      ((Finset.range i).filter (fun j => x ++ [j] ∈ T)).image (fun j => x ++ [j]) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hyT, j, rfl, hji⟩
      exact ⟨j, ⟨hji, hyT⟩, rfl⟩
    · rintro ⟨j, ⟨hji, hjT⟩, rfl⟩
      exact ⟨hjT, j, rfl, hji⟩
  rw [himg, Finset.card_image_of_injective]
  intro j1 j2 h
  exact (append_singleton_inj h).2

lemma childRank_strict_mono {T : Finset Node} {x : Node} {i1 i2 : ℕ}
    (h1 : x ++ [i1] ∈ T) (hlt : i1 < i2) :
    childRank T x i1 < childRank T x i2 := by
  rw [childRank_eq_card_range, childRank_eq_card_range]
  have hss : (Finset.range i1).filter (fun j => x ++ [j] ∈ T) ⊂
      (Finset.range i2).filter (fun j => x ++ [j] ∈ T) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, h1⟩, by simp⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨lt_trans hj.1 hlt, hj.2⟩
  have hc := Finset.card_lt_card hss
  omega

lemma childRank_pos (T : Finset Node) (x : Node) (i : ℕ) :
    0 < childRank T x i := by
  unfold childRank; omega

lemma childRank_le {T : Finset Node} (hpos : ∀ u ∈ T, Positive u)
    (x : Node) {i : ℕ} (hi : 0 < i) :
    childRank T x i ≤ i := by
  rw [childRank_eq_card_range]
  have hsub : (Finset.range i).filter (fun j => x ++ [j] ∈ T) ⊆ Finset.Icc 1 (i - 1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hj ⊢
    have hj0 : 0 < j := hpos (x ++ [j]) hj.2 j (by simp)
    omega
  have hc := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hc
  omega

lemma childRank_surj {T : Finset Node} {x : Node} :
    ∀ (i : ℕ), x ++ [i] ∈ T → ∀ s, 0 < s → s ≤ childRank T x i →
      ∃ j ≤ i, x ++ [j] ∈ T ∧ childRank T x j = s := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hiT s hs0 hsle
    by_cases hseq : s = childRank T x i
    · exact ⟨i, le_rfl, hiT, hseq.symm⟩
    · have hslt : s < childRank T x i := lt_of_le_of_ne hsle hseq
      rw [childRank_eq_card_range] at hslt
      let A := (Finset.range i).filter (fun j => x ++ [j] ∈ T)
      have hA_card_gt : s < A.card + 1 := hslt
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      let i' := A.max' hAne
      have hi'A : i' ∈ A := Finset.max'_mem A hAne
      simp only [A, Finset.mem_filter, Finset.mem_range] at hi'A
      obtain ⟨hi'lt, hi'T⟩ := hi'A
      have hAeq : A = insert i' ((Finset.range i').filter (fun j => x ++ [j] ∈ T)) := by
        ext j
        simp only [A, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨hji, hjT⟩
          have hjle : j ≤ i' := Finset.le_max' A j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hji, hjT⟩)
          by_cases hjeq : j = i'
          · exact Or.inl hjeq
          · exact Or.inr ⟨by omega, hjT⟩
        · rintro (rfl | ⟨hji', hjT⟩)
          · exact ⟨hi'lt, hi'T⟩
          · exact ⟨lt_trans hji' hi'lt, hjT⟩
      have hcardA : A.card = ((Finset.range i').filter (fun j => x ++ [j] ∈ T)).card + 1 := by
        rw [hAeq, Finset.card_insert_of_notMem (by simp)]
      have hsle' : s ≤ childRank T x i' := by
        rw [childRank_eq_card_range]
        omega
      obtain ⟨j, hjle', hjT, hjr⟩ := ih i' hi'lt hi'T s hs0 hsle'
      exact ⟨j, le_trans hjle' (Nat.le_of_lt hi'lt), hjT, hjr⟩

lemma compress_inj_on {T : Finset Node}
    (hpref : ∀ u ∈ T, ∀ p, p.IsPrefix u → p ∈ T) :
    ∀ x ∈ T, ∀ y ∈ T, compress T x = compress T y → x = y := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro _ y _ heq
    have hl := congrArg List.length heq
    rw [compress_nil, compress_length] at hl
    exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | append_singleton x' i ih =>
    intro hx y hy heq
    cases y using List.reverseRecOn with
    | nil =>
      have hl := congrArg List.length heq
      rw [compress_nil, compress_length] at hl
      simp at hl
    | append_singleton y' j =>
      rw [compress_concat, compress_concat] at heq
      obtain ⟨heq_pre, heq_rk⟩ := append_singleton_inj heq
      have hx' : x' ∈ T := hpref (x' ++ [i]) hx x' ⟨[i], rfl⟩
      have hy' : y' ∈ T := hpref (y' ++ [j]) hy y' ⟨[j], rfl⟩
      have hxy' : x' = y' := ih hx' y' hy' heq_pre
      subst hxy'
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exfalso
        have := childRank_strict_mono hx hlt
        omega
      · rfl
      · exfalso
        have := childRank_strict_mono hy hgt
        omega

lemma compressed_label_of_mem {Q : Type} {K : TreeData Q}
    (hpref : ∀ u ∈ K.nodes, ∀ p, p.IsPrefix u → p ∈ K.nodes)
    {x : Node} (hx : x ∈ K.nodes) :
    (compressed K).label (compress K.nodes x) = K.label x := by
  unfold compressed
  simp only
  have hflt : (K.nodes.filter fun y => compress K.nodes y = compress K.nodes x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨hy, heq⟩ => compress_inj_on hpref y hy x hx heq, fun hyx => ⟨hyx ▸ hx, hyx ▸ rfl⟩⟩
  rw [hflt, Finset.singleton_biUnion]

lemma compressed_children_of_mem {Q : Type} {K : TreeData Q}
    (hpref : ∀ u ∈ K.nodes, ∀ p, p.IsPrefix u → p ∈ K.nodes)
    {x : Node} (hx : x ∈ K.nodes) :
    children (compressed K).nodes (compress K.nodes x) =
      (children K.nodes x).image (compress K.nodes) := by
  ext z
  simp only [compressed, children, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨y, hyK, rfl⟩, r, heq⟩
    cases y using List.reverseRecOn with
    | nil =>
      rw [compress_nil] at heq
      simp at heq
    | append_singleton x' i =>
      rw [compress_concat] at heq
      obtain ⟨heq_pre, _⟩ := append_singleton_inj heq
      have hx'K : x' ∈ K.nodes := hpref (x' ++ [i]) hyK x' ⟨[i], rfl⟩
      have hx'eq : x' = x := compress_inj_on hpref x' hx'K x hx heq_pre
      rw [hx'eq] at hyK ⊢
      exact ⟨x ++ [i], ⟨hyK, i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨hyK, i, rfl⟩, rfl⟩
    exact ⟨⟨x ++ [i], hyK, rfl⟩, childRank K.nodes x i, compress_concat K.nodes x i⟩

lemma compressed_valid {Q : Type} {K : TreeData Q}
    (_hpos : ∀ u ∈ K.nodes, Positive u)
    (hpref : ∀ u ∈ K.nodes, ∀ p, p.IsPrefix u → p ∈ K.nodes)
    (hroot : [] ∈ K.nodes)
    (hne : ∀ u ∈ K.nodes, (K.label u).Nonempty)
    (hdisj : ∀ p i j, p ++ [i] ∈ K.nodes → p ++ [j] ∈ K.nodes → i ≠ j →
      Disjoint (K.label (p ++ [i])) (K.label (p ++ [j])))
    (hssub : ∀ u ∈ K.nodes, childLabels K u ⊂ K.label u) :
    Valid (compressed K) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- Positive
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    intro r hr
    unfold compress at hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    omega
  · -- Prefix-closed
    intro z hz p hp
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hz
    have hlen : p.length ≤ x.length := by
      simpa [compress_length] using hp.length_le
    have htk_pre : (x.take p.length).IsPrefix x := List.take_prefix p.length x
    have htkK : x.take p.length ∈ K.nodes := hpref x hxK _ htk_pre
    have hcp_pre : (compress K.nodes (x.take p.length)).IsPrefix (compress K.nodes x) :=
      compress_prefix K.nodes htk_pre
    have hcp_len : (compress K.nodes (x.take p.length)).length = p.length := by
      rw [compress_length, List.length_take_of_le hlen]
    have hp_eq : p = compress K.nodes (x.take p.length) := by
      obtain ⟨t1, ht1⟩ := hp
      obtain ⟨t2, ht2⟩ := hcp_pre
      have := congrArg (List.take p.length) (ht1.trans ht2.symm)
      rw [List.take_left, List.take_left' hcp_len] at this
      exact this
    rw [hp_eq]
    exact Finset.mem_image.mpr ⟨x.take p.length, htkK, rfl⟩
  · -- Left-closed
    intro p' r hp'r s hs0 hsle
    obtain ⟨y, hyK, heq⟩ := Finset.mem_image.mp hp'r
    cases y using List.reverseRecOn with
    | nil =>
      rw [compress_nil] at heq; simp at heq
    | append_singleton x i =>
      rw [compress_concat] at heq
      obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      obtain ⟨j, _, hjK, hjrk⟩ := childRank_surj i hyK s hs0 hsle
      refine Finset.mem_image.mpr ⟨x ++ [j], hjK, ?_⟩
      rw [compress_concat, hjrk]
  · -- [] ∈ nodes
    exact Finset.mem_image.mpr ⟨[], hroot, rfl⟩
  · -- outside label = ∅
    intro z hz
    simp only [compressed, Finset.mem_image, not_exists, not_and] at hz ⊢
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨y, ⟨hy1, hy2⟩, _⟩
    exact hz y hy1 hy2
  · -- nonempty labels
    intro z hz
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hz
    rw [compressed_label_of_mem hpref hxK]
    exact hne x hxK
  · -- sibling disjointness
    intro p' r1 r2 h1 h2 hrne
    obtain ⟨y1, hy1K, heq1⟩ := Finset.mem_image.mp h1
    obtain ⟨y2, hy2K, heq2⟩ := Finset.mem_image.mp h2
    cases y1 using List.reverseRecOn with
    | nil => rw [compress_nil] at heq1; simp at heq1
    | append_singleton x1 i1 =>
      cases y2 using List.reverseRecOn with
      | nil => rw [compress_nil] at heq2; simp at heq2
      | append_singleton x2 i2 =>
        have h1' := heq1; rw [compress_concat] at h1'
        have h2' := heq2; rw [compress_concat] at h2'
        obtain ⟨hx1p, hr1⟩ := append_singleton_inj h1'
        obtain ⟨hx2p, hr2⟩ := append_singleton_inj h2'
        have hx1K : x1 ∈ K.nodes := hpref _ hy1K x1 ⟨[i1], rfl⟩
        have hx2K : x2 ∈ K.nodes := hpref _ hy2K x2 ⟨[i2], rfl⟩
        have hx12 : x1 = x2 := compress_inj_on hpref x1 hx1K x2 hx2K (hx1p.trans hx2p.symm)
        subst hx12
        have hine : i1 ≠ i2 := fun hieq => hrne (hr1 ▸ hr2 ▸ hieq ▸ rfl)
        rw [← heq1, ← heq2, compressed_label_of_mem hpref hy1K, compressed_label_of_mem hpref hy2K]
        exact hdisj x1 i1 i2 hy1K hy2K hine
  · -- childLabels ⊂ label
    intro z hz
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hz
    have hcl : childLabels (compressed K) (compress K.nodes x) = childLabels K x := by
      unfold childLabels
      rw [compressed_children_of_mem hpref hxK]
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, hq⟩
        rw [compressed_label_of_mem hpref (Finset.mem_filter.mp hy).1] at hq
        exact ⟨y, hy, hq⟩
      · rintro ⟨y, hy, hq⟩
        refine ⟨compress K.nodes y, ⟨y, hy, rfl⟩, ?_⟩
        rwa [compressed_label_of_mem hpref (Finset.mem_filter.mp hy).1]
    rw [hcl, compressed_label_of_mem hpref hxK]
    exact hssub x hxK

lemma stage4_valid_compressed {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (σ : Sigma)
    (hroot : [] ∈ (stage4 B H.val σ).nodes) :
    Valid (compressed (stage4 B H.val σ)) := by
  have hv := H.property
  refine compressed_valid
    (fun u hu => stage4_positive B hv σ hu)
    (fun u hu p hp => stage4_prefix_closed B hv σ hu hp)
    hroot
    (fun u hu => by
      rw [stage4_label_of_mem B H.val σ hu]
      have hu3 := ((stage4_mem_iff B H.val σ u).mp hu).1
      rw [stage3_label_of_mem B H.val σ hu3]
      exact ((stage3_mem_iff B H.val σ u).mp hu3).2)
    (fun p i j hi4 hj4 hne => by
      rw [stage4_label_of_mem B H.val σ hi4, stage4_label_of_mem B H.val σ hj4]
      have hi3 := ((stage4_mem_iff B H.val σ _).mp hi4).1
      have hj3 := ((stage4_mem_iff B H.val σ _).mp hj4).1
      rw [stage3_label_of_mem B H.val σ hi3, stage3_label_of_mem B H.val σ hj3]
      have hi1 := ((stage3_mem_iff B H.val σ _).mp hi3).1
      have hj1 := ((stage3_mem_iff B H.val σ _).mp hj3).1
      exact horizontal_disjoint (expand_ordered B hv.1 σ) hi1 hj1 hne)
    (fun u hu => stage4_childLabels_ssubset B hv σ hu)

lemma root_mem_stage4_iff {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (σ : Sigma) :
    [] ∈ (stage4 B H.val σ).nodes ↔
      ((H.val.label []).biUnion (fun q => B.delta q σ)).Nonempty := by
  rw [stage4_mem_iff]
  have hno : ¬ ∃ p ∈ resetNodes (stage3 B H.val σ), p.IsPrefix [] ∧ p ≠ [] := by
    rintro ⟨p, _, hp, hne⟩
    exact hne (List.prefix_nil.mp hp)
  simp only [hno, not_false_eq_true, and_true, stage3_mem_iff, horizontal_label_nil]
  have hroot1 : [] ∈ (expand B H.val σ).nodes := by
    rw [expand_mem_iff]; exact Or.inl H.property.2.1
  simp [hroot1, expand_label_old B H.val σ H.property.2.1]

lemma successor_eq_some_iff {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (σ : Sigma)
    (H' : History Q) :
    successor B H σ = some H' ↔ H'.val = compressed (stage4 B H.val σ) := by
  unfold successor asHistory
  split_ifs with hv
  · simp [Subtype.ext_iff, eq_comm]
  · constructor
    · intro h; cases h
    · intro heq
      exfalso
      apply hv
      rw [← heq]
      exact H'.property

lemma root_mem_stage4_of_succ {Q Sigma : Type} (B : NBW Q Sigma) {H H' : History Q} {σ : Sigma}
    (hsucc : successor B H σ = some H') :
    [] ∈ (stage4 B H.val σ).nodes := by
  have heq := (successor_eq_some_iff B H σ H').mp hsucc
  have hroot_c : [] ∈ (compressed (stage4 B H.val σ)).nodes := heq ▸ H'.property.2.1
  obtain ⟨y, hy4, hyc⟩ := Finset.mem_image.mp hroot_c
  have hy0 : y = [] := by
    have hl := congrArg List.length hyc
    rw [compress_length] at hl
    exact List.eq_nil_of_length_eq_zero hl
  rwa [← hy0]

lemma succ_label_root {Q Sigma : Type} (B : NBW Q Sigma) {H H' : History Q} {σ : Sigma}
    (hsucc : successor B H σ = some H') :
    H'.val.label [] = (H.val.label []).biUnion (fun q => B.delta q σ) := by
  have heq := (successor_eq_some_iff B H σ H').mp hsucc
  have hroot4 : [] ∈ (stage4 B H.val σ).nodes := root_mem_stage4_of_succ B hsucc
  have hroot3 : [] ∈ (stage3 B H.val σ).nodes := ((stage4_mem_iff B H.val σ []).mp hroot4).1
  rw [heq]
  have hc := compressed_label_of_mem
    (fun u hu p hp => stage4_prefix_closed B H.property σ hu hp) hroot4
  rw [compress_nil] at hc
  rw [hc, stage4_label_of_mem B H.val σ hroot4, stage3_label_of_mem B H.val σ hroot3,
    horizontal_label_nil, expand_label_old B H.val σ H.property.2.1]

lemma initialHistory_of_nonempty {Q Sigma : Type} (B : NBW Q Sigma) (hne : B.initial.Nonempty) :
    ∃ H0 : History Q, initialHistory B = some H0 ∧ H0.val = initialData B := by
  have hv : Valid (initialData B) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simp [initialData] at hx; subst hx
      intro i hi; simp at hi
    · intro x hx p hp
      simp [initialData] at hx; subst hx
      have hp0 : p = [] := List.prefix_nil.mp hp
      subst hp0; simp [initialData]
    · intro p i hpi
      simp [initialData] at hpi
    · simp [initialData]
    · intro x hx
      simp [initialData] at hx
      simp [initialData, hx]
    · intro x hx
      simp [initialData] at hx; subst hx
      simpa [initialData] using hne
    · intro p i _ hpi
      simp [initialData] at hpi
    · intro x hx
      simp [initialData] at hx; subst hx
      have hch : children (initialData B).nodes [] = ∅ := by
        ext y
        simp only [children, initialData, Finset.mem_filter, Finset.mem_singleton,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl, i, h⟩
        simp at h
      have hcl : childLabels (initialData B) [] = ∅ := by simp [childLabels, hch]
      rw [hcl, Finset.empty_ssubset]
      simpa [initialData] using hne
  exact ⟨⟨initialData B, hv⟩, dif_pos hv, rfl⟩

/-! ### Forward Direction `(→)` -/

lemma noninc_stabilizes (f : ℕ → ℕ) (h : ∀ k, f (k + 1) ≤ f k) :
    ∃ K, ∀ k ≥ K, f k = f K := by
  have hle_zero : ∀ (g : ℕ → ℕ), (∀ k, g (k + 1) ≤ g k) → ∀ t, g t ≤ g 0 := by
    intro g hg t
    induction t with
    | zero => exact le_rfl
    | succ t iht => exact le_trans (hg t) iht
  suffices ∀ m : ℕ, ∀ g : ℕ → ℕ, (∀ k, g (k + 1) ≤ g k) → g 0 ≤ m → ∃ K, ∀ k ≥ K, g k = g K from
    this (f 0) f h le_rfl
  intro m
  induction m with
  | zero =>
    intro g hg hg0
    refine ⟨0, fun k _ => ?_⟩
    have := hle_zero g hg k
    omega
  | succ m ih =>
    intro g hg hg0
    by_cases hall : ∀ k, g k = g 0
    · exact ⟨0, fun k _ => hall k⟩
    · obtain ⟨k0, hk0⟩ := Classical.not_forall.mp hall
      have hk0_le : g k0 ≤ g 0 := hle_zero g hg k0
      have hk0_lt : g k0 < g 0 := lt_of_le_of_ne hk0_le hk0
      let g' : ℕ → ℕ := fun t => g (k0 + t)
      have hg'0 : g' 0 ≤ m := by
        change g (k0 + 0) ≤ m
        rw [Nat.add_zero]
        omega
      obtain ⟨K', hK'⟩ := ih g' (fun t => by simpa [g', Nat.add_assoc] using hg (k0 + t)) hg'0
      refine ⟨k0 + K', fun k hk => ?_⟩
      have heq := hK' (k - k0) (by omega)
      simpa [g', show k0 + (k - k0) = k by omega] using heq

lemma step_owner_transition {Q Sigma : Type} [Fintype Q]
    (B : NBW Q Sigma) {H H' : History Q} {σ : Sigma}
    (hsucc : successor B H σ = some H')
    {q q' : Q} (hdelta : q' ∈ B.delta q σ)
    {x x' : Node} (hx : x ∈ H.val.nodes) (hown : q ∈ own H.val x)
    (hx' : x' ∈ H'.val.nodes) (hown' : q' ∈ own H'.val x')
    {p : Node} (hp_pre : p.IsPrefix x) (hp_pre' : p.IsPrefix x')
    (hp4 : p ∈ (stage4 B H.val σ).nodes)
    (hp_comp : compress (stage4 B H.val σ).nodes p = p)
    (hp_nores : p ∉ resetNodes (stage3 B H.val σ)) :
    (x = p → q' ∈ B.accepting → p.length < x'.length) ∧
    (∀ c rest, x = p ++ c :: rest →
      ∃ j c', 0 < j ∧ j ≤ c ∧ p ++ [j] ∈ (stage4 B H.val σ).nodes ∧
        c' = childRank (stage4 B H.val σ).nodes p j ∧ c' ≤ j ∧
        (p ++ [c']).IsPrefix x') := by
  have hv := H.property
  have hv' := H'.property
  have hH'_eq : H'.val = compressed (stage4 B H.val σ) :=
    (successor_eq_some_iff B H σ H').mp hsucc
  let H1 := expand B H.val σ
  let H3 := stage3 B H.val σ
  let H4 := stage4 B H.val σ
  have hord1 := expand_ordered B hv.1 σ
  have hsub1 := fun u i (h : u ++ [i] ∈ H1.nodes) => expand_label_sub_child B hv σ h
  have hpref4 : ∀ u ∈ H4.nodes, ∀ r, r.IsPrefix u → r ∈ H4.nodes :=
    fun u hu r hr => stage4_prefix_closed B hv σ hu hr
  have hpos4 : ∀ u ∈ H4.nodes, Positive u :=
    fun u hu => stage4_positive B hv σ hu
  have hqx : q ∈ H.val.label x := (Finset.mem_sdiff.mp hown).1
  have hq'1_x : q' ∈ H1.label x := by
    rw [expand_label_old B H.val σ hx]
    exact Finset.mem_biUnion.mpr ⟨q, hqx, hdelta⟩
  -- Helper: given w ∈ H1.nodes with q' ∈ H1.label w and p <+: w, no proper prefix of p can jump left
  have no_jump_before_p : ∀ (p0 : Node) (k j : ℕ) (v : List ℕ),
      p0.length < p.length → p.IsPrefix (p0 ++ k :: v) →
      0 < j → j < k → p0 ++ [j] ∈ H1.nodes →
      q' ∈ (horizontal H1).label (p0 ++ [j]) → False := by
    intro p0 k j v hp0len hp_p0 hj0 hjk hp0j hq'p0j
    have hp0j_3 : p0 ++ [j] ∈ H3.nodes :=
      (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
    have hp0k_pre_p : (p0 ++ [k]).IsPrefix p := by
      obtain ⟨t, ht⟩ := hp_p0
      have htk := congrArg (List.take (p0.length + 1)) ht
      have h1 : (p ++ t).take (p0.length + 1) = p.take (p0.length + 1) :=
        List.take_append_of_le_length (by omega)
      have h2 : (p0 ++ k :: v).take (p0.length + 1) = p0 ++ [k] := by
        have : p0 ++ k :: v = (p0 ++ [k]) ++ v := by simp
        rw [this, List.take_left' (by simp)]
      rw [h1, h2] at htk
      rw [← htk]
      exact List.take_prefix _ _
    have hp0_pre_p : p0.IsPrefix p := List.IsPrefix.trans ⟨[k], rfl⟩ hp0k_pre_p
    rcases exists_stage4_anc B hv σ hp0j_3 with hp0j_4 | ⟨v0, _, hv0_res, hv0_pre, hv0_ne⟩
    · have hp0_comp : compress H4.nodes p0 = p0 := by
        have hcp := compress_prefix H4.nodes hp0_pre_p
        rw [hp_comp] at hcp
        obtain ⟨t1, ht1⟩ := hcp
        obtain ⟨t2, ht2⟩ := hp0_pre_p
        have htk := congrArg (List.take p0.length) (ht1.trans ht2.symm)
        rw [List.take_left' (compress_length H4.nodes p0), List.take_left] at htk
        exact htk
      let z' := compress H4.nodes (p0 ++ [j])
      have hz'_eq : z' = p0 ++ [childRank H4.nodes p0 j] := by
        simp [z', compress_concat, hp0_comp]
      have hz'_mem : z' ∈ H'.val.nodes := by
        rw [hH'_eq]; exact Finset.mem_image.mpr ⟨p0 ++ [j], hp0j_4, rfl⟩
      have hq'z' : q' ∈ H'.val.label z' := by
        rw [hH'_eq, compressed_label_of_mem hpref4 hp0j_4,
          stage4_label_of_mem B H.val σ hp0j_4, stage3_label_of_mem B H.val σ hp0j_3]
        exact hq'p0j
      have hz'_pre_x' : z'.IsPrefix x' :=
        (mem_label_iff_prefix_own hv' hx' hown' hz'_mem).mp hq'z'
      have hp0k_pre_x' : (p0 ++ [k]).IsPrefix x' := hp0k_pre_p.trans hp_pre'
      rw [hz'_eq] at hz'_pre_x'
      obtain ⟨t1, ht1⟩ := hz'_pre_x'
      obtain ⟨t2, ht2⟩ := hp0k_pre_x'
      have htk := congrArg (List.take (p0.length + 1)) (ht1.trans ht2.symm)
      have hl1 : ((p0 ++ [childRank H4.nodes p0 j]) ++ t1).take (p0.length + 1) =
          p0 ++ [childRank H4.nodes p0 j] := List.take_left' (by simp)
      have hl2 : ((p0 ++ [k]) ++ t2).take (p0.length + 1) = p0 ++ [k] :=
        List.take_left' (by simp)
      rw [hl1, hl2] at htk
      have hrk_eq : childRank H4.nodes p0 j = k := (append_singleton_inj htk).2
      have hrk_le : childRank H4.nodes p0 j ≤ j := childRank_le hpos4 p0 hj0
      omega
    · have hv0_pre_p0 : v0.IsPrefix p0 := prefix_of_proper_prefix_concat hv0_pre hv0_ne
      have hv0_pre_p : v0.IsPrefix p := hv0_pre_p0.trans hp0_pre_p
      have hv0_ne_p : v0 ≠ p := by
        intro heq; subst heq
        have := hv0_pre_p0.length_le
        omega
      obtain ⟨_, hno4⟩ := (stage4_mem_iff B H.val σ p).mp hp4
      exact hno4 ⟨v0, hv0_res, hv0_pre_p, hv0_ne_p⟩
  -- Helper: once we have p ++ [j] <+: u with u ∈ H3.nodes and q' ∈ H3.label u (0 < j),
  -- push through stage4 and compress
  have push_child : ∀ {u : Node} {j : ℕ},
      0 < j → (p ++ [j]).IsPrefix u → u ∈ H3.nodes → q' ∈ H3.label u →
      p ++ [j] ∈ H4.nodes ∧ (p ++ [childRank H4.nodes p j]).IsPrefix x' := by
    intro u j hj0 hpju hu3 hq'u3
    have hpj3 : p ++ [j] ∈ H3.nodes := stage3_prefix_closed B hv σ hu3 hpju
    have hpj4 : p ++ [j] ∈ H4.nodes := by
      refine (stage4_mem_iff B H.val σ (p ++ [j])).mpr ⟨hpj3, ?_⟩
      rintro ⟨r, hr_res, hr_pre, hr_ne⟩
      have hr_pre_p : r.IsPrefix p := prefix_of_proper_prefix_concat hr_pre hr_ne
      by_cases hreq : r = p
      · subst hreq; exact hp_nores hr_res
      · exact ((stage4_mem_iff B H.val σ p).mp hp4).2 ⟨r, hr_res, hr_pre_p, hreq⟩
    rcases exists_stage4_anc B hv σ hu3 with hu4 | ⟨v0, hv0_4, hv0_res, hv0_pre, _⟩
    · let z' := compress H4.nodes u
      have hz'mem : z' ∈ H'.val.nodes := by
        rw [hH'_eq]; exact Finset.mem_image.mpr ⟨u, hu4, rfl⟩
      have hq'z' : q' ∈ H'.val.label z' := by
        rw [hH'_eq, compressed_label_of_mem hpref4 hu4, stage4_label_of_mem B H.val σ hu4]
        exact hq'u3
      have hz'_pre : z'.IsPrefix x' := (mem_label_iff_prefix_own hv' hx' hown' hz'mem).mp hq'z'
      have hcp_pj : (compress H4.nodes (p ++ [j])).IsPrefix z' := compress_prefix H4.nodes hpju
      rw [compress_concat, hp_comp] at hcp_pj
      exact ⟨hpj4, hcp_pj.trans hz'_pre⟩
    · have hpj_pre_v0 : (p ++ [j]).IsPrefix v0 := by
        by_cases hlen : v0.length ≤ p.length
        · exfalso
          obtain ⟨t1, ht1⟩ := hv0_pre
          obtain ⟨t2, ht2⟩ := hpju
          have htk := congrArg (List.take v0.length) (ht1.trans ht2.symm)
          rw [List.take_left] at htk
          have hrhs : ((p ++ [j]) ++ t2).take v0.length = p.take v0.length := by
            rw [List.append_assoc, List.take_append_of_le_length hlen]
          rw [hrhs] at htk
          have hv0_pre_p : v0.IsPrefix p := htk ▸ List.take_prefix v0.length p
          by_cases hv0eq : v0 = p
          · subst hv0eq; exact hp_nores hv0_res
          · exact ((stage4_mem_iff B H.val σ p).mp hp4).2 ⟨v0, hv0_res, hv0_pre_p, hv0eq⟩
        · have hge : (p ++ [j]).length ≤ v0.length := by simp; omega
          obtain ⟨t1, ht1⟩ := hpju
          obtain ⟨t2, ht2⟩ := hv0_pre
          have htk := congrArg (List.take (p ++ [j]).length) (ht1.trans ht2.symm)
          rw [List.take_left, List.take_append_of_le_length hge] at htk
          exact htk ▸ List.take_prefix _ _
      have hq'v0_3 : q' ∈ H3.label v0 := by
        obtain ⟨t, rfl⟩ := hv0_pre
        have hsub : ∀ (a : Node) (b : List ℕ), a ++ b ∈ H3.nodes → H3.label (a ++ b) ⊆ H3.label a := by
          intro a b
          induction b using List.reverseRecOn with
          | nil => intro _; simp
          | append_singleton b' last ih =>
            intro hab
            have hab' : (a ++ b') ++ [last] ∈ H3.nodes := by simpa using hab
            have hab1 : a ++ b' ∈ H3.nodes := stage3_prefix_closed B hv σ hab' ⟨[last], rfl⟩
            have hs1 : H3.label ((a ++ b') ++ [last]) ⊆ childLabels H3 (a ++ b') :=
              Finset.subset_biUnion_of_mem H3.label
                (Finset.mem_filter.mpr ⟨hab', last, rfl⟩)
            have hs2 := stage3_childLabels_sub B hv σ (a ++ b')
            have hs3 : H3.label (a ++ (b' ++ [last])) ⊆ H3.label (a ++ b') := by
              simpa using hs1.trans hs2
            exact hs3.trans (ih hab1)
        exact hsub v0 t hu3 hq'u3
      let z' := compress H4.nodes v0
      have hz'mem : z' ∈ H'.val.nodes := by
        rw [hH'_eq]; exact Finset.mem_image.mpr ⟨v0, hv0_4, rfl⟩
      have hq'z' : q' ∈ H'.val.label z' := by
        rw [hH'_eq, compressed_label_of_mem hpref4 hv0_4, stage4_label_of_mem B H.val σ hv0_4]
        exact hq'v0_3
      have hz'_pre : z'.IsPrefix x' := (mem_label_iff_prefix_own hv' hx' hown' hz'mem).mp hq'z'
      have hcp_pj : (compress H4.nodes (p ++ [j])).IsPrefix z' := compress_prefix H4.nodes hpj_pre_v0
      rw [compress_concat, hp_comp] at hcp_pj
      exact ⟨hpj4, hcp_pj.trans hz'_pre⟩
  refine ⟨?_, ?_⟩
  · intro hxp hq'acc
    subst hxp
    let d := degree H.val.nodes x
    let w := x ++ [d + 1]
    have hw1 : w ∈ H1.nodes := by
      rw [expand_mem_iff]; exact Or.inr ⟨x, hx, rfl⟩
    have hq'w1 : q' ∈ H1.label w := by
      rw [expand_label_new B H.val σ hx]
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨q, hqx, hdelta⟩, hq'acc⟩
    rcases horizontal_dichotomy hord1 hsub1 w hw1 q' hq'w1 with hq'w2 | ⟨p0, k, v, j, heq, hj0, hjk, hp0j, hq'p0j⟩
    · have hw3 : w ∈ H3.nodes := (stage3_mem_iff B H.val σ w).mpr ⟨hw1, ⟨q', hq'w2⟩⟩
      have hq'w3 : q' ∈ H3.label w := by rwa [stage3_label_of_mem B H.val σ hw3]
      obtain ⟨_, hpre'⟩ := push_child (Nat.succ_pos d) (List.prefix_refl w) hw3 hq'w3
      have hlen := hpre'.length_le
      simp at hlen; omega
    · by_cases hp0len : p0.length < x.length
      · exfalso
        exact no_jump_before_p p0 k j v hp0len (heq ▸ ⟨[d + 1], rfl⟩) hj0 hjk hp0j hq'p0j
      · have hv_nil : v = [] := by
          have hl := congrArg List.length heq
          simp [w] at hl
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hv_nil
        obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
        have hp0j_3 : x ++ [j] ∈ H3.nodes := (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
        have hq'p0j_3 : q' ∈ H3.label (x ++ [j]) := by rwa [stage3_label_of_mem B H.val σ hp0j_3]
        obtain ⟨_, hpre'⟩ := push_child hj0 (List.prefix_refl _) hp0j_3 hq'p0j_3
        have hlen := hpre'.length_le
        simp at hlen; omega
  · intro c rest hxeq
    have hc0 : 0 < c := hv.1.1 x hx c (by simp [hxeq])
    have hx1 : x ∈ H1.nodes := (expand_mem_iff B H.val σ x).mpr (Or.inl hx)
    rcases horizontal_dichotomy hord1 hsub1 x hx1 q' hq'1_x with hq'x2 | ⟨p0, k, v, j, heq, hj0, hjk, hp0j, hq'p0j⟩
    · have hx3 : x ∈ H3.nodes := (stage3_mem_iff B H.val σ x).mpr ⟨hx1, ⟨q', hq'x2⟩⟩
      have hq'x3 : q' ∈ H3.label x := by rwa [stage3_label_of_mem B H.val σ hx3]
      have hp_c_pre : (p ++ [c]).IsPrefix x := by rw [hxeq]; exact ⟨rest, by simp⟩
      obtain ⟨hpc4, hpre'⟩ := push_child hc0 hp_c_pre hx3 hq'x3
      exact ⟨c, childRank H4.nodes p c, hc0, le_rfl, hpc4, rfl, childRank_le hpos4 p hc0, hpre'⟩
    · by_cases hp0len : p0.length < p.length
      · exfalso
        exact no_jump_before_p p0 k j v hp0len (heq ▸ hp_pre) hj0 hjk hp0j hq'p0j
      · by_cases hp0eq : p0.length = p.length
        · have heq_comb : p ++ c :: rest = p0 ++ k :: v := hxeq.symm.trans heq
          have hp0_eq_p : p0 = p := by
            have htk := congrArg (List.take p.length) heq_comb
            rw [List.take_left, List.take_left' hp0eq] at htk
            exact htk.symm
          subst hp0_eq_p
          have hkc : k = c := by
            have := List.append_cancel_left heq_comb.symm
            exact (List.cons.inj this).1
          subst hkc
          have hpj3 : p0 ++ [j] ∈ H3.nodes := (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
          have hq'pj3 : q' ∈ H3.label (p0 ++ [j]) := by rwa [stage3_label_of_mem B H.val σ hpj3]
          obtain ⟨hpj4, hpre'⟩ := push_child hj0 (List.prefix_refl _) hpj3 hq'pj3
          exact ⟨j, childRank H4.nodes p0 j, hj0, Nat.le_of_lt hjk, hpj4, rfl,
            childRank_le hpos4 p0 hj0, hpre'⟩
        · have hp_c_pre_p0 : (p ++ [c]).IsPrefix p0 := by
            have heq_comb : (p ++ [c]) ++ rest = p0 ++ k :: v := by simpa [hxeq] using heq
            have htk := congrArg (List.take (p.length + 1)) heq_comb
            rw [List.take_left' (by simp), List.take_append_of_le_length (by omega)] at htk
            exact htk ▸ List.take_prefix _ _
          have hp0j_3 : p0 ++ [j] ∈ H3.nodes := (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
          have hq'p0j_3 : q' ∈ H3.label (p0 ++ [j]) := by rwa [stage3_label_of_mem B H.val σ hp0j_3]
          have hp_c_pre_p0j : (p ++ [c]).IsPrefix (p0 ++ [j]) := hp_c_pre_p0.trans ⟨[j], rfl⟩
          obtain ⟨hpc4, hpre'⟩ := push_child hc0 hp_c_pre_p0j hp0j_3 hq'p0j_3
          exact ⟨c, childRank H4.nodes p c, hc0, le_rfl, hpc4, rfl, childRank_le hpos4 p hc0, hpre'⟩

lemma lemma_9_mp {Q Sigma : Type} [Fintype Q]
    (B : NBW Q Sigma) (α : ℕ → Sigma) (hlang : α ∈ language B) :
    ∃ (ρ : ℕ → History Q) (x : Node),
      Positive x ∧ IsTrace B α ρ ∧
      (∃ N, ∀ i ≥ N, x ∉ unstable B (ρ i) (α i)) ∧
      (∀ N, ∃ i ≥ N, x ∈ acceptingNodes B (ρ i) (α i)) := by
  obtain ⟨r, ⟨hr0, hrstep⟩, qf, hqf_acc, hqf_inf⟩ := hlang
  obtain ⟨H0, hinit, hH0_val⟩ := initialHistory_of_nonempty B ⟨r 0, hr0⟩
  have hr0_lbl : r 0 ∈ H0.val.label [] := by simp [hH0_val, initialData, hr0]
  have hnext_ex : ∀ (i : ℕ) (H : History Q), r i ∈ H.val.label [] →
      ∃ H' : History Q, successor B H (α i) = some H' ∧ r (i + 1) ∈ H'.val.label [] := by
    intro i H hri
    have hmem_bi : r (i + 1) ∈ (H.val.label []).biUnion (fun q => B.delta q (α i)) :=
      Finset.mem_biUnion.mpr ⟨r i, hri, hrstep i⟩
    have hroot4 : [] ∈ (stage4 B H.val (α i)).nodes :=
      (root_mem_stage4_iff B H (α i)).mpr ⟨r (i + 1), hmem_bi⟩
    have hv' := stage4_valid_compressed B H (α i) hroot4
    let H' : History Q := ⟨compressed (stage4 B H.val (α i)), hv'⟩
    have hsucc : successor B H (α i) = some H' := (successor_eq_some_iff B H (α i) H').mpr rfl
    have hri1 : r (i + 1) ∈ H'.val.label [] := by
      rw [succ_label_root B hsucc]
      exact hmem_bi
    exact ⟨H', hsucc, hri1⟩
  let traceState : ∀ i : ℕ, {H : History Q // r i ∈ H.val.label []} :=
    Nat.rec ⟨H0, hr0_lbl⟩ (fun i ih =>
      ⟨Classical.choose (hnext_ex i ih.val ih.property),
       (Classical.choose_spec (hnext_ex i ih.val ih.property)).2⟩)
  let ρ : ℕ → History Q := fun i => (traceState i).val
  have hρ_lbl : ∀ i, r i ∈ (ρ i).val.label [] := fun i => (traceState i).property
  have htr : IsTrace B α ρ := by
    refine ⟨hinit, fun i => ?_⟩
    exact (Classical.choose_spec (hnext_ex i (traceState i).val (traceState i).property)).1
  have hown_ex : ∀ i, ∃ x ∈ (ρ i).val.nodes, r i ∈ own (ρ i).val x := fun i => by
    obtain ⟨x, hx, _, hown⟩ := exists_own_of_mem_label (ρ i).property (ρ i).property.2.1 (hρ_lbl i)
    exact ⟨x, hx, hown⟩
  let xSeq : ℕ → Node := fun i => Classical.choose (hown_ex i)
  have hxSeq_mem : ∀ i, xSeq i ∈ (ρ i).val.nodes := fun i => (Classical.choose_spec (hown_ex i)).1
  have hxSeq_own : ∀ i, r i ∈ own (ρ i).val (xSeq i) := fun i => (Classical.choose_spec (hown_ex i)).2
  by_contra hno_wit
  have hdepth : ∀ d : ℕ, ∃ (p : Node) (N : ℕ), p.length = d ∧
      ∀ i ≥ N, p.IsPrefix (xSeq i) ∧ p ∉ unstable B (ρ i) (α i) := by
    intro d
    induction d with
    | zero =>
      refine ⟨[], 0, rfl, fun i _ => ⟨List.nil_prefix, ?_⟩⟩
      simp only [unstable, Finset.mem_filter, not_and, not_or, not_not]
      intro _
      exact ⟨root_mem_stage4_of_succ B (htr.2 i), rfl⟩
    | succ d ih =>
      obtain ⟨p, N, hplen, hp_inv⟩ := ih
      have hp_pos : Positive p :=
        (ρ N).property.1.1 p ((ρ N).property.1.2.1 _ (hxSeq_mem N) p (hp_inv N le_rfl).1)
      have hnot_inf_acc : ¬ ∀ M, ∃ i ≥ M, p ∈ acceptingNodes B (ρ i) (α i) := by
        intro hacc
        exact hno_wit ⟨ρ, p, hp_pos, htr, ⟨N, fun i hi => (hp_inv i hi).2⟩, hacc⟩
      obtain ⟨M0, hM0_pre⟩ := Classical.not_forall.mp hnot_inf_acc
      have hM0 : ∀ i ≥ M0, p ∉ acceptingNodes B (ρ i) (α i) := by
        intro i hi hpacc
        exact hM0_pre ⟨i, hi, hpacc⟩
      let M := max N M0
      have hp_nores : ∀ i ≥ M, p ∉ resetNodes (stage3 B (ρ i).val (α i)) := by
        intro i hi hres
        have hiN : N ≤ i := le_trans (le_max_left N M0) hi
        have hiM0 : M0 ≤ i := le_trans (le_max_right N M0) hi
        obtain ⟨hpre_i, hstab_i⟩ := hp_inv i hiN
        have hp_mem_i : p ∈ (ρ i).val.nodes := (ρ i).property.1.2.1 _ (hxSeq_mem i) p hpre_i
        simp only [unstable, Finset.mem_filter, hp_mem_i, true_and, not_or, not_not] at hstab_i
        have hacc_i : p ∈ acceptingNodes B (ρ i) (α i) :=
          Finset.mem_filter.mpr ⟨hp_mem_i, hres, hstab_i.1, hstab_i.2⟩
        exact hM0 i hiM0 hacc_i
      -- Find i0 ≥ M with r (i0 + 1) = qf ∈ B.accepting
      obtain ⟨t_acc, ht_acc_ge, ht_acc_eq⟩ := hqf_inf (M + 1)
      let i0 := t_acc - 1
      have hi0_ge : M ≤ i0 := by omega
      have hri0_acc : r (i0 + 1) ∈ B.accepting := by
        have : i0 + 1 = t_acc := by omega
        rw [this, ht_acc_eq]
        exact hqf_acc
      -- Show p.length < (xSeq (i0 + 1)).length
      have hstep_at : ∀ i ≥ M,
          (xSeq i = p → r (i + 1) ∈ B.accepting → p.length < (xSeq (i + 1)).length) ∧
          (∀ c rest, xSeq i = p ++ c :: rest →
            ∃ j c', 0 < j ∧ j ≤ c ∧ p ++ [j] ∈ (stage4 B (ρ i).val (α i)).nodes ∧
              c' = childRank (stage4 B (ρ i).val (α i)).nodes p j ∧ c' ≤ j ∧
              (p ++ [c']).IsPrefix (xSeq (i + 1))) := by
        intro i hi
        have hiN : N ≤ i := le_trans (le_max_left N M0) hi
        have hi1N : N ≤ i + 1 := by omega
        obtain ⟨hpre_i, hstab_i⟩ := hp_inv i hiN
        have hp_mem_i : p ∈ (ρ i).val.nodes := (ρ i).property.1.2.1 _ (hxSeq_mem i) p hpre_i
        simp only [unstable, Finset.mem_filter, hp_mem_i, true_and, not_or, not_not] at hstab_i
        exact step_owner_transition B (htr.2 i) (hrstep i) (hxSeq_mem i) (hxSeq_own i)
          (hxSeq_mem (i + 1)) (hxSeq_own (i + 1)) hpre_i (hp_inv (i + 1) hi1N).1
          hstab_i.1 hstab_i.2 (hp_nores i hi)
      let M1 := i0 + 1
      have hlen_M1 : p.length < (xSeq M1).length := by
        obtain ⟨w, hw⟩ := (hp_inv i0 (le_trans (le_max_left N M0) hi0_ge)).1
        cases w with
        | nil =>
          have hxp : xSeq i0 = p := by simpa using hw.symm
          exact (hstep_at i0 hi0_ge).1 hxp hri0_acc
        | cons c rest =>
          obtain ⟨_, c', _, _, _, _, _, hpre'⟩ := (hstep_at i0 hi0_ge).2 c rest hw.symm
          have hl := hpre'.length_le
          simp at hl; omega
      have hlen_all : ∀ k : ℕ, p.length < (xSeq (M1 + k)).length := by
        intro k
        induction k with
        | zero => simpa using hlen_M1
        | succ k ihk =>
          have hiN : N ≤ M1 + k := by omega
          have hiM : M ≤ M1 + k := by omega
          obtain ⟨w, hw⟩ := (hp_inv (M1 + k) hiN).1
          cases w with
          | nil =>
            rw [← hw] at ihk; simp at ihk
          | cons c rest =>
            obtain ⟨_, c', _, _, _, _, _, hpre'⟩ := (hstep_at (M1 + k) hiM).2 c rest hw.symm
            have hl := hpre'.length_le
            simp [Nat.add_assoc] at hl ⊢; omega
      let cSeq : ℕ → ℕ := fun k => (xSeq (M1 + k))[p.length]!
      have hcSeq_split : ∀ k : ℕ, ∃ rest, xSeq (M1 + k) = p ++ cSeq k :: rest := by
        intro k
        have hiN : N ≤ M1 + k := by omega
        obtain ⟨w, hw⟩ := (hp_inv (M1 + k) hiN).1
        cases w with
        | nil =>
          have hl := hlen_all k
          rw [← hw] at hl; simp at hl
        | cons c rest =>
          have hc_eq : cSeq k = c := by
            simp only [cSeq, ← hw]
            have h1 : p ++ c :: rest = (p ++ [c]) ++ rest := by simp
            rw [h1, getElem!_append_left (by simp), getElem!_append_singleton_last]
          exact ⟨rest, by rw [hc_eq, hw]⟩
      have hcSeq_step : ∀ k : ℕ,
          ∃ j ≤ cSeq k, p ++ [j] ∈ (stage4 B (ρ (M1 + k)).val (α (M1 + k))).nodes ∧
            cSeq (k + 1) = childRank (stage4 B (ρ (M1 + k)).val (α (M1 + k))).nodes p j ∧
            cSeq (k + 1) ≤ j := by
        intro k
        obtain ⟨rest, hsplit⟩ := hcSeq_split k
        have hiM : M ≤ M1 + k := by omega
        obtain ⟨j, c', _, hjc, hpj4, hc'rk, hc'j, hpre'⟩ := (hstep_at (M1 + k) hiM).2 (cSeq k) rest hsplit
        have hc_next : cSeq (k + 1) = c' := by
          obtain ⟨t, ht⟩ := hpre'
          simp only [cSeq, show M1 + (k + 1) = M1 + k + 1 by omega, ← ht]
          rw [getElem!_append_left (by simp), getElem!_append_singleton_last]
        exact ⟨j, hjc, hpj4, hc_next.trans hc'rk, hc_next ▸ hc'j⟩
      have hcSeq_noninc : ∀ k, cSeq (k + 1) ≤ cSeq k := by
        intro k
        obtain ⟨j, hjc, _, _, hcj⟩ := hcSeq_step k
        omega
      obtain ⟨K, hK⟩ := noninc_stabilizes cSeq hcSeq_noninc
      let cStar := cSeq K
      let N_next := M1 + K
      refine ⟨p ++ [cStar], N_next, by simp [hplen], fun i hi => ?_⟩
      let k := i - M1
      have hkK : K ≤ k := by omega
      have hik : M1 + k = i := by omega
      have hck : cSeq k = cStar := hK k hkK
      have hck1 : cSeq (k + 1) = cStar := hK (k + 1) (by omega)
      obtain ⟨rest, hsplit⟩ := hcSeq_split k
      rw [hik, hck] at hsplit
      have hpre_next : (p ++ [cStar]).IsPrefix (xSeq i) := ⟨rest, by simpa using hsplit.symm⟩
      obtain ⟨j, hjc, hpj4, hcrk, hcj⟩ := hcSeq_step k
      rw [hik] at hpj4 hcrk
      rw [hck] at hjc
      rw [hck1] at hcrk hcj
      have hj_eq : j = cStar := by omega
      subst hj_eq
      have hiN : N ≤ i := by omega
      obtain ⟨hpre_p_i, hstab_p_i⟩ := hp_inv i hiN
      have hp_mem_i : p ∈ (ρ i).val.nodes := (ρ i).property.1.2.1 _ (hxSeq_mem i) p hpre_p_i
      simp only [unstable, Finset.mem_filter, hp_mem_i, true_and, not_or, not_not] at hstab_p_i
      refine ⟨hpre_next, ?_⟩
      simp only [unstable, Finset.mem_filter, not_and, not_or, not_not]
      intro _
      refine ⟨hpj4, ?_⟩
      rw [compress_concat, hstab_p_i.2, ← hcrk]
  obtain ⟨p, N, hplen, hp_inv⟩ := hdepth (Fintype.card Q)
  have hp_mem : p ∈ (ρ N).val.nodes :=
    (ρ N).property.1.2.1 _ (hxSeq_mem N) p (hp_inv N le_rfl).1
  have hlt := length_lt_card_of_mem (ρ N) hp_mem
  omega

/-! ### Backward Direction `(←)` -/

def ReachOn {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma)
    (a b : ℕ) (qa qb : Q) : Prop :=
  ∃ f : ℕ → Q, f a = qa ∧ f b = qb ∧ ∀ i, a ≤ i → i < b → f (i + 1) ∈ B.delta (f i) (α i)

def AccReachOn {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma)
    (a b : ℕ) (qa qb : Q) : Prop :=
  ∃ f : ℕ → Q, f a = qa ∧ f b = qb ∧
    (∀ i, a ≤ i → i < b → f (i + 1) ∈ B.delta (f i) (α i)) ∧
    ∃ j, a < j ∧ j ≤ b ∧ f j ∈ B.accepting

lemma reachOn_refl {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma) (a : ℕ) (q : Q) :
    ReachOn B α a a q q :=
  ⟨fun _ => q, rfl, rfl, fun _ h1 h2 => by omega⟩

lemma reachOn_step {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma)
    {a b : ℕ} (hab : a ≤ b) {qa qb qc : Q}
    (hr : ReachOn B α a b qa qb) (hd : qc ∈ B.delta qb (α b)) :
    ReachOn B α a (b + 1) qa qc := by
  obtain ⟨f, hfa, hfb, hfstep⟩ := hr
  refine ⟨fun t => if t = b + 1 then qc else f t, ?_, by simp, ?_⟩
  · dsimp only
    rw [if_neg (by omega)]
    exact hfa
  · intro i hai hib
    dsimp only
    by_cases hieq : i = b
    · subst hieq
      rw [if_pos rfl, if_neg (by omega), hfb]
      exact hd
    · rw [if_neg (by omega), if_neg (by omega)]
      exact hfstep i hai (by omega)

lemma accReachOn_of_reachOn_acc {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma)
    {a b : ℕ} (hab : a ≤ b) {qa qb qc : Q}
    (hr : ReachOn B α a b qa qb) (hd : qc ∈ B.delta qb (α b)) (hacc : qc ∈ B.accepting) :
    AccReachOn B α a (b + 1) qa qc := by
  obtain ⟨f, hfa, hfb, hfstep⟩ := reachOn_step B α hab hr hd
  exact ⟨f, hfa, hfb, hfstep, b + 1, by omega, le_rfl, hfb ▸ hacc⟩

lemma accReachOn_step {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma)
    {a b : ℕ} (_hab : a ≤ b) {qa qb qc : Q}
    (hr : AccReachOn B α a b qa qb) (hd : qc ∈ B.delta qb (α b)) :
    AccReachOn B α a (b + 1) qa qc := by
  obtain ⟨f, hfa, hfb, hfstep, j, haj, hjb, hfj⟩ := hr
  have hab' : a < b := lt_of_lt_of_le haj hjb
  refine ⟨fun t => if t = b + 1 then qc else f t, ?_, by simp, ?_, j, haj, by omega, ?_⟩
  · dsimp only
    rw [if_neg (by omega)]
    exact hfa
  · intro i hai hib
    dsimp only
    by_cases hieq : i = b
    · subst hieq
      rw [if_pos rfl, if_neg (by omega), hfb]
      exact hd
    · rw [if_neg (by omega), if_neg (by omega)]
      exact hfstep i hai (by omega)
  · dsimp only
    rw [if_neg (by omega)]
    exact hfj

lemma root_reach_of_trace {Q Sigma : Type} {B : NBW Q Sigma} {α : ℕ → Sigma}
    {ρ : ℕ → History Q} (htr : IsTrace B α ρ) :
    ∀ m : ℕ, ∀ q ∈ (ρ m).val.label [], ∃ q0 ∈ B.initial, ReachOn B α 0 m q0 q
  | 0, q, hq => by
    have hinit := htr.1
    unfold initialHistory asHistory at hinit
    split_ifs at hinit with hv
    have h0 : ρ 0 = ⟨initialData B, hv⟩ := Option.some.inj hinit.symm
    rw [h0] at hq
    simp only [initialData, ↓reduceIte] at hq
    exact ⟨q, hq, reachOn_refl B α 0 q⟩
  | m + 1, q, hq => by
    rw [succ_label_root B (htr.2 m)] at hq
    obtain ⟨q', hq', hd⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨q0, hq0, hr⟩ := root_reach_of_trace htr m q' hq'
    exact ⟨q0, hq0, reachOn_step B α (Nat.zero_le m) hr hd⟩

inductive LayerReach {Q : Type} (L : ℕ → Finset Q) (R : ℕ → Q → Q → Prop) :
    ℕ → ℕ → Q → Q → Prop where
  | refl {k : ℕ} {q : Q} (hq : q ∈ L k) : LayerReach L R k 0 q q
  | step {k d : ℕ} {q q' q'' : Q}
      (h1 : LayerReach L R k d q q')
      (h2 : R (k + d) q' q'')
      (h3 : q'' ∈ L (k + d + 1)) : LayerReach L R k (d + 1) q q''

lemma layerReach_mem_start {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    {k d : ℕ} {q q' : Q} (h : LayerReach L R k d q q') : q ∈ L k := by
  induction h with
  | refl hq => exact hq
  | step _ _ _ ih => exact ih

lemma layerReach_exists_pred {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    (hpred : ∀ k, ∀ q'' ∈ L (k + 1), ∃ q' ∈ L k, R k q' q'') :
    ∀ k d, ∀ q'' ∈ L (k + d), ∃ q ∈ L k, LayerReach L R k d q q''
  | _, 0, q'', hq'' => ⟨q'', hq'', LayerReach.refl hq''⟩
  | k, d + 1, q'', hq'' => by
    obtain ⟨q', hq', hr⟩ := hpred (k + d) q'' hq''
    obtain ⟨q, hq, hlr⟩ := layerReach_exists_pred hpred k d q' hq'
    exact ⟨q, hq, LayerReach.step hlr hr hq''⟩

lemma layerReach_truncate {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    {k : ℕ} : ∀ {d e : ℕ} {q w : Q},
      LayerReach L R k (d + e) q w → ∃ u, LayerReach L R k d q u
  | _, 0, _, w, h => ⟨w, h⟩
  | _, _ + 1, _, _, h => by
    cases h with
    | step h1 _ _ => exact layerReach_truncate h1

lemma layerReach_uncons {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    {k : ℕ} : ∀ {d : ℕ} {q w : Q},
      LayerReach L R k (d + 1) q w →
      ∃ q1 ∈ L (k + 1), R k q q1 ∧ LayerReach L R (k + 1) d q1 w
  | 0, _, w, h => by
    cases h with
    | step h1 h2 h3 =>
      cases h1 with
      | refl _ =>
        exact ⟨w, by simpa using h3, by simpa using h2, LayerReach.refl (by simpa using h3)⟩
  | d + 1, _, w, h => by
    cases h with
    | step h1 h2 h3 =>
      obtain ⟨q1, hq1, hr1, hlr⟩ := layerReach_uncons h1
      refine ⟨q1, hq1, hr1, LayerReach.step hlr ?_ ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm 1 d] using h2
      · simpa [Nat.add_assoc, Nat.add_comm 1 d] using h3

lemma konig_layers {Q : Type} [Fintype Q]
    (L : ℕ → Finset Q) (R : ℕ → Q → Q → Prop)
    (hne : ∀ k, (L k).Nonempty)
    (hpred : ∀ k, ∀ q'' ∈ L (k + 1), ∃ q' ∈ L k, R k q' q'') :
    ∃ seq : ℕ → Q, (∀ k, seq k ∈ L k) ∧ (∀ k, R k (seq k) (seq (k + 1))) := by
  let Good : ℕ → Q → Prop := fun k q => q ∈ L k ∧ ∀ d, ∃ w, LayerReach L R k d q w
  have hGood0 : ∃ q0, Good 0 q0 := by
    have hex_d : ∀ d : ℕ, ∃ q ∈ L 0, ∃ w, LayerReach L R 0 d q w := by
      intro d
      obtain ⟨w, hw⟩ := hne d
      obtain ⟨q, hq, hlr⟩ := layerReach_exists_pred hpred 0 d w (by simpa using hw)
      exact ⟨q, hq, w, hlr⟩
    have : Nonempty Q := ⟨Classical.choose (hne 0)⟩
    let g : ℕ → Q := fun d => Classical.choose (hex_d d)
    obtain ⟨q0, hq0_inf⟩ := Finite.exists_infinite_fiber g
    have hq0_set : (g ⁻¹' {q0}).Infinite := Set.infinite_coe_iff.mp hq0_inf
    obtain ⟨d0, hd0⟩ := hq0_set.nonempty
    have hd0_eq : Classical.choose (hex_d d0) = q0 := hd0
    have hq0_L0 : q0 ∈ L 0 := hd0_eq ▸ (Classical.choose_spec (hex_d d0)).1
    refine ⟨q0, hq0_L0, fun d => ?_⟩
    obtain ⟨d', hd'_mem, hd'_not_lt⟩ := (hq0_set.sdiff (Set.finite_lt_nat d)).nonempty
    have hd'_ge : d ≤ d' := Nat.le_of_not_lt hd'_not_lt
    have hd'_eq : Classical.choose (hex_d d') = q0 := hd'_mem
    obtain ⟨w, hlr⟩ := (Classical.choose_spec (hex_d d')).2
    rw [hd'_eq] at hlr
    have hsplit : d' = d + (d' - d) := by omega
    rw [hsplit] at hlr
    exact layerReach_truncate hlr
  have hGood_step : ∀ k q, Good k q → ∃ q1, Good (k + 1) q1 ∧ R k q q1 := by
    intro k q ⟨_, hreach⟩
    have hex_d : ∀ d : ℕ, ∃ q1 ∈ L (k + 1), R k q q1 ∧ ∃ w, LayerReach L R (k + 1) d q1 w := by
      intro d
      obtain ⟨w, hlr⟩ := hreach (d + 1)
      obtain ⟨q1, hq1, hr, hlr'⟩ := layerReach_uncons hlr
      exact ⟨q1, hq1, hr, w, hlr'⟩
    have : Nonempty Q := ⟨Classical.choose (hne 0)⟩
    let h : ℕ → Q := fun d => Classical.choose (hex_d d)
    obtain ⟨q1, hq1_inf⟩ := Finite.exists_infinite_fiber h
    have hq1_set : (h ⁻¹' {q1}).Infinite := Set.infinite_coe_iff.mp hq1_inf
    obtain ⟨d0, hd0⟩ := hq1_set.nonempty
    have hd0_eq : Classical.choose (hex_d d0) = q1 := hd0
    have hspec0 := Classical.choose_spec (hex_d d0)
    have hq1_L : q1 ∈ L (k + 1) := hd0_eq ▸ hspec0.1
    have hr_q1 : R k q q1 := hd0_eq ▸ hspec0.2.1
    refine ⟨q1, ⟨hq1_L, fun d => ?_⟩, hr_q1⟩
    obtain ⟨d', hd'_mem, hd'_not_lt⟩ := (hq1_set.sdiff (Set.finite_lt_nat d)).nonempty
    have hd'_ge : d ≤ d' := Nat.le_of_not_lt hd'_not_lt
    have hd'_eq : Classical.choose (hex_d d') = q1 := hd'_mem
    obtain ⟨w, hlr⟩ := (Classical.choose_spec (hex_d d')).2.2
    rw [hd'_eq] at hlr
    have hsplit : d' = d + (d' - d) := by omega
    rw [hsplit] at hlr
    exact layerReach_truncate hlr
  let gSeq : ∀ k : ℕ, {q : Q // Good k q} :=
    Nat.rec ⟨Classical.choose hGood0, Classical.choose_spec hGood0⟩
      (fun k ih =>
        ⟨Classical.choose (hGood_step k ih.val ih.property),
         (Classical.choose_spec (hGood_step k ih.val ih.property)).1⟩)
  refine ⟨fun k => (gSeq k).val, fun k => (gSeq k).property.1, fun k => ?_⟩
  exact (Classical.choose_spec (hGood_step k (gSeq k).val (gSeq k).property)).2

lemma lemma_9_mpr {Q Sigma : Type} [Fintype Q]
    (B : NBW Q Sigma) (α : ℕ → Sigma)
    {ρ : ℕ → History Q} {x : Node}
    (htr : IsTrace B α ρ)
    (hstab_ex : ∃ N, ∀ i ≥ N, x ∉ unstable B (ρ i) (α i))
    (hacc_inf : ∀ N, ∃ i ≥ N, x ∈ acceptingNodes B (ρ i) (α i)) :
    α ∈ language B := by
  obtain ⟨N0, hstab⟩ := hstab_ex
  let tSeq : ℕ → ℕ :=
    Nat.rec (Classical.choose (hacc_inf N0))
      (fun _ prev => Classical.choose (hacc_inf (prev + 1)))
  have ht_succ : ∀ k, tSeq (k + 1) = Classical.choose (hacc_inf (tSeq k + 1)) := fun _ => rfl
  have ht0_ge : N0 ≤ tSeq 0 := (Classical.choose_spec (hacc_inf N0)).1
  have ht_acc : ∀ k, x ∈ acceptingNodes B (ρ (tSeq k)) (α (tSeq k)) := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hacc_inf N0)).2
    | succ k => exact (Classical.choose_spec (hacc_inf (tSeq k + 1))).2
  have ht_lt : ∀ k, tSeq k < tSeq (k + 1) := fun k => by
    rw [ht_succ k]
    have := (Classical.choose_spec (hacc_inf (tSeq k + 1))).1
    omega
  -- Stability properties of x for all i ≥ tSeq 0
  have hx_mem_t0 : x ∈ (ρ (tSeq 0)).val.nodes :=
    (Finset.mem_filter.mp (ht_acc 0)).1
  have hx_persist : ∀ d : ℕ,
      let i := tSeq 0 + d
      x ∈ (ρ i).val.nodes ∧
      x ∈ (stage4 B (ρ i).val (α i)).nodes ∧
      compress (stage4 B (ρ i).val (α i)).nodes x = x ∧
      (ρ (i + 1)).val.label x = (stage3 B (ρ i).val (α i)).label x := by
    intro d
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      have hst := hstab (tSeq 0) ht0_ge
      simp only [unstable, Finset.mem_filter, hx_mem_t0, true_and, not_or, not_not] at hst
      have hsucc_eq := (successor_eq_some_iff B (ρ (tSeq 0)) (α (tSeq 0)) (ρ (tSeq 0 + 1))).mp (htr.2 (tSeq 0))
      have hpref4 : ∀ u ∈ (stage4 B (ρ (tSeq 0)).val (α (tSeq 0))).nodes, ∀ p, p.IsPrefix u →
          p ∈ (stage4 B (ρ (tSeq 0)).val (α (tSeq 0))).nodes :=
        fun u hu p hp => stage4_prefix_closed B (ρ (tSeq 0)).property (α (tSeq 0)) hu hp
      have hlbl := compressed_label_of_mem hpref4 hst.1
      rw [hst.2] at hlbl
      exact ⟨hx_mem_t0, hst.1, hst.2, by rw [hsucc_eq, hlbl, stage4_label_of_mem B _ _ hst.1]⟩
    | succ d ih =>
      obtain ⟨_, hx4_prev, hxcomp_prev, _⟩ := ih
      let ip := tSeq 0 + d
      let i := tSeq 0 + (d + 1)
      have hsucc_prev := (successor_eq_some_iff B (ρ ip) (α ip) (ρ (ip + 1))).mp (htr.2 ip)
      have hx_mem_next : x ∈ (ρ i).val.nodes := by
        have : i = ip + 1 := by omega
        rw [this, hsucc_prev]
        exact Finset.mem_image.mpr ⟨x, hx4_prev, hxcomp_prev⟩
      have hst := hstab i (by omega)
      simp only [unstable, Finset.mem_filter, hx_mem_next, true_and, not_or, not_not] at hst
      have hsucc_eq := (successor_eq_some_iff B (ρ i) (α i) (ρ (i + 1))).mp (htr.2 i)
      have hpref4 : ∀ u ∈ (stage4 B (ρ i).val (α i)).nodes, ∀ p, p.IsPrefix u →
          p ∈ (stage4 B (ρ i).val (α i)).nodes :=
        fun u hu p hp => stage4_prefix_closed B (ρ i).property (α i) hu hp
      have hlbl := compressed_label_of_mem hpref4 hst.1
      rw [hst.2] at hlbl
      exact ⟨hx_mem_next, hst.1, hst.2, by rw [hsucc_eq, hlbl, stage4_label_of_mem B _ _ hst.1]⟩
  have hx_at : ∀ i ≥ tSeq 0,
      x ∈ (ρ i).val.nodes ∧
      x ∈ (stage4 B (ρ i).val (α i)).nodes ∧
      compress (stage4 B (ρ i).val (α i)).nodes x = x ∧
      (ρ (i + 1)).val.label x = (stage3 B (ρ i).val (α i)).label x := by
    intro i hi
    simpa [show tSeq 0 + (i - tSeq 0) = i by omega] using hx_persist (i - tSeq 0)
  -- At sSeq k := tSeq k + 1, children of x are empty
  let sSeq : ℕ → ℕ := fun k => tSeq k + 1
  have hs_lt : ∀ k, sSeq k < sSeq (k + 1) := fun k => by
    have := ht_lt k; simp [sSeq]; omega
  have ht0_le_tk : ∀ k, tSeq 0 ≤ tSeq k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => have := ht_lt k; omega
  have hx_leaf_after_acc : ∀ k, children (ρ (sSeq k)).val.nodes x = ∅ := by
    intro k
    have hacc_k := ht_acc k
    simp only [acceptingNodes, Finset.mem_filter] at hacc_k
    obtain ⟨_, hres_k, hx4_k, hxcomp_k⟩ := hacc_k
    have hsucc_eq := (successor_eq_some_iff B (ρ (tSeq k)) (α (tSeq k)) (ρ (sSeq k))).mp (htr.2 (tSeq k))
    have hpref4 : ∀ u ∈ (stage4 B (ρ (tSeq k)).val (α (tSeq k))).nodes, ∀ p, p.IsPrefix u →
        p ∈ (stage4 B (ρ (tSeq k)).val (α (tSeq k))).nodes :=
      fun u hu p hp => stage4_prefix_closed B (ρ (tSeq k)).property (α (tSeq k)) hu hp
    have hch := compressed_children_of_mem hpref4 hx4_k
    rw [hxcomp_k, stage4_children_of_reset B _ _ hres_k] at hch
    rw [hsucc_eq, hch]
    simp
  -- Inductive invariant from a = sSeq k forward
  have hseg_inv : ∀ (k d : ℕ),
      (∀ q ∈ (ρ (sSeq k + d)).val.label x,
        ∃ qa ∈ (ρ (sSeq k)).val.label x, ReachOn B α (sSeq k) (sSeq k + d) qa q) ∧
      (∀ y ∈ children (ρ (sSeq k + d)).val.nodes x, ∀ q ∈ (ρ (sSeq k + d)).val.label y,
        ∃ qa ∈ (ρ (sSeq k)).val.label x, AccReachOn B α (sSeq k) (sSeq k + d) qa q) := by
    intro k d
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      refine ⟨fun q hq => ⟨q, hq, reachOn_refl B α (sSeq k) q⟩, ?_⟩
      intro y hy
      rw [hx_leaf_after_acc k] at hy
      simp at hy
    | succ d ih =>
      let a := sSeq k
      let m := a + d
      have hm_ge_t0 : tSeq 0 ≤ m := by
        have := ht0_le_tk k
        simp [m, a, sSeq]; omega
      obtain ⟨hx_m, hx4_m, hxcomp_m, hlbl_next⟩ := hx_at m hm_ge_t0
      have hx3_m : x ∈ (stage3 B (ρ m).val (α m)).nodes :=
        ((stage4_mem_iff B (ρ m).val (α m) x).mp hx4_m).1
      have hsub31 : ∀ u ∈ (stage3 B (ρ m).val (α m)).nodes,
          (stage3 B (ρ m).val (α m)).label u ⊆ (expand B (ρ m).val (α m)).label u := by
        intro u hu q hq
        rw [stage3_label_of_mem B _ _ hu] at hq
        exact (Finset.mem_filter.mp hq).1
      have hm1_eq : sSeq k + (d + 1) = m + 1 := by simp [m, a, Nat.add_assoc]
      refine ⟨?_, ?_⟩
      · intro q hq
        rw [hm1_eq, hlbl_next] at hq
        have hq1 := hsub31 x hx3_m hq
        rw [expand_label_old B (ρ m).val (α m) hx_m] at hq1
        obtain ⟨q', hq'x, hd⟩ := Finset.mem_biUnion.mp hq1
        obtain ⟨qa, hqa, hr⟩ := ih.1 q' hq'x
        rw [hm1_eq]
        exact ⟨qa, hqa, reachOn_step B α (Nat.le_add_right a d) hr hd⟩
      · intro y' hy' q hq
        rw [hm1_eq] at hy' hq ⊢
        have hsucc_eq := (successor_eq_some_iff B (ρ m) (α m) (ρ (m + 1))).mp (htr.2 m)
        have hpref4 : ∀ u ∈ (stage4 B (ρ m).val (α m)).nodes, ∀ p, p.IsPrefix u →
            p ∈ (stage4 B (ρ m).val (α m)).nodes :=
          fun u hu p hp => stage4_prefix_closed B (ρ m).property (α m) hu hp
        have hch_eq := compressed_children_of_mem hpref4 hx4_m
        rw [hxcomp_m] at hch_eq
        rw [hsucc_eq, hch_eq] at hy'
        obtain ⟨y, hy_ch4, rfl⟩ := Finset.mem_image.mp hy'
        simp only [children, Finset.mem_filter] at hy_ch4
        obtain ⟨hy4, j, rfl⟩ := hy_ch4
        have hy3 : x ++ [j] ∈ (stage3 B (ρ m).val (α m)).nodes :=
          ((stage4_mem_iff B (ρ m).val (α m) _).mp hy4).1
        rw [hsucc_eq, compressed_label_of_mem hpref4 hy4, stage4_label_of_mem B _ _ hy4] at hq
        have hq1 : q ∈ (expand B (ρ m).val (α m)).label (x ++ [j]) := hsub31 _ hy3 hq
        have hy1 : x ++ [j] ∈ (expand B (ρ m).val (α m)).nodes :=
          ((stage3_mem_iff B (ρ m).val (α m) _).mp hy3).1
        rcases (expand_mem_iff B (ρ m).val (α m) (x ++ [j])).mp hy1 with hy_old | ⟨z, hz_old, heq⟩
        · rw [expand_label_old B (ρ m).val (α m) hy_old] at hq1
          obtain ⟨q', hq'y, hd⟩ := Finset.mem_biUnion.mp hq1
          have hy_ch_m : x ++ [j] ∈ children (ρ m).val.nodes x := by
            simp [children, hy_old]
          obtain ⟨qa, hqa, har⟩ := ih.2 (x ++ [j]) hy_ch_m q' hq'y
          exact ⟨qa, hqa, accReachOn_step B α (Nat.le_add_right a d) har hd⟩
        · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
          rw [expand_label_new B (ρ m).val (α m) hz_old] at hq1
          obtain ⟨hq_bi, hq_acc⟩ := Finset.mem_inter.mp hq1
          obtain ⟨q', hq'x, hd⟩ := Finset.mem_biUnion.mp hq_bi
          obtain ⟨qa, hqa, hr⟩ := ih.1 q' hq'x
          exact ⟨qa, hqa, accReachOn_of_reachOn_acc B α (Nat.le_add_right a d) hr hd hq_acc⟩
  -- Deduce accepting reachability from L k to L (k + 1)
  let L : ℕ → Finset Q := fun k => (ρ (sSeq k)).val.label x
  have hL_ne : ∀ k, (L k).Nonempty := by
    intro k
    have hs_ge : tSeq 0 ≤ sSeq k := by
      have := ht0_le_tk k; simp [sSeq]; omega
    exact (ρ (sSeq k)).property.2.2.2.1 x (hx_at (sSeq k) hs_ge).1
  have hL_pred : ∀ k, ∀ q'' ∈ L (k + 1), ∃ q' ∈ L k, AccReachOn B α (sSeq k) (sSeq (k + 1)) q' q'' := by
    intro k q'' hq''
    let m := tSeq (k + 1)
    have ha_le_m : sSeq k ≤ m := by
      have := ht_lt k; simp [sSeq, m]; omega
    let d := m - sSeq k
    have hm_eq : sSeq k + d = m := by omega
    obtain ⟨ih1, ih2⟩ := hseg_inv k d
    rw [hm_eq] at ih1 ih2
    have hm_ge_t0 : tSeq 0 ≤ m := ht0_le_tk (k + 1)
    obtain ⟨_, _, _, hlbl_next⟩ := hx_at m hm_ge_t0
    have hacc_m := ht_acc (k + 1)
    simp only [acceptingNodes, Finset.mem_filter] at hacc_m
    have hres_m : x ∈ resetNodes (stage3 B (ρ m).val (α m)) := hacc_m.2.1
    have hres_eq : (stage3 B (ρ m).val (α m)).label x = childLabels (stage3 B (ρ m).val (α m)) x :=
      (Finset.mem_filter.mp hres_m).2
    have hq''_3 : q'' ∈ childLabels (stage3 B (ρ m).val (α m)) x := by
      change q'' ∈ (ρ (m + 1)).val.label x at hq''
      rwa [hlbl_next, hres_eq] at hq''
    obtain ⟨y, hy_ch3, hq''y3⟩ := Finset.mem_biUnion.mp hq''_3
    simp only [children, Finset.mem_filter] at hy_ch3
    obtain ⟨hy3, j, rfl⟩ := hy_ch3
    have hq''y1 : q'' ∈ (expand B (ρ m).val (α m)).label (x ++ [j]) := by
      rw [stage3_label_of_mem B _ _ hy3] at hq''y3
      exact (Finset.mem_filter.mp hq''y3).1
    have hy1 : x ++ [j] ∈ (expand B (ρ m).val (α m)).nodes :=
      ((stage3_mem_iff B (ρ m).val (α m) _).mp hy3).1
    have hs_next : sSeq (k + 1) = m + 1 := rfl
    rw [hs_next]
    rcases (expand_mem_iff B (ρ m).val (α m) (x ++ [j])).mp hy1 with hy_old | ⟨z, hz_old, heq⟩
    · rw [expand_label_old B (ρ m).val (α m) hy_old] at hq''y1
      obtain ⟨q_mid, hq_mid, hd⟩ := Finset.mem_biUnion.mp hq''y1
      have hy_ch_m : x ++ [j] ∈ children (ρ m).val.nodes x := by simp [children, hy_old]
      obtain ⟨qa, hqa, har⟩ := ih2 (x ++ [j]) hy_ch_m q_mid hq_mid
      exact ⟨qa, hqa, accReachOn_step B α ha_le_m har hd⟩
    · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      rw [expand_label_new B (ρ m).val (α m) hz_old] at hq''y1
      obtain ⟨hq_bi, hq_acc⟩ := Finset.mem_inter.mp hq''y1
      obtain ⟨q_mid, hq_mid, hd⟩ := Finset.mem_biUnion.mp hq_bi
      obtain ⟨qa, hqa, hr⟩ := ih1 q_mid hq_mid
      exact ⟨qa, hqa, accReachOn_of_reachOn_acc B α ha_le_m hr hd hq_acc⟩
  -- Apply König's lemma
  obtain ⟨qSeq, hqSeq_mem, hqSeq_step⟩ :=
    konig_layers L (fun k q1 q2 => AccReachOn B α (sSeq k) (sSeq (k + 1)) q1 q2) hL_ne hL_pred
  -- Initial segment 0 .. sSeq 0
  have hq0_root : qSeq 0 ∈ (ρ (sSeq 0)).val.label [] := by
    have hx_s0 : x ∈ (ρ (sSeq 0)).val.nodes := (hx_at (sSeq 0) (by simp [sSeq])).1
    have hsub := label_sub_of_prefix (ρ (sSeq 0)).property [] x (by simpa using hx_s0)
    exact hsub (by simpa using hqSeq_mem 0)
  obtain ⟨qInit, hqInit, fInit, hfInit0, hfInits0, hfInit_step⟩ :=
    root_reach_of_trace htr (sSeq 0) (qSeq 0) hq0_root
  have hfSeg_ex : ∀ k, ∃ f : ℕ → Q,
      f (sSeq k) = qSeq k ∧
      f (sSeq (k + 1)) = qSeq (k + 1) ∧
      (∀ i, sSeq k ≤ i → i < sSeq (k + 1) → f (i + 1) ∈ B.delta (f i) (α i)) ∧
      ∃ j, sSeq k < j ∧ j ≤ sSeq (k + 1) ∧ f j ∈ B.accepting := hqSeq_step
  let fSeg : ℕ → ℕ → Q := fun k => Classical.choose (hfSeg_ex k)
  have hfSeg_spec : ∀ k,
      fSeg k (sSeq k) = qSeq k ∧
      fSeg k (sSeq (k + 1)) = qSeq (k + 1) ∧
      (∀ i, sSeq k ≤ i → i < sSeq (k + 1) → fSeg k (i + 1) ∈ B.delta (fSeg k i) (α i)) ∧
      ∃ j, sSeq k < j ∧ j ≤ sSeq (k + 1) ∧ fSeg k j ∈ B.accepting :=
    fun k => Classical.choose_spec (hfSeg_ex k)
  -- Strictly monotone properties of sSeq
  have hs_mono : StrictMono sSeq := strictMono_nat_of_lt_succ hs_lt
  have hs_ge_id : ∀ k, k ≤ sSeq k := by
    intro k
    induction k with
    | zero => omega
    | succ k ih => have := hs_lt k; omega
  let segSet : ℕ → Finset ℕ := fun i => (Finset.range (i + 1)).filter (fun k => sSeq k ≤ i)
  have hsegSet_ne : ∀ {i : ℕ}, sSeq 0 ≤ i → (segSet i).Nonempty := fun {i} hi =>
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi⟩⟩
  let idxOf : ∀ (i : ℕ), sSeq 0 ≤ i → ℕ := fun i hi => (segSet i).max' (hsegSet_ne hi)
  have hidx_bounds : ∀ {i : ℕ} (hi : sSeq 0 ≤ i),
      sSeq (idxOf i hi) ≤ i ∧ i < sSeq (idxOf i hi + 1) := by
    intro i hi
    have hmem := Finset.max'_mem (segSet i) (hsegSet_ne hi)
    have hle : sSeq (idxOf i hi) ≤ i := (Finset.mem_filter.mp hmem).2
    refine ⟨hle, ?_⟩
    by_contra hnot_lt
    have hge : sSeq (idxOf i hi + 1) ≤ i := Nat.le_of_not_lt hnot_lt
    have hk1_le_i : idxOf i hi + 1 ≤ i := le_trans (hs_ge_id _) hge
    have hk1_mem : idxOf i hi + 1 ∈ segSet i :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hge⟩
    have hmax := Finset.le_max' (segSet i) (idxOf i hi + 1) hk1_mem
    change idxOf i hi + 1 ≤ idxOf i hi at hmax
    omega
  have hidx_eq : ∀ {i k : ℕ} (hi : sSeq 0 ≤ i),
      sSeq k ≤ i → i < sSeq (k + 1) → idxOf i hi = k := by
    intro i k hi h1 h2
    obtain ⟨b1, b2⟩ := hidx_bounds hi
    rcases lt_trichotomy (idxOf i hi) k with hlt | heq | hgt
    · have : sSeq (idxOf i hi + 1) ≤ sSeq k :=
        hs_mono.monotone (show idxOf i hi + 1 ≤ k by omega)
      omega
    · exact heq
    · have : sSeq (k + 1) ≤ sSeq (idxOf i hi) :=
        hs_mono.monotone (show k + 1 ≤ idxOf i hi by omega)
      omega
  let run : ℕ → Q := fun i =>
    if hi : sSeq 0 ≤ i then fSeg (idxOf i hi) i else fInit i
  have hrun_at_s : ∀ k, run (sSeq k) = qSeq k := by
    intro k
    have hi : sSeq 0 ≤ sSeq k := hs_mono.monotone (Nat.zero_le k)
    simp only [run, dif_pos hi]
    rw [hidx_eq hi le_rfl (hs_lt k)]
    exact (hfSeg_spec k).1
  have hrun_in_seg : ∀ k i, sSeq k ≤ i → i < sSeq (k + 1) → run i = fSeg k i := by
    intro k i h1 h2
    have hi : sSeq 0 ≤ i := le_trans (hs_mono.monotone (Nat.zero_le k)) h1
    simp only [run, dif_pos hi, hidx_eq hi h1 h2]
  have hisRun : IsRun B α run := by
    refine ⟨?_, ?_⟩
    · have hs0_pos : 0 < sSeq 0 := by simp [sSeq]
      simp only [run, dif_neg (show ¬ sSeq 0 ≤ 0 by omega)]
      rw [hfInit0]
      exact hqInit
    · intro i
      by_cases hi : sSeq 0 ≤ i
      · obtain ⟨hk1, hk2⟩ := hidx_bounds hi
        rw [hrun_in_seg (idxOf i hi) i hk1 hk2]
        by_cases hi1 : i + 1 < sSeq (idxOf i hi + 1)
        · rw [hrun_in_seg (idxOf i hi) (i + 1) (Nat.le_trans hk1 (Nat.le_succ i)) hi1]
          exact (hfSeg_spec (idxOf i hi)).2.2.1 i hk1 hk2
        · have heq : i + 1 = sSeq (idxOf i hi + 1) := by omega
          rw [heq, hrun_at_s (idxOf i hi + 1), ← (hfSeg_spec (idxOf i hi)).2.1, ← heq]
          exact (hfSeg_spec (idxOf i hi)).2.2.1 i hk1 hk2
      · have hilt : i < sSeq 0 := Nat.lt_of_not_le hi
        simp only [run, dif_neg hi]
        by_cases hi1 : i + 1 < sSeq 0
        · have hnot1 : ¬ sSeq 0 ≤ i + 1 := by omega
          rw [dif_neg hnot1]
          exact hfInit_step i (Nat.zero_le i) hilt
        · have heq : i + 1 = sSeq 0 := by omega
          have hrun_s0 := hrun_at_s 0
          simp only [run] at hrun_s0
          rw [heq, hrun_s0, ← hfInits0, ← heq]
          exact hfInit_step i (Nat.zero_le i) hilt
  -- Infinitely many accepting visits
  have hwit_ex : ∀ k, ∃ j, sSeq k < j ∧ j ≤ sSeq (k + 1) ∧ run j ∈ B.accepting := by
    intro k
    obtain ⟨j, hj1, hj2, hjacc⟩ := (hfSeg_spec k).2.2.2
    refine ⟨j, hj1, hj2, ?_⟩
    by_cases hjlt : j < sSeq (k + 1)
    · rw [hrun_in_seg k j (Nat.le_of_lt hj1) hjlt]
      exact hjacc
    · have hjeq : j = sSeq (k + 1) := by omega
      rw [hjeq, hrun_at_s (k + 1), ← (hfSeg_spec k).2.1, ← hjeq]
      exact hjacc
  let witIdx : ℕ → ℕ := fun k => Classical.choose (hwit_ex k)
  have hwit_spec : ∀ k,
      sSeq k < witIdx k ∧ witIdx k ≤ sSeq (k + 1) ∧ run (witIdx k) ∈ B.accepting :=
    fun k => Classical.choose_spec (hwit_ex k)
  have : Nonempty Q := ⟨run 0⟩
  obtain ⟨qf, hqf_inf⟩ := Finite.exists_infinite_fiber (fun k => run (witIdx k))
  have hqf_set : ((fun k => run (witIdx k)) ⁻¹' {qf}).Infinite := Set.infinite_coe_iff.mp hqf_inf
  obtain ⟨k0, hk0⟩ := hqf_set.nonempty
  have hqf_acc : qf ∈ B.accepting := by
    have heq : run (witIdx k0) = qf := hk0
    exact heq ▸ (hwit_spec k0).2.2
  refine ⟨run, hisRun, qf, hqf_acc, fun N => ?_⟩
  obtain ⟨k, hk_mem, hk_not_lt⟩ := (hqf_set.sdiff (Set.finite_lt_nat N)).nonempty
  have hk_ge : N ≤ k := Nat.le_of_not_lt hk_not_lt
  have hk_eq : run (witIdx k) = qf := hk_mem
  have hwit_ge : N ≤ witIdx k := by
    have := hs_ge_id k
    have := (hwit_spec k).1
    omega
  exact ⟨witIdx k, hwit_ge, hk_eq⟩

end
end BuchiRabinIndex.LowerBound.Lemma9Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma9Aux in
theorem solution {Q Sigma : Type} [Fintype Q] [Nonempty Q] [Fintype Sigma]
    (B : NBW Q Sigma) (α : ℕ → Sigma) :
    α ∈ language B ↔ ∃ (ρ : ℕ → History Q) (x : Node),
      Positive x ∧ IsTrace B α ρ ∧
      (∃ N, ∀ i ≥ N, x ∉ unstable B (ρ i) (α i)) ∧
      (∀ N, ∃ i ≥ N, x ∈ acceptingNodes B (ρ i) (α i)) := by
  constructor
  · exact lemma_9_mp B α
  · rintro ⟨ρ, x, _, htr, hstab, hacc⟩
    exact lemma_9_mpr B α htr hstab hacc

