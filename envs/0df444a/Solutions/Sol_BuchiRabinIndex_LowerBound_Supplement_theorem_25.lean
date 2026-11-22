-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.Supplement.theorem_25
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:33:15.048125+00:00
-- url     : https://prove2.me/submissions/b7f2e285-7b39-41f1-9e88-2a2ecc9a79fd

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging
import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Counting
import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_15
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_19
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_24

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace BuchiRabinIndex.LowerBound.Supplement.Thm25Aux
open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
open scoped Classical

noncomputable def colourImage {I : Type} {n : ℕ} (Id : Vertex n → I) : Finset I :=
  (Finset.univ : Finset (Vertex n)).image Id

/-! ### Part 1: Basic History-Tree Properties and Equinumerosity -/

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

lemma own_nonempty {Q : Type} (H : History Q) {x : Node} (hx : x ∈ H.val.nodes) :
    (own H.val x).Nonempty := by
  have hss := H.property.2.2.2.2.2 x hx
  rw [own, Finset.sdiff_nonempty]
  exact fun h => hss.not_subset h

lemma nodes_card_le {Q : Type} [Fintype Q] (H : History Q) :
    H.val.nodes.card ≤ Fintype.card Q := by
  have hv := H.property
  have hdisj : (H.val.nodes : Set Node).PairwiseDisjoint (own H.val) :=
    fun x hx y hy hne => own_disjoint hv hx hy hne
  have hpos : ∀ x ∈ H.val.nodes, 1 ≤ (own H.val x).card :=
    fun x hx => Finset.one_le_card.mpr (own_nonempty H hx)
  calc H.val.nodes.card
      = ∑ _x ∈ H.val.nodes, 1 := by simp
    _ ≤ ∑ x ∈ H.val.nodes, (own H.val x).card := Finset.sum_le_sum hpos
    _ = (H.val.nodes.biUnion (own H.val)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card Q := Finset.card_univ

lemma card_chain_eq : ∀ x : Node, Positive x → (chain x).card = weight x + 1
  | [], _ => by simp [chain, weight]
  | i :: v, hx => by
    have hi : 0 < i := hx i (by simp)
    have hv : Positive v := fun k hk => hx k (by simp [hk])
    have ih := card_chain_eq v hv
    have hdisj : Disjoint ((Finset.Icc 1 (i - 1)).image fun j => [j])
        ((chain v).image (i :: ·)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
      simp at hy hj; omega
    have hnil : [] ∉ ((Finset.Icc 1 (i - 1)).image fun j => [j]) ∪ ((chain v).image (i :: ·)) := by
      simp
    simp only [chain]
    rw [Finset.card_insert_of_notMem hnil, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_image_of_injective _ (fun a b h => by simpa using h), ih]
    simp [weight]; omega

lemma pos_bw (b : ℕ) : ∀ (d : ℕ) (x : Node), x ∈ boundedWords b d → Positive x
  | 0, x, hx => by
    simp [boundedWords] at hx
    subst hx
    intro i hi; simp at hi
  | d + 1, x, hx => by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · intro i hi; simp at hi
    · obtain ⟨a, ha, hx'⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx'
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpt := pos_bw b d t ht
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · exact hpt i hi

lemma pos_and_weight_of_mem_fullTree {n : ℕ} {x : Node} (hx : x ∈ fullTree n) :
    Positive x ∧ weight x ≤ n - 1 := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · obtain ⟨hb, hw⟩ := Finset.mem_filter.mp hx
    exact ⟨pos_bw _ _ x hb, hw⟩

lemma length_le_sum : ∀ l : List ℕ, Positive l → l.length ≤ l.sum
  | [], _ => by simp
  | a :: t, hp => by
    have ht := length_le_sum t (fun k hk => hp k (by simp [hk]))
    have ha := hp a (by simp)
    simp; omega

lemma mem_boundedWords (b : ℕ) : ∀ (d : ℕ) (x : Node),
    (∀ i ∈ x, 1 ≤ i ∧ i ≤ b) → x.length ≤ d → x ∈ boundedWords b d
  | 0, x, _, hl => by simp at hl; subst hl; simp [boundedWords]
  | d + 1, [], _, _ => by simp [boundedWords]
  | d + 1, a :: t, hb, hl => by
    simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    right
    exact ⟨a, hb a (by simp), t,
      mem_boundedWords b d t (fun i hi => hb i (by simp [hi])) (by simp at hl; omega), rfl⟩

lemma mem_fullTree_of_pos_weight {n : ℕ} (hn : 1 ≤ n) {x : Node}
    (hx : Positive x) (hw : weight x ≤ n - 1) : x ∈ fullTree n := by
  have hn0 : n ≠ 0 := by omega
  unfold fullTree
  rw [if_neg hn0, Finset.mem_filter]
  refine ⟨?_, hw⟩
  have hsum : ∀ (l : List ℕ) (i : ℕ), i ∈ l → i ≤ l.sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      intro i hi; rcases List.mem_cons.1 hi with rfl | hi
      · simp
      · have := ih i hi; simp; omega
  exact mem_boundedWords (n - 1) (n - 1) x
    (fun i hi => ⟨hx i hi, (hsum x i hi).trans hw⟩) ((length_le_sum x hx).trans hw)

lemma nodes_sub_fullTree {Q : Type} [Fintype Q] [Nonempty Q] (H : History Q) :
    H.val.nodes ⊆ fullTree (Fintype.card Q) := by
  have hk : 1 ≤ Fintype.card Q := Fintype.card_pos
  intro x hx
  have hpx : Positive x := H.property.1.1 x hx
  have hch_sub : chain x ⊆ H.val.nodes :=
    (fact_30 x x hpx hpx).2.2.2.2.2.1 H.val.nodes H.property.1 hx
  have hcard : (chain x).card ≤ Fintype.card Q :=
    (Finset.card_le_card hch_sub).trans (nodes_card_le H)
  rw [card_chain_eq x hpx] at hcard
  exact mem_fullTree_of_pos_weight hk hpx (by omega)

lemma history_finite {Q : Type} [Fintype Q] [Nonempty Q] : Finite (History Q) := by
  let k := Fintype.card Q
  have hsub : ∀ H : History Q, H.val.nodes ∈ (fullTree k).powerset :=
    fun H => Finset.mem_powerset.mpr (nodes_sub_fullTree H)
  let enc : History Q → ↥((fullTree k).powerset) × (Vertex k → Finset Q) :=
    fun H => (⟨H.val.nodes, hsub H⟩, fun v => H.val.label v.val)
  refine Finite.of_injective enc ?_
  intro H1 H2 heq
  have hnodes : H1.val.nodes = H2.val.nodes := congrArg (Subtype.val ∘ Prod.fst) heq
  have hlbl_on : ∀ v : Vertex k, H1.val.label v.val = H2.val.label v.val :=
    fun v => congrFun (congrArg Prod.snd heq) v
  have hlbl : H1.val.label = H2.val.label := by
    funext x
    by_cases hx : x ∈ H1.val.nodes
    · exact hlbl_on ⟨x, nodes_sub_fullTree H1 hx⟩
    · have hx2 : x ∉ H2.val.nodes := hnodes ▸ hx
      rw [H1.property.2.2.1 x hx, H2.property.2.2.1 x hx2]
  apply Subtype.ext
  rcases H1 with ⟨⟨n1, l1⟩, _⟩
  rcases H2 with ⟨⟨n2, l2⟩, _⟩
  simp only at hnodes hlbl
  subst hnodes hlbl
  rfl

lemma valid_mapData {Q R : Type} (e : Q ≃ R) {H : TreeData Q} (hv : Valid H) :
    Valid (mapData H e) := by
  refine ⟨hv.1, hv.2.1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mapData, hv.2.2.1 x hx, Finset.image_empty]
  · intro x hx
    exact (hv.2.2.2.1 x hx).image e
  · intro p i j hpi hpj hij
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.mp hr1
    obtain ⟨q2, hq2, heq⟩ := Finset.mem_image.mp hr2
    cases e.injective heq
    exact Finset.disjoint_left.mp (hv.2.2.2.2.1 p i j hpi hpj hij) hq1 hq2
  · intro x hx
    have hch_eq : childLabels (mapData H e) x = (childLabels H x).image e := by
      ext r
      simp only [childLabels, mapData, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨fun ⟨c, hc, q, hq, hqe⟩ => ⟨q, ⟨c, hc, hq⟩, hqe⟩,
             fun ⟨q, ⟨c, hc, hq⟩, hqe⟩ => ⟨c, hc, q, hq, hqe⟩⟩
    rw [hch_eq]
    have hss := hv.2.2.2.2.2 x hx
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.image_subset_image hss.subset, ?_⟩
    intro heq_img
    obtain ⟨q, hq_lbl, hq_not_ch⟩ := Finset.exists_of_ssubset hss
    have heq_mem : e q ∈ (childLabels H x).image e := by
      rw [heq_img]; exact Finset.mem_image_of_mem e hq_lbl
    obtain ⟨q', hq'_ch, hqq'⟩ := Finset.mem_image.mp heq_mem
    cases e.injective hqq'
    exact hq_not_ch hq'_ch

lemma mapData_comp_symm {Q R : Type} (e : Q ≃ R) (H : TreeData Q) :
    mapData (mapData H e) e.symm = H := by
  rcases H with ⟨ns, lbl⟩
  simp only [mapData, TreeData.mk.injEq, true_and]
  funext x
  ext q
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨r, ⟨q', hq', rfl⟩, hrq⟩
    have hqq : q' = q := by simpa using hrq
    rwa [← hqq]
  · intro hq
    exact ⟨e q, ⟨q, hq, rfl⟩, e.symm_apply_apply q⟩

lemma historyCount_eq_hist {Q : Type} [Fintype Q] :
    historyCount Q = hist (Fintype.card Q) := by
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let equivH : History Q ≃ History (Fin (Fintype.card Q)) :=
    { toFun := fun H => ⟨mapData H.val e, valid_mapData e H.property⟩
      invFun := fun H => ⟨mapData H.val e.symm, valid_mapData e.symm H.property⟩
      left_inv := fun H => Subtype.ext (mapData_comp_symm e H.val)
      right_inv := fun H => Subtype.ext (mapData_comp_symm e.symm H.val) }
  exact Nat.card_congr equivH

/-! ### Part 2: Index Bound for Arbitrary NBWs -/

lemma card_canonicalColour_image (n : ℕ) (hn : 1 ≤ n) :
    (colourImage (canonicalColour n)).card = ∑ w ∈ Finset.range n, sf n w := by
  have himg_univ : colourImage (canonicalColour n) = Finset.univ := by
    ext u
    simp only [colourImage, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp u.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
  rw [himg_univ, Finset.card_univ, Fintype.card_coe]
  let block : ℕ → Finset (ℕ × ℕ) := fun w => (Finset.Icc 1 (sf n w)).image (fun f => (w, f))
  have hid_eq : identifiers n = (Finset.range n).biUnion block := by
    ext wf
    rcases wf with ⟨w, f⟩
    simp only [identifiers, block, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, hcid⟩
      have hw_eq : weight x = w := congrArg Prod.fst hcid
      have hcf_eq : cf n x = f := congrArg Prod.snd hcid
      have hw_le : weight x ≤ n - 1 := (pos_and_weight_of_mem_fullTree hx).2
      refine ⟨w, by omega, f, ?_, rfl⟩
      rw [← (theorem_19 n hn).2 w]
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hw_eq⟩, hcf_eq⟩
    · rintro ⟨w', hw', f', hf', heq⟩
      have hww : w' = w := congrArg Prod.fst heq
      have hff : f' = f := congrArg Prod.snd heq
      subst hww hff
      rw [← (theorem_19 n hn).2 w'] at hf'
      obtain ⟨x, hx_filt, hcf_eq⟩ := Finset.mem_image.mp hf'
      obtain ⟨hx, hw_eq⟩ := Finset.mem_filter.mp hx_filt
      exact ⟨x, hx, Prod.ext hw_eq hcf_eq⟩
  have hdisj : ((Finset.range n : Finset ℕ) : Set ℕ).PairwiseDisjoint block := by
    intro w1 _ w2 _ hne
    change Disjoint (block w1) (block w2)
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    obtain ⟨f1, -, rfl⟩ := Finset.mem_image.mp hp1
    obtain ⟨f2, -, hp2'⟩ := Finset.mem_image.mp hp2
    exact hne (congrArg Prod.fst hp2').symm
  have hblock_card : ∀ w ∈ Finset.range n, (block w).card = sf n w := by
    intro w _
    simp only [block]
    rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h), Nat.card_Icc]
    omega
  rw [hid_eq, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl hblock_card

lemma geom_sum_two (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

lemma sum_sf_closed (n : ℕ) (hn : 1 ≤ n) :
    (Even n → ∑ w ∈ Finset.range n, sf n w = 3 * 2 ^ (n / 2 - 1) - 1) ∧
    (Odd n → ∑ w ∈ Finset.range n, sf n w = 2 ^ ((n + 1) / 2) - 1) := by
  obtain ⟨hsf0, hsf_lo, hsf_hi⟩ := lemma_15 n hn
  refine ⟨?_, ?_⟩
  · intro hev
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := even_iff_exists_two_mul.mp hev
    have hm1 : 1 ≤ m := by omega
    have hdiv : n / 2 = m := by omega
    have hrng : Finset.range n = Finset.range ((1 + m) + (m - 1)) :=
      congrArg Finset.range (by omega)
    have h1 : ∑ w ∈ Finset.range (1 + m), sf n w = 2 ^ m := by
      rw [Finset.sum_range_add, Finset.sum_range_one, hsf0]
      have hlo : ∑ i ∈ Finset.range m, sf n (1 + i) = ∑ i ∈ Finset.range m, 2 ^ i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt : i < m := Finset.mem_range.mp hi
        rw [hsf_lo (1 + i) (by omega) (by omega)]
        congr 1; omega
      rw [hlo, geom_sum_two]
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    have h2 : ∑ j ∈ Finset.range (m - 1), sf n ((1 + m) + j) = 2 ^ (m - 1) - 1 := by
      have hhi : ∑ j ∈ Finset.range (m - 1), sf n ((1 + m) + j) =
          ∑ j ∈ Finset.range (m - 1), 2 ^ (m - 1 - 1 - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj_lt : j < m - 1 := Finset.mem_range.mp hj
        rw [hsf_hi ((1 + m) + j) (by omega) (by omega)]
        congr 1; omega
      rw [hhi, Finset.sum_range_reflect (fun k => 2 ^ k) (m - 1), geom_sum_two]
    rw [hrng, Finset.sum_range_add, h1, h2, hdiv]
    have hm_pow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]; ring
    have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    omega
  · intro hodd
    rcases hodd with ⟨m, hm⟩
    have hdiv : n / 2 = m := by omega
    have hdiv2 : (n + 1) / 2 = m + 1 := by omega
    have hrng : Finset.range n = Finset.range ((1 + m) + m) :=
      congrArg Finset.range (by omega)
    have h1 : ∑ w ∈ Finset.range (1 + m), sf n w = 2 ^ m := by
      rw [Finset.sum_range_add, Finset.sum_range_one, hsf0]
      have hlo : ∑ i ∈ Finset.range m, sf n (1 + i) = ∑ i ∈ Finset.range m, 2 ^ i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt : i < m := Finset.mem_range.mp hi
        rw [hsf_lo (1 + i) (by omega) (by omega)]
        congr 1; omega
      rw [hlo, geom_sum_two]
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    have h2 : ∑ j ∈ Finset.range m, sf n ((1 + m) + j) = 2 ^ m - 1 := by
      have hhi : ∑ j ∈ Finset.range m, sf n ((1 + m) + j) =
          ∑ j ∈ Finset.range m, 2 ^ (m - 1 - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj_lt : j < m := Finset.mem_range.mp hj
        rw [hsf_hi ((1 + m) + j) (by omega) (by omega)]
        congr 1; omega
      rw [hhi, Finset.sum_range_reflect (fun k => 2 ^ k) m, geom_sum_two]
    rw [hrng, Finset.sum_range_add, h1, h2, hdiv2, pow_succ]
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

lemma reducedCondition_card_le_sum_sf {Q Sigma : Type} [Fintype Q] [Nonempty Q]
    (B : NBW Q Sigma) :
    (reducedCondition B).card ≤ ∑ w ∈ Finset.range (Fintype.card Q), sf (Fintype.card Q) w := by
  let n := Fintype.card Q
  have hn : 1 ≤ n := Fintype.card_pos
  have hact_le : (activeColours B (canonicalColour n)).card ≤ (colourImage (canonicalColour n)).card := by
    unfold activeColours colourImage
    exact Finset.card_filter_le _ _
  calc (reducedCondition B).card
      ≤ (activeColours B (canonicalColour n)).card := Finset.card_image_le
    _ ≤ (colourImage (canonicalColour n)).card := hact_le
    _ = ∑ w ∈ Finset.range n, sf n w := card_canonicalColour_image n hn

/-! ### Part 3: First-Child / Next-Sibling Binary Encoding of Ordered Trees (`≤ 4^k`) -/

def fcns : Node → List Bool
  | [] => []
  | i :: v => (true :: List.replicate (i - 1) false) ++ fcns v

def unfcnsGo : ℕ → List Bool → Node
  | acc, [] => [acc + 1]
  | acc, false :: bs => unfcnsGo (acc + 1) bs
  | acc, true :: bs => (acc + 1) :: unfcnsGo 0 bs

def unfcns : List Bool → Node
  | [] => []
  | false :: _ => []
  | true :: bs => unfcnsGo 0 bs

lemma unfcnsGo_rep : ∀ (v : Node), Positive v → ∀ (m acc : ℕ),
    unfcnsGo acc (List.replicate m false ++ fcns v) = (acc + m + 1) :: v
  | [], _, m, acc => by
    induction m generalizing acc with
    | zero => simp [fcns, unfcnsGo]
    | succ m ih =>
      simp only [List.replicate_succ, List.cons_append, unfcnsGo]
      rw [ih (acc + 1)]
      congr 1; omega
  | i :: w, hv, m, acc => by
    have hi : 0 < i := hv i (by simp)
    have hw : Positive w := fun a ha => hv a (by simp [ha])
    induction m generalizing acc with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, fcns, List.cons_append, unfcnsGo]
      rw [unfcnsGo_rep w hw (i - 1) 0]
      simp only [Nat.zero_add, Nat.add_zero]
      rw [Nat.sub_add_cancel hi]
    | succ m ih =>
      simp only [List.replicate_succ, List.cons_append, unfcnsGo]
      rw [ih (acc + 1)]
      congr 1; omega

lemma unfcns_fcns {x : Node} (hx : Positive x) : unfcns (fcns x) = x := by
  cases x with
  | nil => rfl
  | cons i v =>
    have hi : 0 < i := hx i (by simp)
    have hv : Positive v := fun a ha => hx a (by simp [ha])
    simp only [fcns, List.cons_append, unfcns]
    rw [unfcnsGo_rep v hv (i - 1) 0]
    congr 1; omega

lemma fcns_append : ∀ (a c : Node), fcns (a ++ c) = fcns a ++ fcns c
  | [], c => by simp [fcns]
  | i :: a, c => by simp [fcns, fcns_append a c, List.append_assoc]

def BinTree (B : Finset (List Bool)) : Prop :=
  [] ∈ B ∧ ∀ u b, u ++ [b] ∈ B → u ∈ B

lemma binTree_prefix {B : Finset (List Bool)} (hB : BinTree B) :
    ∀ (u r : List Bool), u ++ r ∈ B → u ∈ B := by
  intro u r
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r b ih =>
    intro hmem
    rw [← List.append_assoc] at hmem
    exact ih (hB.2 (u ++ r) b hmem)

lemma binTree_of_ordered {T : Finset Node} (hord : Ordered T) (hnil : [] ∈ T) :
    BinTree (T.image fcns) := by
  refine ⟨Finset.mem_image.mpr ⟨[], hnil, rfl⟩, ?_⟩
  intro u b hmem
  obtain ⟨x, hxT, hfx⟩ := Finset.mem_image.mp hmem
  have hpx : Positive x := hord.1 x hxT
  rcases List.eq_nil_or_concat x with rfl | ⟨p, i, rfl⟩
  · simp [fcns] at hfx
  · rw [List.concat_eq_append] at hxT hpx hfx
    have hi : 0 < i := hpx i (by simp)
    rw [fcns_append] at hfx
    by_cases hi1 : i = 1
    · subst hi1
      simp only [fcns, Nat.sub_self, List.replicate_zero, List.append_nil] at hfx
      have hu : fcns p = u := List.append_inj_left' hfx (by simp)
      have hpT : p ∈ T := hord.2.1 (p ++ [1]) hxT p ⟨[1], rfl⟩
      exact Finset.mem_image.mpr ⟨p, hpT, hu⟩
    · have hi2 : 2 ≤ i := by omega
      have hrep : (true :: List.replicate (i - 1) false) =
          (true :: List.replicate (i - 2) false) ++ [false] := by
        have hsub : i - 1 = (i - 2) + 1 := by omega
        rw [hsub, List.replicate_succ']
        simp
      simp only [fcns, List.append_nil] at hfx
      rw [hrep, ← List.append_assoc] at hfx
      have hu : fcns p ++ (true :: List.replicate (i - 2) false) = u :=
        List.append_inj_left' hfx (by simp)
      have hfc_prev : fcns (p ++ [i - 1]) = u := by
        have hsub2 : i - 1 - 1 = i - 2 := by omega
        rw [fcns_append]
        simpa [fcns, hsub2] using hu
      have hprevT : p ++ [i - 1] ∈ T := hord.2.2 p i hxT (i - 1) (by omega) (by omega)
      exact Finset.mem_image.mpr ⟨p ++ [i - 1], hprevT, hfc_prev⟩

def subBin (B : Finset (List Bool)) (w : List Bool) : Finset (List Bool) :=
  B.filter (w.IsPrefix ·)

lemma subBin_eq_empty_of_notMem {B : Finset (List Bool)} (hB : BinTree B)
    {w : List Bool} (hw : w ∉ B) : subBin B w = ∅ := by
  ext y
  simp only [subBin, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro hyB hpref
  obtain ⟨r, rfl⟩ := hpref
  exact hw (binTree_prefix hB w r hyB)

lemma subBin_split {B : Finset (List Bool)} {w : List Bool} (hw : w ∈ B) :
    subBin B w = insert w (subBin B (w ++ [false]) ∪ subBin B (w ++ [true])) ∧
      (subBin B w).card =
        1 + (subBin B (w ++ [false])).card + (subBin B (w ++ [true])).card := by
  have hsplit : subBin B w = insert w (subBin B (w ++ [false]) ∪ subBin B (w ++ [true])) := by
    ext y
    simp only [subBin, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨hyB, r, rfl⟩
      cases r with
      | nil => left; simp
      | cons b rest =>
        cases b
        · right; left; exact ⟨hyB, rest, by simp⟩
        · right; right; exact ⟨hyB, rest, by simp⟩
    · rintro (hyw | ⟨hyB, r, rfl⟩ | ⟨hyB, r, rfl⟩)
      · subst hyw; exact ⟨hw, List.prefix_refl _⟩
      · exact ⟨hyB, false :: r, by simp⟩
      · exact ⟨hyB, true :: r, by simp⟩
  have hwnot : w ∉ subBin B (w ++ [false]) ∪ subBin B (w ++ [true]) := by
    simp only [subBin, Finset.mem_union, Finset.mem_filter, not_or, not_and]
    refine ⟨fun _ ⟨r, hr⟩ => ?_, fun _ ⟨r, hr⟩ => ?_⟩
    · have hl := congrArg List.length hr; simp at hl
    · have hl := congrArg List.length hr; simp at hl
  have hdisj : Disjoint (subBin B (w ++ [false])) (subBin B (w ++ [true])) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨_, r1, rfl⟩ := Finset.mem_filter.mp hy1
    obtain ⟨_, r2, heq⟩ := Finset.mem_filter.mp hy2
    simp only [List.append_assoc, List.singleton_append] at heq
    have hcons := List.append_cancel_left heq
    simp at hcons
  refine ⟨hsplit, ?_⟩
  rw [hsplit, Finset.card_insert_of_notMem hwnot, Finset.card_union_of_disjoint hdisj]
  omega

def encBin : ℕ → Finset (List Bool) → List Bool → List Bool
  | 0, _, _ => []
  | fuel + 1, B, w =>
    let bL := decide (w ++ [false] ∈ B)
    let bR := decide (w ++ [true] ∈ B)
    bL :: bR ::
      ((if bL then encBin fuel B (w ++ [false]) else []) ++
       (if bR then encBin fuel B (w ++ [true]) else []))

def decBin : ℕ → List Bool → List Bool → Finset (List Bool) × List Bool
  | 0, _, bits => (∅, bits)
  | fuel + 1, w, bL :: bR :: rest =>
    let r1 := if bL then decBin fuel (w ++ [false]) rest else (∅, rest)
    let r2 := if bR then decBin fuel (w ++ [true]) r1.2 else (∅, r1.2)
    (insert w (r1.1 ∪ r2.1), r2.2)
  | _ + 1, _, _ => (∅, [])

lemma encBin_spec {B : Finset (List Bool)} (hB : BinTree B) :
    ∀ (fuel : ℕ) (w : List Bool), w ∈ B → (subBin B w).card ≤ fuel →
      (encBin fuel B w).length = 2 * (subBin B w).card ∧
        ∀ rem : List Bool, decBin fuel w (encBin fuel B w ++ rem) = (subBin B w, rem)
  | 0, w, hw, hcard => by
    have hpos : 0 < (subBin B w).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, List.prefix_refl w⟩⟩
    omega
  | fuel + 1, w, hw, hcard => by
    obtain ⟨hsplit, hscard⟩ := subBin_split hw
    have hcL : (subBin B (w ++ [false])).card ≤ fuel := by omega
    have hcR : (subBin B (w ++ [true])).card ≤ fuel := by omega
    have hL_len : (if decide (w ++ [false] ∈ B) then encBin fuel B (w ++ [false]) else []).length =
        2 * (subBin B (w ++ [false])).card := by
      by_cases hmemL : w ++ [false] ∈ B
      · simp [hmemL, (encBin_spec hB fuel (w ++ [false]) hmemL hcL).1]
      · simp [hmemL, subBin_eq_empty_of_notMem hB hmemL]
    have hR_len : (if decide (w ++ [true] ∈ B) then encBin fuel B (w ++ [true]) else []).length =
        2 * (subBin B (w ++ [true])).card := by
      by_cases hmemR : w ++ [true] ∈ B
      · simp [hmemR, (encBin_spec hB fuel (w ++ [true]) hmemR hcR).1]
      · simp [hmemR, subBin_eq_empty_of_notMem hB hmemR]
    refine ⟨?_, ?_⟩
    · simp only [encBin, List.length_cons, List.length_append]
      rw [hL_len, hR_len, hscard]
      omega
    · intro rem
      simp only [encBin, List.cons_append, List.append_assoc, decBin]
      have hstep1 :
          (if decide (w ++ [false] ∈ B) then
            decBin fuel (w ++ [false])
              ((if decide (w ++ [false] ∈ B) then encBin fuel B (w ++ [false]) else []) ++
               ((if decide (w ++ [true] ∈ B) then encBin fuel B (w ++ [true]) else []) ++ rem))
          else
            (∅, (if decide (w ++ [false] ∈ B) then encBin fuel B (w ++ [false]) else []) ++
                ((if decide (w ++ [true] ∈ B) then encBin fuel B (w ++ [true]) else []) ++ rem))) =
          (subBin B (w ++ [false]),
           (if decide (w ++ [true] ∈ B) then encBin fuel B (w ++ [true]) else []) ++ rem) := by
        by_cases hmemL : w ++ [false] ∈ B
        · simp [hmemL, (encBin_spec hB fuel (w ++ [false]) hmemL hcL).2]
        · simp [hmemL, subBin_eq_empty_of_notMem hB hmemL]
      rw [hstep1]
      dsimp only
      have hstep2 :
          (if decide (w ++ [true] ∈ B) then
            decBin fuel (w ++ [true])
              ((if decide (w ++ [true] ∈ B) then encBin fuel B (w ++ [true]) else []) ++ rem)
          else
            (∅, (if decide (w ++ [true] ∈ B) then encBin fuel B (w ++ [true]) else []) ++ rem)) =
          (subBin B (w ++ [true]), rem) := by
        by_cases hmemR : w ++ [true] ∈ B
        · simp [hmemR, (encBin_spec hB fuel (w ++ [true]) hmemR hcR).2]
        · simp [hmemR, subBin_eq_empty_of_notMem hB hmemR]
      rw [hstep2, ← hsplit]

noncomputable def ordTrees (n k : ℕ) : Finset (Finset Node) :=
  ((fullTree n).powersetCard k).filter Ordered

lemma ordTrees_card_le (n k : ℕ) (hk : 1 ≤ k) : (ordTrees n k).card ≤ 4 ^ k := by
  let toVec : Finset Node → (Fin (2 * k) → Bool) :=
    fun T i => (encBin k (T.image fcns) []).getD i.val false
  have hinj : Set.InjOn toVec (ordTrees n k) := by
    intro T1 hT1 T2 hT2 heq
    simp only [ordTrees, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hT1 hT2
    obtain ⟨⟨_, hcard1⟩, hord1⟩ := hT1
    obtain ⟨⟨_, hcard2⟩, hord2⟩ := hT2
    have hne1 : T1.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x1, hx1⟩ := hne1
    have hnil1 : [] ∈ T1 := hord1.2.1 x1 hx1 [] List.nil_prefix
    have hne2 : T2.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x2, hx2⟩ := hne2
    have hnil2 : [] ∈ T2 := hord2.2.1 x2 hx2 [] List.nil_prefix
    let B1 := T1.image fcns
    let B2 := T2.image fcns
    have hB1 : BinTree B1 := binTree_of_ordered hord1 hnil1
    have hB2 : BinTree B2 := binTree_of_ordered hord2 hnil2
    have hsub1 : subBin B1 [] = B1 := by ext y; simp [subBin]
    have hsub2 : subBin B2 [] = B2 := by ext y; simp [subBin]
    have hcB1 : B1.card = k := by
      rw [← hcard1]
      refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
      have h1 := unfcns_fcns (hord1.1 a ha)
      have h2 := unfcns_fcns (hord1.1 b hb)
      rw [← h1, ← h2, hab]
    have hcB2 : B2.card = k := by
      rw [← hcard2]
      refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
      have h1 := unfcns_fcns (hord2.1 a ha)
      have h2 := unfcns_fcns (hord2.1 b hb)
      rw [← h1, ← h2, hab]
    have hsp1 := encBin_spec hB1 k [] hB1.1 (by rw [hsub1, hcB1])
    have hsp2 := encBin_spec hB2 k [] hB2.1 (by rw [hsub2, hcB2])
    rw [hsub1, hcB1] at hsp1
    rw [hsub2, hcB2] at hsp2
    have hlist_eq : encBin k B1 [] = encBin k B2 [] := by
      apply List.ext_getElem
      · rw [hsp1.1, hsp2.1]
      · intro i hi1 hi2
        have hi2k : i < 2 * k := by omega
        have hfun := congrFun heq ⟨i, hi2k⟩
        simp only [toVec] at hfun
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some] at hfun
        exact hfun
    have hdec1 := hsp1.2 []
    have hdec2 := hsp2.2 []
    rw [List.append_nil] at hdec1 hdec2
    have hB_eq : B1 = B2 := by
      have hpair : decBin k [] (encBin k B1 []) = decBin k [] (encBin k B2 []) :=
        congrArg (decBin k []) hlist_eq
      rw [hdec1, hdec2] at hpair
      exact Prod.mk.inj hpair |>.1
    have himg_inv : ∀ (T : Finset Node), Ordered T → (T.image fcns).image unfcns = T := by
      intro T hord
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, ⟨y, hyT, rfl⟩, rfl⟩
        rwa [unfcns_fcns (hord.1 y hyT)]
      · intro hxT
        exact ⟨fcns x, ⟨x, hxT, rfl⟩, unfcns_fcns (hord.1 x hxT)⟩
    calc T1 = B1.image unfcns := (himg_inv T1 hord1).symm
      _ = B2.image unfcns := congrArg (Finset.image unfcns) hB_eq
      _ = T2 := himg_inv T2 hord2
  have hle : (ordTrees n k).card ≤ (Finset.univ : Finset (Fin (2 * k) → Bool)).card :=
    Finset.card_le_card_of_injOn toVec (fun _ _ => Finset.mem_univ _) hinj
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      pow_mul] at hle
  simpa using hle

/-! ### Part 4: Decomposition of `History (Fin n)` by Tree and Own-Assignment -/

def ValidAssign (n k : ℕ) (g : Fin n → Fin (k + 1)) : Prop :=
  ∀ j : Fin k, ∃ q : Fin n, g q = j.succ

noncomputable def partSet (n k : ℕ) : Finset (Fin n → Fin (k + 1)) :=
  Finset.univ.filter (ValidAssign n k)

lemma finset_sum_union_le {β : Type} [DecidableEq β] (u v : Finset β) (f : β → ℕ) :
    ∑ x ∈ u ∪ v, f x ≤ ∑ x ∈ u, f x + ∑ x ∈ v, f x := by
  induction u using Finset.induction_on with
  | empty => simp
  | @insert x u hx ih =>
    by_cases hxv : x ∈ v
    · have hmem : x ∈ u ∪ v := Finset.mem_union_right u hxv
      rw [Finset.insert_union, Finset.insert_eq_of_mem hmem, Finset.sum_insert hx]
      omega
    · have hnot : x ∉ u ∪ v := by simp [hx, hxv]
      rw [Finset.insert_union, Finset.sum_insert hnot, Finset.sum_insert hx]
      omega

lemma finset_sum_biUnion_le {α β : Type} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (finset_sum_union_le _ _ f).trans (Nat.add_le_add_left ih _)

lemma biUnion_own_congr {Q : Type} (s : Finset Node) (H1 H2 : TreeData Q)
    (h : ∀ y ∈ s, own H1 y = own H2 y) :
    s.biUnion (own H1) = s.biUnion (own H2) :=
  Finset.biUnion_congr rfl h

lemma label_eq_biUnion_own {Q : Type} [Fintype Q] [Nonempty Q] (H : History Q) :
    ∀ x ∈ H.val.nodes, H.val.label x = (H.val.nodes.filter (x.IsPrefix ·)).biUnion (own H.val) := by
  let n := Fintype.card Q
  have hn : 1 ≤ n := Fintype.card_pos
  have hsub_ft : H.val.nodes ⊆ fullTree n := nodes_sub_fullTree H
  have hex_own : ∀ (rem : ℕ) (x : Node), x ∈ H.val.nodes → n - x.length ≤ rem →
      ∀ q ∈ H.val.label x, ∃ y ∈ H.val.nodes, x.IsPrefix y ∧ q ∈ own H.val y := by
    intro rem
    induction rem with
    | zero =>
      intro x hx hrem q _
      obtain ⟨hpx, hwx⟩ := pos_and_weight_of_mem_fullTree (hsub_ft hx)
      have hlen : x.length ≤ n - 1 := (length_le_sum x hpx).trans hwx
      omega
    | succ rem ih =>
      intro x hx hrem q hqx
      by_cases hqo : q ∈ own H.val x
      · exact ⟨x, hx, List.prefix_refl x, hqo⟩
      · have hq_ch : q ∈ childLabels H.val x := by
          by_contra hnot
          exact hqo (Finset.mem_sdiff.mpr ⟨hqx, hnot⟩)
        obtain ⟨c, hc_mem, hqc⟩ := Finset.mem_biUnion.mp hq_ch
        obtain ⟨hc_nodes, i, rfl⟩ := Finset.mem_filter.mp hc_mem
        have hlen_c : (x ++ [i]).length = x.length + 1 := by simp
        obtain ⟨hpxc, hwxc⟩ := pos_and_weight_of_mem_fullTree (hsub_ft hc_nodes)
        have hlen_le : (x ++ [i]).length ≤ n - 1 := (length_le_sum _ hpxc).trans hwxc
        obtain ⟨y, hy_nodes, hpref_c, hqy⟩ := ih (x ++ [i]) hc_nodes (by omega) q hqc
        exact ⟨y, hy_nodes, (List.prefix_append x [i]).trans hpref_c, hqy⟩
  intro x hx
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · intro hqx
    obtain ⟨y, hy_nodes, hpref, hqy⟩ := hex_own n x hx (by omega) q hqx
    exact ⟨y, ⟨hy_nodes, hpref⟩, hqy⟩
  · rintro ⟨y, ⟨hy_nodes, w, rfl⟩, hqy⟩
    exact label_sub_of_prefix H.property x w hy_nodes (Finset.sdiff_subset hqy)

lemma hist_le_sum_ordTrees_partSet (n : ℕ) (hn : 1 ≤ n) :
    hist n ≤ ∑ k ∈ Finset.Icc 1 n, (ordTrees n k).card * (partSet n k).card := by
  haveI hneFin : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI hfinH : Finite (History (Fin n)) := history_finite
  let hftH : Fintype (History (Fin n)) := Fintype.ofFinite (History (Fin n))
  let allH : Finset (History (Fin n)) := @Finset.univ (History (Fin n)) hftH
  have hhist_eq : hist n = allH.card := by
    unfold hist historyCount
    rw [@Nat.card_eq_fintype_card (History (Fin n)) hftH]
    exact (@Finset.card_univ (History (Fin n)) hftH).symm
  rw [hhist_eq]
  let treeFib : Finset Node → Finset (History (Fin n)) :=
    fun T => allH.filter (fun H => H.val.nodes = T)
  let allTrees : Finset (Finset Node) := (Finset.Icc 1 n).biUnion (ordTrees n)
  have hallH_sub : allH ⊆ allTrees.biUnion treeFib := by
    intro H hH
    have hk_pos : 1 ≤ H.val.nodes.card := Finset.one_le_card.mpr ⟨[], H.property.2.1⟩
    have hk_le : H.val.nodes.card ≤ n := by simpa [Fintype.card_fin] using nodes_card_le H
    have hsub : H.val.nodes ⊆ fullTree n := by simpa [Fintype.card_fin] using nodes_sub_fullTree H
    have hT_mem : H.val.nodes ∈ ordTrees n H.val.nodes.card :=
      Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, rfl⟩, H.property.1⟩
    exact Finset.mem_biUnion.mpr
      ⟨H.val.nodes, Finset.mem_biUnion.mpr ⟨H.val.nodes.card, Finset.mem_Icc.mpr ⟨hk_pos, hk_le⟩, hT_mem⟩,
       Finset.mem_filter.mpr ⟨hH, rfl⟩⟩
  have hfib_le : ∀ k ∈ Finset.Icc 1 n, ∀ T ∈ ordTrees n k, (treeFib T).card ≤ (partSet n k).card := by
    intro k _ T hT
    have hT_card : T.card = k := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    let eT : ↥T ≃ Fin k := (Fintype.equivFin ↥T).trans (finCongr ( (Fintype.card_coe T).trans hT_card ))
    let toAssign : History (Fin n) → (Fin n → Fin (k + 1)) := fun H q =>
      if h : ∃ z : ↥T, q ∈ own H.val z.val then (eT (Classical.choose h)).succ else 0
    have hmaps : Set.MapsTo toAssign (treeFib T) (partSet n k) := by
      intro H hH
      have hHT : H.val.nodes = T := (Finset.mem_filter.mp hH).2
      simp only [partSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      let z : ↥T := eT.symm j
      have hz_nodes : z.val ∈ H.val.nodes := hHT ▸ z.property
      obtain ⟨q, hq_own⟩ := own_nonempty H hz_nodes
      have hex : ∃ w : ↥T, q ∈ own H.val w.val := ⟨z, hq_own⟩
      refine ⟨q, ?_⟩
      simp only [toAssign, dif_pos hex]
      have hw_eq : Classical.choose hex = z := by
        by_contra hne
        have hne_val : (Classical.choose hex).val ≠ z.val := fun h => hne (Subtype.ext h)
        have hw_nodes : (Classical.choose hex).val ∈ H.val.nodes := hHT ▸ (Classical.choose hex).property
        exact Finset.disjoint_left.mp (own_disjoint H.property hw_nodes hz_nodes hne_val)
          (Classical.choose_spec hex) hq_own
      rw [hw_eq, eT.apply_symm_apply]
    have hinj : Set.InjOn toAssign (treeFib T) := by
      intro H1 hH1 H2 hH2 heq
      have hHT1 : H1.val.nodes = T := (Finset.mem_filter.mp hH1).2
      have hHT2 : H2.val.nodes = T := (Finset.mem_filter.mp hH2).2
      have hown_iff : ∀ (H : History (Fin n)), H.val.nodes = T →
          ∀ (z : ↥T) (q : Fin n), q ∈ own H.val z.val ↔ toAssign H q = (eT z).succ := by
        intro H hHT z q
        constructor
        · intro hq
          have hex : ∃ w : ↥T, q ∈ own H.val w.val := ⟨z, hq⟩
          simp only [toAssign, dif_pos hex]
          have hw_eq : Classical.choose hex = z := by
            by_contra hne
            have hne_val : (Classical.choose hex).val ≠ z.val := fun h => hne (Subtype.ext h)
            exact Finset.disjoint_left.mp
              (own_disjoint H.property (hHT ▸ (Classical.choose hex).property) (hHT ▸ z.property) hne_val)
              (Classical.choose_spec hex) hq
          rw [hw_eq]
        · intro hval
          simp only [toAssign] at hval
          split_ifs at hval with hex
          · have hsucc := Fin.succ_inj.mp hval
            have hwz : Classical.choose hex = z := eT.injective hsucc
            rw [← hwz]
            exact Classical.choose_spec hex
          · exact absurd hval.symm (Fin.succ_ne_zero _)
      have hown_eq : ∀ y ∈ T, own H1.val y = own H2.val y := by
        intro y hyT
        ext q
        rw [hown_iff H1 hHT1 ⟨y, hyT⟩ q, hown_iff H2 hHT2 ⟨y, hyT⟩ q, heq]
      have hlbl_eq : H1.val.label = H2.val.label := by
        funext x
        by_cases hxT : x ∈ T
        · rw [label_eq_biUnion_own H1 x (hHT1 ▸ hxT),
              label_eq_biUnion_own H2 x (hHT2 ▸ hxT), hHT1, hHT2]
          exact biUnion_own_congr (T.filter (x.IsPrefix ·)) H1.val H2.val
            (fun y hy => hown_eq y (Finset.mem_filter.mp hy).1)
        · rw [H1.property.2.2.1 x (hHT1 ▸ hxT), H2.property.2.2.1 x (hHT2 ▸ hxT)]
      apply Subtype.ext
      rcases H1 with ⟨⟨n1, l1⟩, _⟩
      rcases H2 with ⟨⟨n2, l2⟩, _⟩
      simp only at hHT1 hHT2 hlbl_eq
      subst hHT1 hHT2 hlbl_eq
      rfl
    exact Finset.card_le_card_of_injOn toAssign hmaps hinj
  calc allH.card
      ≤ (allTrees.biUnion treeFib).card := Finset.card_le_card hallH_sub
    _ ≤ ∑ T ∈ allTrees, (treeFib T).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ∑ T ∈ ordTrees n k, (treeFib T).card :=
        finset_sum_biUnion_le (Finset.Icc 1 n) (ordTrees n) (fun T => (treeFib T).card)
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ∑ _T ∈ ordTrees n k, (partSet n k).card :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum (hfib_le k hk)
    _ = ∑ k ∈ Finset.Icc 1 n, (ordTrees n k).card * (partSet n k).card := by simp

/-! ### Part 5: Generating-Function Bound on `partSet n k` -/

lemma partSet_zero (n : ℕ) : (partSet n 0).card = 1 := by
  have heq : partSet n 0 = {fun _ => 0} := by
    ext g
    simp only [partSet, ValidAssign, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    refine ⟨fun _ => funext fun q => Fin.ext (by have := (g q).isLt; omega),
            fun _ j => Fin.elim0 j⟩
  rw [heq, Finset.card_singleton]

lemma partSet_succ_le (n k : ℕ) :
    (partSet n (k + 1)).card ≤
      ∑ m ∈ Finset.Icc 1 n, Nat.choose n m * (partSet (n - m) k).card := by
  let lastVal : Fin (k + 2) := Fin.last (k + 1)
  let fibOf : (Fin n → Fin (k + 2)) → Finset (Fin n) :=
    fun g => Finset.univ.filter (fun q => g q = lastVal)
  let pFib : Finset (Fin n) → Finset (Fin n → Fin (k + 2)) :=
    fun S => (partSet n (k + 1)).filter (fun g => fibOf g = S)
  let allSubs : Finset (Finset (Fin n)) :=
    (Finset.Icc 1 n).biUnion (fun m => (Finset.univ : Finset (Fin n)).powersetCard m)
  have hsub_all : partSet n (k + 1) ⊆ allSubs.biUnion pFib := by
    intro g hg
    have hv : ValidAssign n (k + 1) g := (Finset.mem_filter.mp hg).2
    obtain ⟨q0, hq0⟩ := hv (Fin.last k)
    have hlast_eq : (Fin.last k).succ = lastVal := by ext; simp [lastVal]
    have hq0_mem : q0 ∈ fibOf g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0.trans hlast_eq⟩
    have hm1 : 1 ≤ (fibOf g).card := Finset.one_le_card.mpr ⟨q0, hq0_mem⟩
    have hmn : (fibOf g).card ≤ n :=
      (Finset.card_le_card (Finset.subset_univ _)).trans (Finset.card_fin n).le
    exact Finset.mem_biUnion.mpr
      ⟨fibOf g,
       Finset.mem_biUnion.mpr ⟨(fibOf g).card, Finset.mem_Icc.mpr ⟨hm1, hmn⟩,
         Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩,
       Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
  have hpFib_le : ∀ m ∈ Finset.Icc 1 n,
      ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (pFib S).card ≤ (partSet (n - m) k).card := by
    intro m _ S hS
    have hScard : S.card = m := (Finset.mem_powersetCard.mp hS).2
    let Sc : Finset (Fin n) := Finset.univ \ S
    have hSc_card : Sc.card = n - m := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hScard]
    let eSc : Fin (n - m) ≃ ↥Sc :=
      ((Fintype.equivFin ↥Sc).trans (finCongr ((Fintype.card_coe Sc).trans hSc_card))).symm
    let restr : (Fin n → Fin (k + 2)) → (Fin (n - m) → Fin (k + 1)) := fun g r =>
      if hlt : (g (eSc r).val).val < k + 1 then ⟨(g (eSc r).val).val, hlt⟩ else 0
    have hmaps : Set.MapsTo restr (pFib S) (partSet (n - m) k) := by
      intro g hg
      obtain ⟨hg_part, hgS⟩ := Finset.mem_filter.mp hg
      have hv : ValidAssign n (k + 1) g := (Finset.mem_filter.mp hg_part).2
      simp only [partSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      obtain ⟨q, hq⟩ := hv j.castSucc
      have hval_q : (g q).val = j.val + 1 := by
        rw [hq]; rfl
      have hlt_q : (g q).val < k + 1 := by omega
      have hnotS : q ∉ S := by
        rw [← hgS]
        simp only [fibOf, lastVal, Finset.mem_filter, Finset.mem_univ, true_and]
        intro heq_last
        have : (g q).val = k + 1 := congrArg Fin.val heq_last
        omega
      have hqSc : q ∈ Sc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hnotS⟩
      let r : Fin (n - m) := eSc.symm ⟨q, hqSc⟩
      refine ⟨r, ?_⟩
      have heSc_r : (eSc r).val = q := congrArg Subtype.val (eSc.apply_symm_apply ⟨q, hqSc⟩)
      simp only [restr, heSc_r, dif_pos hlt_q]
      exact Fin.ext hval_q
    have hinj : Set.InjOn restr (pFib S) := by
      intro g1 hg1 g2 hg2 heq
      obtain ⟨_, hg1S⟩ := Finset.mem_filter.mp hg1
      obtain ⟨_, hg2S⟩ := Finset.mem_filter.mp hg2
      funext q
      by_cases hqS : q ∈ S
      · have hq1 : q ∈ fibOf g1 := hg1S.symm ▸ hqS
        have hq2 : q ∈ fibOf g2 := hg2S.symm ▸ hqS
        have h1 : g1 q = lastVal := (Finset.mem_filter.mp hq1).2
        have h2 : g2 q = lastVal := (Finset.mem_filter.mp hq2).2
        exact h1.trans h2.symm
      · have h1lt : (g1 q).val < k + 1 := by
          have hne : g1 q ≠ lastVal := fun h =>
            hqS (hg1S ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)
          have hle := (g1 q).isLt
          have hne_val : (g1 q).val ≠ k + 1 := fun hv => hne (Fin.ext hv)
          omega
        have h2lt : (g2 q).val < k + 1 := by
          have hne : g2 q ≠ lastVal := fun h =>
            hqS (hg2S ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩)
          have hle := (g2 q).isLt
          have hne_val : (g2 q).val ≠ k + 1 := fun hv => hne (Fin.ext hv)
          omega
        have hqSc : q ∈ Sc := Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqS⟩
        let r : Fin (n - m) := eSc.symm ⟨q, hqSc⟩
        have heSc_r : (eSc r).val = q := congrArg Subtype.val (eSc.apply_symm_apply ⟨q, hqSc⟩)
        have hr_eq := congrFun heq r
        simp only [restr, heSc_r, dif_pos h1lt, dif_pos h2lt] at hr_eq
        exact Fin.ext (congrArg (Fin.val : Fin (k + 1) → ℕ) hr_eq)
    exact Finset.card_le_card_of_injOn restr hmaps hinj
  calc (partSet n (k + 1)).card
      ≤ (allSubs.biUnion pFib).card := Finset.card_le_card hsub_all
    _ ≤ ∑ S ∈ allSubs, (pFib S).card := Finset.card_biUnion_le
    _ ≤ ∑ m ∈ Finset.Icc 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, (pFib S).card :=
        finset_sum_biUnion_le (Finset.Icc 1 n)
          (fun m => (Finset.univ : Finset (Fin n)).powersetCard m) (fun S => (pFib S).card)
    _ ≤ ∑ m ∈ Finset.Icc 1 n, ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          (partSet (n - m) k).card :=
        Finset.sum_le_sum fun m hm => Finset.sum_le_sum (hpFib_le m hm)
    _ = ∑ m ∈ Finset.Icc 1 n, Nat.choose n m * (partSet (n - m) k).card := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_fin, smul_eq_mul]

lemma pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ (n.factorial : ℝ) * Real.exp x := by
  have hmem : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_self n)
  have hnonneg : ∀ i ∈ Finset.range (n + 1), 0 ≤ x ^ i / (i.factorial : ℝ) :=
    fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _)
  have hterm : x ^ n / (n.factorial : ℝ) ≤ ∑ i ∈ Finset.range (n + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum hnonneg hmem
  have hsum := Real.sum_le_exp_of_nonneg hx (n + 1)
  have hle := hterm.trans hsum
  have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rwa [div_le_iff₀ hfac_pos, mul_comm (Real.exp x)] at hle

lemma sum_Icc_pow_div_factorial_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, x ^ m / (m.factorial : ℝ) ≤ Real.exp x - 1 := by
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0not : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
  have hsum := Real.sum_le_exp_of_nonneg hx (n + 1)
  rw [hrange, Finset.sum_insert h0not] at hsum
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsum
  linarith

lemma partSet_egf_bound : ∀ (k n : ℕ) {x : ℝ}, 0 ≤ x →
    ((partSet n k).card : ℝ) * x ^ n ≤
      (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k
  | 0, n, x, hx => by
    rw [partSet_zero]
    simp only [Nat.cast_one, one_mul, pow_zero, mul_one]
    exact pow_le_factorial_mul_exp hx n
  | k + 1, n, x, hx => by
    have hexp_ge1 : 1 ≤ Real.exp x := by
      have h := Real.add_one_le_exp x
      linarith
    have hexp_sub_nn : 0 ≤ Real.exp x - 1 := by linarith
    have hrec_nat := partSet_succ_le n k
    have hrec_real : ((partSet n (k + 1)).card : ℝ) * x ^ n ≤
        ∑ m ∈ Finset.Icc 1 n,
          (Nat.choose n m : ℝ) * (((partSet (n - m) k).card : ℝ) * x ^ (n - m)) * x ^ m := by
      have hcast : ((partSet n (k + 1)).card : ℝ) ≤
          ∑ m ∈ Finset.Icc 1 n, (Nat.choose n m : ℝ) * ((partSet (n - m) k).card : ℝ) := by
        exact_mod_cast hrec_nat
      calc ((partSet n (k + 1)).card : ℝ) * x ^ n
          ≤ (∑ m ∈ Finset.Icc 1 n, (Nat.choose n m : ℝ) * ((partSet (n - m) k).card : ℝ)) * x ^ n :=
            mul_le_mul_of_nonneg_right hcast (pow_nonneg hx n)
        _ = ∑ m ∈ Finset.Icc 1 n,
              (Nat.choose n m : ℝ) * ((partSet (n - m) k).card : ℝ) * x ^ n :=
            Finset.sum_mul _ _ _
        _ = ∑ m ∈ Finset.Icc 1 n,
              (Nat.choose n m : ℝ) * (((partSet (n - m) k).card : ℝ) * x ^ (n - m)) * x ^ m := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
            have hpow : x ^ n = x ^ (n - m) * x ^ m := by
              rw [← pow_add, Nat.sub_add_cancel hmn]
            rw [hpow]; ring
    have hterm_le : ∀ m ∈ Finset.Icc 1 n,
        (Nat.choose n m : ℝ) * (((partSet (n - m) k).card : ℝ) * x ^ (n - m)) * x ^ m ≤
          (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k * (x ^ m / (m.factorial : ℝ)) := by
      intro m hm
      have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
      have ih := partSet_egf_bound k (n - m) hx
      have hchoose_nn : (0 : ℝ) ≤ (Nat.choose n m : ℝ) := Nat.cast_nonneg _
      have hxm_nn : 0 ≤ x ^ m := pow_nonneg hx m
      have hchoose_fac : (Nat.choose n m : ℝ) * ((n - m).factorial : ℝ) =
          (n.factorial : ℝ) / (m.factorial : ℝ) := by
        have hnat := Nat.choose_mul_factorial_mul_factorial hmn
        have hcast : (Nat.choose n m : ℝ) * (m.factorial : ℝ) * ((n - m).factorial : ℝ) =
            (n.factorial : ℝ) := by exact_mod_cast hnat
        have hmpos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
        rw [eq_div_iff hmpos.ne']
        linarith
      calc (Nat.choose n m : ℝ) * (((partSet (n - m) k).card : ℝ) * x ^ (n - m)) * x ^ m
          ≤ (Nat.choose n m : ℝ) *
              (((n - m).factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k) * x ^ m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ih hchoose_nn) hxm_nn
        _ = ((Nat.choose n m : ℝ) * ((n - m).factorial : ℝ)) *
              Real.exp x * (Real.exp x - 1) ^ k * x ^ m := by ring
        _ = (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k *
              (x ^ m / (m.factorial : ℝ)) := by
            rw [hchoose_fac]; ring
    calc ((partSet n (k + 1)).card : ℝ) * x ^ n
        ≤ ∑ m ∈ Finset.Icc 1 n,
            (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k * (x ^ m / (m.factorial : ℝ)) :=
          hrec_real.trans (Finset.sum_le_sum hterm_le)
      _ = (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k *
            (∑ m ∈ Finset.Icc 1 n, x ^ m / (m.factorial : ℝ)) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ k * (Real.exp x - 1) := by
          refine mul_le_mul_of_nonneg_left (sum_Icc_pow_div_factorial_le hx n) ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg x))
            (pow_nonneg hexp_sub_nn k)
      _ = (n.factorial : ℝ) * Real.exp x * (Real.exp x - 1) ^ (k + 1) := by
          rw [pow_succ]; ring

/-! ### Part 6: Elementary Factorial & Numerical Asymptotics (`o((1.65 n)^n)`) -/

lemma factorial_le_stirling : ∀ n : ℕ, 1 ≤ n →
    (n.factorial : ℝ) ≤ Real.exp 1 * (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n
  | 0, hn => by omega
  | 1, _ => by
    simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one]
    rw [mul_div_cancel₀ _ (Real.exp_ne_zero 1)]
  | m + 2, _ => by
    let k := m + 1
    have hk1 : 1 ≤ k := Nat.succ_pos m
    have ih := factorial_le_stirling k hk1
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
    have hk1_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
    let u : ℝ := 1 / (k + 1 : ℝ)
    have h1sub : (k : ℝ) / (k + 1 : ℝ) ≤ Real.exp (-u) := by
      have heq : 1 - u = (k : ℝ) / (k + 1 : ℝ) := by
        simp only [u]; field_simp; ring
      rw [← heq]
      exact Real.one_sub_le_exp_neg u
    have hexp_u : Real.exp u ≤ (k + 1 : ℝ) / (k : ℝ) := by
      rw [Real.exp_neg] at h1sub
      have hexp_pos : 0 < Real.exp u := Real.exp_pos u
      have hdiv_pos : 0 < (k : ℝ) / (k + 1 : ℝ) := div_pos hk_pos hk1_pos
      have hmul : (k : ℝ) / (k + 1 : ℝ) * Real.exp u ≤ 1 := by
        calc (k : ℝ) / (k + 1 : ℝ) * Real.exp u
            ≤ (Real.exp u)⁻¹ * Real.exp u := mul_le_mul_of_nonneg_right h1sub hexp_pos.le
          _ = 1 := inv_mul_cancel₀ hexp_pos.ne'
      rw [div_mul_eq_mul_div, div_le_one hk1_pos] at hmul
      rwa [le_div_iff₀ hk_pos, mul_comm]
    have hexp1_le : Real.exp 1 ≤ ((k + 1 : ℝ) / (k : ℝ)) ^ (k + 1) := by
      have hpow : (Real.exp u) ^ (k + 1) ≤ ((k + 1 : ℝ) / (k : ℝ)) ^ (k + 1) :=
        pow_le_pow_left₀ (Real.exp_nonneg u) hexp_u (k + 1)
      have hexp_pow : (Real.exp u) ^ (k + 1) = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        simp only [u, Nat.cast_add, Nat.cast_one]
        exact mul_one_div_cancel hk1_pos.ne'
      rwa [hexp_pow] at hpow
    have hpow_step : (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k ≤
        ((k + 1 : ℝ) / Real.exp 1) ^ (k + 1) := by
      rw [div_pow] at hexp1_le
      have hkpow_pos : 0 < (k : ℝ) ^ (k + 1) := pow_pos hk_pos (k + 1)
      have hmul1 : Real.exp 1 * (k : ℝ) ^ (k + 1) ≤ (k + 1 : ℝ) ^ (k + 1) :=
        (le_div_iff₀ hkpow_pos).mp hexp1_le
      have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
      have hepow_pos : 0 < (Real.exp 1) ^ (k + 1) := pow_pos he_pos (k + 1)
      rw [div_pow, div_pow, pow_succ (Real.exp 1) k]
      have hrew : (k : ℝ) * ((k : ℝ) ^ k / (Real.exp 1) ^ k) =
          (Real.exp 1 * (k : ℝ) ^ (k + 1)) / ((Real.exp 1) ^ k * Real.exp 1) := by
        rw [pow_succ (k : ℝ) k]
        field_simp [he_pos.ne']
      rw [hrew]
      exact div_le_div_of_nonneg_right hmul1 (by positivity)
    have hm2_eq : m + 2 = k + 1 := rfl
    have hm2_cast : ((m + 2 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp [k]; ring
    rw [hm2_eq, hm2_cast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc ((k : ℝ) + 1) * (k.factorial : ℝ)
        ≤ ((k : ℝ) + 1) * (Real.exp 1 * (k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k) :=
          mul_le_mul_of_nonneg_left ih hk1_pos.le
      _ = Real.exp 1 * ((k : ℝ) + 1) * ((k : ℝ) * ((k : ℝ) / Real.exp 1) ^ k) := by ring
      _ ≤ Real.exp 1 * ((k : ℝ) + 1) * (((k : ℝ) + 1) / Real.exp 1) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left hpow_step (by positivity)

noncomputable def x0Val : ℝ := 22314 / 100000

lemma exp_x0_le : Real.exp x0Val ≤ (5 / 4 : ℝ) := by
  have hb := Real.exp_bound (x := x0Val) (by norm_num [x0Val]) (n := 5) (by norm_num)
  have hle := (abs_sub_le_iff.mp hb).1
  have hnum : (∑ m ∈ Finset.range 5, x0Val ^ m / (m.factorial : ℝ)) +
      |x0Val| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * (5 : ℝ))) ≤ (5 / 4 : ℝ) := by
    norm_num [x0Val, Finset.sum_range_succ, Nat.factorial]
  linarith

lemma exp_one_bounds : (1957 / 720 : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ 3 := by
  refine ⟨?_, ?_⟩
  · have hlo := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 7
    have hnum : (1957 / 720 : ℝ) = ∑ i ∈ Finset.range 7, (1 : ℝ) ^ i / (i.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  · have hb := Real.exp_bound (x := (1 : ℝ)) (by norm_num) (n := 4) (by norm_num)
    have hhi := (abs_sub_le_iff.mp hb).1
    have hnum : (∑ m ∈ Finset.range 4, (1 : ℝ) ^ m / (m.factorial : ℝ)) +
        |(1 : ℝ)| ^ 4 * ((Nat.succ 4 : ℝ) / ((Nat.factorial 4 : ℝ) * (4 : ℝ))) ≤ 3 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith

lemma hist_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    (hist n : ℝ) ≤ 4 * (n : ℝ) ^ 2 * ((1649 / 1000 : ℝ) * (n : ℝ)) ^ n := by
  have hx0_pos : 0 < x0Val := by norm_num [x0Val]
  have hx0_nn : 0 ≤ x0Val := hx0_pos.le
  have hexp_x0 : Real.exp x0Val ≤ (5 / 4 : ℝ) := exp_x0_le
  have hexp_ge1 : 1 ≤ Real.exp x0Val := by
    have h := Real.add_one_le_exp x0Val; linarith
  have hexp_sub_le : Real.exp x0Val - 1 ≤ (1 / 4 : ℝ) := by linarith
  have hexp_sub_nn : 0 ≤ Real.exp x0Val - 1 := by linarith
  obtain ⟨he_lo, he_hi⟩ := exp_one_bounds
  have hterm_k : ∀ k ∈ Finset.Icc 1 n,
      ((ordTrees n k).card : ℝ) * ((partSet n k).card : ℝ) * x0Val ^ n ≤
        (5 / 4 : ℝ) * (n.factorial : ℝ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hord_le : ((ordTrees n k).card : ℝ) ≤ (4 : ℝ) ^ k := by
      exact_mod_cast ordTrees_card_le n k hk1
    have hpart_le := partSet_egf_bound k n hx0_nn
    have h4sub : (4 : ℝ) ^ k * (Real.exp x0Val - 1) ^ k ≤ 1 := by
      rw [← mul_pow]
      have hmul : (4 : ℝ) * (Real.exp x0Val - 1) ≤ (1 : ℝ) := by linarith
      have hmnn : 0 ≤ (4 : ℝ) * (Real.exp x0Val - 1) := by positivity
      calc ((4 : ℝ) * (Real.exp x0Val - 1)) ^ k ≤ (1 : ℝ) ^ k := pow_le_pow_left₀ hmnn hmul k
        _ = 1 := one_pow k
    calc ((ordTrees n k).card : ℝ) * ((partSet n k).card : ℝ) * x0Val ^ n
        = ((ordTrees n k).card : ℝ) * (((partSet n k).card : ℝ) * x0Val ^ n) := by ring
      _ ≤ (4 : ℝ) ^ k * ((n.factorial : ℝ) * Real.exp x0Val * (Real.exp x0Val - 1) ^ k) :=
          mul_le_mul hord_le hpart_le (by positivity) (by positivity)
      _ = (n.factorial : ℝ) * Real.exp x0Val * ((4 : ℝ) ^ k * (Real.exp x0Val - 1) ^ k) := by ring
      _ ≤ (n.factorial : ℝ) * (5 / 4 : ℝ) * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hexp_x0 (Nat.cast_nonneg _))
            h4sub (by positivity) (by positivity)
      _ = (5 / 4 : ℝ) * (n.factorial : ℝ) := by ring
  have hsum_hist : (hist n : ℝ) * x0Val ^ n ≤ (n : ℝ) * ((5 / 4 : ℝ) * (n.factorial : ℝ)) := by
    have hnat := hist_le_sum_ordTrees_partSet n hn
    have hcast : (hist n : ℝ) ≤
        ∑ k ∈ Finset.Icc 1 n, ((ordTrees n k).card : ℝ) * ((partSet n k).card : ℝ) := by
      exact_mod_cast hnat
    have hcard_nat : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
    have hcard_icc : ((Finset.Icc 1 n).card : ℝ) = (n : ℝ) := by exact_mod_cast hcard_nat
    calc (hist n : ℝ) * x0Val ^ n
        ≤ (∑ k ∈ Finset.Icc 1 n, ((ordTrees n k).card : ℝ) * ((partSet n k).card : ℝ)) * x0Val ^ n :=
          mul_le_mul_of_nonneg_right hcast (pow_nonneg hx0_nn n)
      _ = ∑ k ∈ Finset.Icc 1 n,
            ((ordTrees n k).card : ℝ) * ((partSet n k).card : ℝ) * x0Val ^ n :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ _k ∈ Finset.Icc 1 n, (5 / 4 : ℝ) * (n.factorial : ℝ) := Finset.sum_le_sum hterm_k
      _ = (n : ℝ) * ((5 / 4 : ℝ) * (n.factorial : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard_icc]
  have hx0n_pos : 0 < x0Val ^ n := pow_pos hx0_pos n
  have hdiv_hist : (hist n : ℝ) ≤
      ((5 / 4 : ℝ) * Real.exp 1) * (n : ℝ) ^ 2 * ((n : ℝ) / (Real.exp 1 * x0Val)) ^ n := by
    have hst := factorial_le_stirling n hn
    have hpow_eq : ((n : ℝ) / Real.exp 1) ^ n / x0Val ^ n =
        ((n : ℝ) / (Real.exp 1 * x0Val)) ^ n := by
      rw [← div_pow, div_div]
    calc (hist n : ℝ)
        ≤ (n : ℝ) * ((5 / 4 : ℝ) * (n.factorial : ℝ)) / x0Val ^ n :=
          (le_div_iff₀ hx0n_pos).mpr hsum_hist
      _ ≤ (n : ℝ) * ((5 / 4 : ℝ) * (Real.exp 1 * (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n)) / x0Val ^ n :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hst (by norm_num)) (Nat.cast_nonneg _))
            hx0n_pos.le
      _ = ((5 / 4 : ℝ) * Real.exp 1) * (n : ℝ) ^ 2 * (((n : ℝ) / Real.exp 1) ^ n / x0Val ^ n) := by ring
      _ = ((5 / 4 : ℝ) * Real.exp 1) * (n : ℝ) ^ 2 * ((n : ℝ) / (Real.exp 1 * x0Val)) ^ n := by
          rw [hpow_eq]
  have hbase_le : (n : ℝ) / (Real.exp 1 * x0Val) ≤ (1649 / 1000 : ℝ) * (n : ℝ) := by
    have hprod_ge : (1000 / 1649 : ℝ) ≤ Real.exp 1 * x0Val := by
      have hnum : (1000 / 1649 : ℝ) ≤ (1957 / 720 : ℝ) * x0Val := by norm_num [x0Val]
      exact hnum.trans (mul_le_mul_of_nonneg_right he_lo hx0_nn)
    have hex_pos : 0 < Real.exp 1 * x0Val := mul_pos (Real.exp_pos 1) hx0_pos
    rw [div_le_iff₀ hex_pos]
    calc (n : ℝ) = (n : ℝ) * ((1649 / 1000 : ℝ) * (1000 / 1649 : ℝ)) := by ring
      _ ≤ (n : ℝ) * ((1649 / 1000 : ℝ) * (Real.exp 1 * x0Val)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hprod_ge (by norm_num)) (Nat.cast_nonneg _)
      _ = (1649 / 1000 : ℝ) * (n : ℝ) * (Real.exp 1 * x0Val) := by ring
  have hcoeff_le : (5 / 4 : ℝ) * Real.exp 1 ≤ 4 := by linarith
  have hbase_nn : 0 ≤ (n : ℝ) / (Real.exp 1 * x0Val) := by positivity
  calc (hist n : ℝ)
      ≤ ((5 / 4 : ℝ) * Real.exp 1) * (n : ℝ) ^ 2 * ((n : ℝ) / (Real.exp 1 * x0Val)) ^ n := hdiv_hist
    _ ≤ 4 * (n : ℝ) ^ 2 * ((1649 / 1000 : ℝ) * (n : ℝ)) ^ n := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hcoeff_le (sq_nonneg _))
          (pow_le_pow_left₀ hbase_nn hbase_le n) (pow_nonneg hbase_nn n) (by positivity)

lemma hist_little_o : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (hist n : ℝ) ≤ ε * stateScale n := by
  intro ε hε
  let r : ℝ := 1650 / 1649
  have hr : 1 < r := by norm_num [r]
  have htend := tendsto_pow_const_div_const_pow_of_one_lt 2 hr
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / r ^ n < ε / 4 :=
    htend.eventually (gt_mem_nhds (by linarith))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N0, hN0⟩ := hev
  refine ⟨max 1 N0, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N0) hn
  have hn0 : N0 ≤ n := le_trans (le_max_right 1 N0) hn
  have hlt := hN0 n hn0
  have hub := hist_upper_bound n hn1
  have hscale_pos : 0 < stateScale n := by
    unfold stateScale
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
    positivity
  have hratio : ((1649 / 1000 : ℝ) * (n : ℝ)) ^ n = stateScale n / r ^ n := by
    have hr_pos : 0 < r := by norm_num [r]
    have hrn_pos : 0 < r ^ n := pow_pos hr_pos n
    rw [eq_div_iff hrn_pos.ne', ← mul_pow]
    unfold stateScale
    congr 1
    simp only [r]; ring
  calc (hist n : ℝ)
      ≤ 4 * (n : ℝ) ^ 2 * ((1649 / 1000 : ℝ) * (n : ℝ)) ^ n := hub
    _ = 4 * ((n : ℝ) ^ 2 / r ^ n) * stateScale n := by rw [hratio]; ring
    _ ≤ 4 * (ε / 4) * stateScale n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlt.le (by norm_num)) hscale_pos.le
    _ = ε * stateScale n := by ring

end BuchiRabinIndex.LowerBound.Supplement.Thm25Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
  BuchiRabinIndex.LowerBound.Supplement.Thm25Aux in
theorem solution :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (hist n : ℝ) ≤ ε * stateScale n) ∧
    (∀ (Q Sigma : Type) [Fintype Q] [Nonempty Q] [Fintype Sigma] (B : NBW Q Sigma),
      Finite (History Q) ∧ historyCount Q = hist (Fintype.card Q) ∧
      (Even (Fintype.card Q) →
        (reducedCondition B).card ≤ 3 * 2 ^ (Fintype.card Q / 2 - 1) - 1) ∧
      (Odd (Fintype.card Q) →
        (reducedCondition B).card ≤ 2 ^ ((Fintype.card Q + 1) / 2) - 1) ∧
      transitionLanguage B (reducedCondition B) = language B) := by
  refine ⟨hist_little_o, ?_⟩
  intro Q Sigma _ _ _ B
  let n := Fintype.card Q
  have hn : 1 ≤ n := Fintype.card_pos
  have hred_le := reducedCondition_card_le_sum_sf B
  obtain ⟨hsum_ev, hsum_odd⟩ := sum_sf_closed n hn
  refine ⟨history_finite, historyCount_eq_hist, ?_, ?_, theorem_24 B⟩
  · intro hev
    exact hred_le.trans (hsum_ev hev).le
  · intro hodd
    exact hred_le.trans (hsum_odd hodd).le
