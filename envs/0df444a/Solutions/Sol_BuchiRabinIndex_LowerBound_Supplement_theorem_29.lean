-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.Supplement.theorem_29
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:16:11.682065+00:00
-- url     : https://prove2.me/submissions/ce43bf38-aaa6-4361-a214-ae65a0e2bb82

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging
import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_38
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_39
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_15
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_19

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement.Thm29Aux
open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
open scoped Classical

noncomputable def colourImage {I : Type} {n : ℕ} (Id : Vertex n → I) : Finset I :=
  (Finset.univ : Finset (Vertex n)).image Id

lemma label_sub_of_prefix {Q : Type} {H : TreeData Q} (hv : Valid H) :
    ∀ (x : Node) (w : List ℕ), x ++ w ∈ H.nodes → H.label (x ++ w) ⊆ H.label x
  | x, [], _ => by simp
  | x, i :: rest, hmem => by
    have hxi_mem : x ++ [i] ∈ H.nodes :=
      hv.1.2.1 (x ++ (i :: rest)) hmem (x ++ [i]) ⟨rest, by simp⟩
    have h1 : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
      label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hmem)
    have h1' : H.label (x ++ i :: rest) ⊆ H.label (x ++ [i]) := by simpa using h1
    have hchild : x ++ [i] ∈ children H.nodes x := by
      simp [children, hxi_mem]
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

lemma simple_of_root_card_le {Q : Type} (H : History Q)
    (hroot : (H.val.label []).card ≤ H.val.nodes.card) : Simple H := by
  have hv := H.property
  have hpos : ∀ z ∈ H.val.nodes, 1 ≤ (own H.val z).card := by
    intro z hz
    rw [Finset.one_le_card]
    have hss := hv.2.2.2.2.2 z hz
    rw [own, Finset.sdiff_nonempty]
    exact fun h => hss.not_subset h
  have hdisj : (H.val.nodes : Set Node).PairwiseDisjoint (own H.val) :=
    fun a ha b hb hne => own_disjoint hv ha hb hne
  have hbi_sub : H.val.nodes.biUnion (own H.val) ⊆ H.val.label [] := by
    intro q hq
    obtain ⟨z, hz, hqz⟩ := Finset.mem_biUnion.mp hq
    have hz_sub : H.val.label z ⊆ H.val.label [] := by
      simpa using label_sub_of_prefix hv [] z (by simpa using hz)
    exact hz_sub (Finset.sdiff_subset hqz)
  have hsum_le : ∑ z ∈ H.val.nodes, (own H.val z).card ≤ H.val.nodes.card := by
    calc ∑ z ∈ H.val.nodes, (own H.val z).card
        = (H.val.nodes.biUnion (own H.val)).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (H.val.label []).card := Finset.card_le_card hbi_sub
      _ ≤ H.val.nodes.card := hroot
  intro z hz
  by_contra hne1
  have hz1 : 1 ≤ (own H.val z).card := hpos z hz
  have hgt1 : 1 < (own H.val z).card := by omega
  have hlt : ∑ _w ∈ H.val.nodes, 1 < ∑ w ∈ H.val.nodes, (own H.val w).card :=
    Finset.sum_lt_sum hpos ⟨z, hz, hgt1⟩
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt
  omega

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

lemma simple_of_htree {n : ℕ} {T : Finset Node} {H : History (Fin n)}
    (hH : Htree n T = some H) : Simple H := by
  unfold Htree asHistory at hH
  split_ifs at hH with hv
  simp only [Option.some.injEq] at hH
  have hval : H.val = canonicalData n T := by rw [← hH]
  have hnodes : H.val.nodes = T := by rw [hval]; rfl
  apply simple_of_root_card_le H
  rw [hnodes, hval]
  let fib : Node → Finset (Fin n) := fun y => Finset.univ.filter fun q : Fin n => q.val = rank T y
  have hsub : (canonicalData n T).label [] ⊆ T.biUnion fib := by
    intro q hq
    unfold canonicalData at hq
    dsimp only at hq
    split_ifs at hq with hnil
    · obtain ⟨_, y, hyT, _, hqr⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_biUnion.mpr ⟨y, hyT, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqr⟩⟩
    · simp at hq
  have hfib_le : ∀ y ∈ T, (fib y).card ≤ 1 := by
    intro y _
    refine Finset.card_le_one.mpr fun q1 h1 q2 h2 => ?_
    exact Fin.ext ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
  calc ((canonicalData n T).label []).card
      ≤ (T.biUnion fib).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ T, (fib y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ T, 1 := Finset.sum_le_sum hfib_le
    _ = T.card := by simp

lemma exists_sole_acc_edge (n : ℕ) (hn : 1 ≤ n) (x : Node) (hx : x ∈ fullTree n) :
    ∃ e : Edge (Fin n) (Letter n),
      IsEdge (fullBuchi n hn) e ∧ Reachable (fullBuchi n hn) e.1 ∧
        acc (fullBuchi n hn) e = {x} := by
  obtain ⟨hpx, hw⟩ := pos_and_weight_of_mem_fullTree hx
  let T := chain x
  have h30 := fact_30 x x hpx hpx
  have hLast : Last T x := h30.2.1
  have hT_ord : Ordered T := h30.2.2.2.2.1
  have hT_ne : T.Nonempty := ⟨x, hLast.1⟩
  have hT_card : T.card ≤ n := by rw [card_chain_eq x hpx]; omega
  obtain ⟨H, hHtree, hReach⟩ := lemma_39 n hn T hT_ord hT_ne hT_card
  have hSimple : Simple H := simple_of_htree hHtree
  have hnodes : H.val.nodes = T := by
    unfold Htree asHistory at hHtree
    split_ifs at hHtree with hv
    simp only [Option.some.injEq] at hHtree
    rw [← hHtree]; rfl
  have hLeaf : Leaf H.val.nodes x := by
    rw [hnodes]
    exact (h30.2.2.2.2.2.2.2.2 T x hT_ord hLast).1
  have hown_eq : own H.val x = H.val.label x := by
    simp [own, childLabels, hLeaf.2]
  have hcard1 : (H.val.label x).card = 1 := by
    rw [← hown_eq]
    exact hSimple x hLeaf.1
  obtain ⟨s, hs_lbl⟩ := Finset.card_eq_one.mp hcard1
  let π : Fin n → Fin n := Equiv.swap s (lastState n hn)
  have hinj : Set.InjOn π {q | q ∈ stateSet H.val} :=
    (Equiv.swap s (lastState n hn)).injective.injOn
  have hπs : π s = lastState n hn := Equiv.swap_apply_left s (lastState n hn)
  obtain ⟨H', hsucc, -, -, hacc, -⟩ :=
    (lemma_38 n hn H hSimple).2.2.1 x s π hLeaf hs_lbl hinj hπs
  exact ⟨(H, permLetter (stateSet H.val) π, H'), hsucc, hReach, hacc⟩

lemma card_mergedCondition_fullBuchi (n : ℕ) (hn : 1 ≤ n) {I : Type} (Id : Vertex n → I) :
    (mergedCondition (fullBuchi n hn) Id).card = (colourImage Id).card := by
  let F := fullBuchi n hn
  have hact : activeColours F Id = colourImage Id := by
    ext c
    simp only [activeColours, colourImage, Finset.mem_filter, and_iff_left_iff_imp]
    intro hc
    obtain ⟨xV, -, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨e, he_edge, he_reach, he_acc⟩ := exists_sole_acc_edge n hn xV.val xV.property
    refine ⟨e, xV, rfl, he_edge, he_reach, ?_⟩
    rw [he_acc]
    exact Finset.mem_singleton_self xV.val
  have hinj : Set.InjOn (mergedPair F Id) (colourImage Id) := by
    intro c1 hc1 c2 hc2 heq
    simp only [colourImage, Finset.mem_coe] at hc1 hc2
    obtain ⟨xV, -, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨e, he_edge, he_reach, he_acc⟩ := exists_sole_acc_edge n hn xV.val xV.property
    have he1 : e ∈ (mergedPair F Id (Id xV)).1 :=
      ⟨xV, rfl, he_edge, he_reach, by rw [he_acc]; exact Finset.mem_singleton_self xV.val⟩
    have he2 : e ∈ (mergedPair F Id c2).1 := by rw [← heq]; exact he1
    obtain ⟨zV, hzId, -, -, hz_acc⟩ := he2
    rw [he_acc, Finset.mem_singleton] at hz_acc
    have hzx : zV = xV := Subtype.ext hz_acc
    rw [← hzId, hzx]
  unfold mergedCondition
  rw [hact, Finset.card_image_of_injOn hinj]

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

end BuchiRabinIndex.LowerBound.Supplement.Thm29Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
  BuchiRabinIndex.LowerBound.Supplement.Thm29Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (Even n → (reducedCondition (fullBuchi n hn)).card = 3 * 2 ^ (n / 2 - 1) - 1) ∧
    (Odd n → (reducedCondition (fullBuchi n hn)).card = 2 ^ ((n + 1) / 2) - 1) := by
  have hcard : (reducedCondition (fullBuchi n hn)).card = ∑ w ∈ Finset.range n, sf n w := by
    unfold reducedCondition
    rw [Fintype.card_fin, card_mergedCondition_fullBuchi n hn (canonicalColour n),
      card_canonicalColour_image n hn]
  rw [hcard]
  exact sum_sf_closed n hn
