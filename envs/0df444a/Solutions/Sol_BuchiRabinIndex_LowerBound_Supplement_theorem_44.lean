-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.Supplement.theorem_44
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:18:50.026232+00:00
-- url     : https://prove2.me/submissions/9d798aba-39b2-4640-b02b-131e4a43cc51

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging
import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_31
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_9
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_38
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_39
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_40
import Theorems.Thm_BuchiRabinIndex_LowerBound_theorem_42
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_14
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_19

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace BuchiRabinIndex.LowerBound.Supplement.Thm44Aux
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

lemma nodes_card_le_root {Q : Type} (H : History Q) :
    H.val.nodes.card ≤ (H.val.label []).card := by
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
  calc H.val.nodes.card
      = ∑ _z ∈ H.val.nodes, 1 := by simp
    _ ≤ ∑ z ∈ H.val.nodes, (own H.val z).card := Finset.sum_le_sum hpos
    _ = (H.val.nodes.biUnion (own H.val)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (H.val.label []).card := Finset.card_le_card hbi_sub

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

lemma nodes_card_le {Q : Type} [Fintype Q] (H : History Q) :
    H.val.nodes.card ≤ Fintype.card Q :=
  (nodes_card_le_root H).trans ((Finset.card_le_card (Finset.subset_univ _)).trans Finset.card_univ.le)

lemma mem_mapData_label {Q R : Type} (H : TreeData Q) (π : Q → R) (x : Node) (r : R) :
    r ∈ (mapData H π).label x ↔ ∃ q ∈ H.label x, π q = r :=
  Finset.mem_image

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
  have hlen : ∀ (l : List ℕ), Positive l → l.length ≤ l.sum := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      intro hp; have := ih (fun k hk => hp k (by simp [hk]))
      have := hp a (by simp); simp; omega
  exact mem_boundedWords (n - 1) (n - 1) x
    (fun i hi => ⟨hx i hi, (hsum x i hi).trans hw⟩) ((hlen x hx).trans hw)

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

lemma trace_unique {Q Sigma : Type} {B : NBW Q Sigma} {α : ℕ → Sigma}
    {ρ1 ρ2 : ℕ → History Q} (h1 : IsTrace B α ρ1) (h2 : IsTrace B α ρ2) : ρ1 = ρ2 := by
  funext i
  induction i with
  | zero => exact Option.some.inj (h1.1.symm.trans h2.1)
  | succ i ih =>
    have s1 := h1.2 i
    rw [ih] at s1
    exact Option.some.inj (s1.symm.trans (h2.2 i))

lemma eventually_mem_infSet {X : Type} [Finite X] (f : ℕ → X) :
    ∃ N : ℕ, ∀ i ≥ N, f i ∈ infSet f := by
  have hft : Fintype X := Fintype.ofFinite X
  have hbad : ∀ x : X, x ∉ infSet f → ∃ Nx : ℕ, ∀ i ≥ Nx, f i ≠ x := by
    intro x hx
    change ¬ (∀ N, ∃ i ≥ N, f i = x) at hx
    push Not at hx
    exact hx
  let B : Finset X := (@Finset.univ X hft).filter (fun x => x ∉ infSet f)
  let bound : X → ℕ := fun x => if hx : x ∉ infSet f then Classical.choose (hbad x hx) else 0
  refine ⟨B.sup bound, fun i hi => ?_⟩
  by_contra hni
  have hxB : f i ∈ B := Finset.mem_filter.mpr ⟨@Finset.mem_univ X hft _, hni⟩
  have hle : bound (f i) ≤ B.sup bound := Finset.le_sup hxB
  have hspec := Classical.choose_spec (hbad (f i) hni)
  have hbound_eq : bound (f i) = Classical.choose (hbad (f i) hni) := dif_pos hni
  exact hspec i (by omega) rfl

lemma readWord_append_singleton {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ (v : List Sigma) (o : Option (History Q)) (σ : Sigma),
      readWord B o (v ++ [σ]) = (readWord B o v).bind (fun h => successor B h σ)
  | [], o, σ => by simp [readWord]
  | a :: v, o, σ => by
    simp only [List.cons_append, readWord]
    exact readWord_append_singleton B v (o.bind fun h => successor B h a) σ

lemma trace_reachable {Q Sigma : Type} {B : NBW Q Sigma} {α : ℕ → Sigma}
    {ρ : ℕ → History Q} (htr : IsTrace B α ρ) : ∀ k : ℕ, Reachable B (ρ k)
  | 0 => ⟨[], by simpa [readWord] using htr.1⟩
  | k + 1 => by
    obtain ⟨v, hv⟩ := trace_reachable htr k
    refine ⟨v ++ [α k], ?_⟩
    rw [readWord_append_singleton, hv]
    simpa using htr.2 k

lemma mem_succ_of_not_unstable {Q Sigma : Type} {B : NBW Q Sigma}
    {H H' : History Q} {σ : Sigma} {x : Node}
    (hx : x ∈ H.val.nodes) (hst : x ∉ unstable B H σ)
    (hs : successor B H σ = some H') : x ∈ H'.val.nodes := by
  unfold unstable at hst
  simp only [Finset.mem_filter, hx, true_and, not_or, not_not] at hst
  unfold successor asHistory at hs
  split_ifs at hs with hv
  simp only [Option.some.injEq] at hs
  subst hs
  simp only [compressed, Finset.mem_image]
  exact ⟨x, hst.1, hst.2⟩

lemma persist_from {Q Sigma : Type} {B : NBW Q Sigma} {α : ℕ → Sigma}
    {ρ : ℕ → History Q} (htr : IsTrace B α ρ) {x : Node} {k0 : ℕ}
    (hx0 : x ∈ (ρ k0).val.nodes) (hstab : ∀ k ≥ k0, x ∉ unstable B (ρ k) (α k)) :
    ∀ k ≥ k0, x ∈ (ρ k).val.nodes := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => simpa using hx0
  | succ d ih =>
    have hle : k0 ≤ k0 + d := Nat.le_add_right k0 d
    exact mem_succ_of_not_unstable (ih hle) (hstab (k0 + d) hle) (htr.2 (k0 + d))

lemma correct_of_coexistenceRespecting {Q Sigma I : Type}
    [Fintype Q] [Nonempty Q] [Fintype Sigma]
    (B : NBW Q Sigma) (Id : Vertex (Fintype.card Q) → I)
    (hresp : CoexistenceRespecting Id) :
    transitionLanguage B (mergedCondition B Id) = language B := by
  haveI hfinH : Finite (History Q) := history_finite
  haveI hfinE : Finite (Edge Q Sigma) := inferInstance
  let n := Fintype.card Q
  have hn : 1 ≤ n := Fintype.card_pos
  ext α
  constructor
  · rintro ⟨ρ, htr, p, hp_mem, hp_acc⟩
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp_mem
    obtain ⟨⟨e0, he0_inf, ⟨xV, hxId, he0_orig⟩⟩, hdisj⟩ := hp_acc
    have hx_nodes : xV.val ∈ e0.1.val.nodes := (Finset.mem_filter.mp he0_orig.2.2).1
    have hpx : Positive xV.val := e0.1.property.1.1 xV.val hx_nodes
    rw [lemma_9 B α]
    obtain ⟨N0, hN0⟩ := eventually_mem_infSet (edgeSequence α ρ)
    refine ⟨ρ, xV.val, hpx, htr, ⟨N0, ?_⟩, ?_⟩
    · intro k hk hx_unst
      have hek_inf : edgeSequence α ρ k ∈ infSet (edgeSequence α ρ) := hN0 k hk
      have hek_mp2 : edgeSequence α ρ k ∈ (mergedPair B Id c).2 :=
        ⟨xV, hxId, htr.2 k, trace_reachable htr k, hx_unst⟩
      exact Set.eq_empty_iff_forall_notMem.mp hdisj (edgeSequence α ρ k) ⟨hek_inf, hek_mp2⟩
    · intro N
      obtain ⟨k, hkN, hke0⟩ := he0_inf N
      have hacc_eq : acceptingNodes B (ρ k) (α k) = acc B (edgeSequence α ρ k) := rfl
      refine ⟨k, hkN, ?_⟩
      rw [hacc_eq, hke0]
      exact he0_orig.2.2
  · intro hlang
    obtain ⟨ρ, x, _, htr, ⟨N1, hstab⟩, hacc_inf⟩ := (lemma_9 B α).mp hlang
    let S_idx : Set ℕ := {k : ℕ | N1 ≤ k ∧ x ∈ acceptingNodes B (ρ k) (α k)}
    have hinf_idx : S_idx.Infinite := by
      rw [Set.infinite_iff_exists_gt]
      intro a
      obtain ⟨k, hk, hx_acc⟩ := hacc_inf (max N1 (a + 1))
      exact ⟨k, ⟨le_trans (le_max_left _ _) hk, hx_acc⟩, by omega⟩
    haveI hinf_S : Infinite ↥S_idx := Set.infinite_coe_iff.mpr hinf_idx
    obtain ⟨e0, he0_fib⟩ :=
      Finite.exists_infinite_fiber (fun s : ↥S_idx => edgeSequence α ρ s.val)
    have he0_set : ((fun s : ↥S_idx => edgeSequence α ρ s.val) ⁻¹' {e0}).Infinite :=
      Set.infinite_coe_iff.mp he0_fib
    obtain ⟨s0, hs0⟩ := he0_set.nonempty
    have hs0_eq : edgeSequence α ρ s0.val = e0 := hs0
    have hk0_ge : N1 ≤ s0.val := s0.property.1
    have hx_acc0 : x ∈ acceptingNodes B (ρ s0.val) (α s0.val) := s0.property.2
    have hx_nodes0 : x ∈ (ρ s0.val).val.nodes := (Finset.mem_filter.mp hx_acc0).1
    have hx_ft : x ∈ fullTree n := nodes_sub_fullTree (ρ s0.val) hx_nodes0
    let xV : Vertex n := ⟨x, hx_ft⟩
    let c := Id xV
    have he0_inf : e0 ∈ infSet (edgeSequence α ρ) := by
      intro N
      have hfin : ({s : ↥S_idx | s.val < N} : Set ↥S_idx).Finite := by
        refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
        exact (Set.finite_lt_nat N).subset (by rintro _ ⟨s, hs, rfl⟩; exact hs)
      obtain ⟨s, hs_mem, hs_not_lt⟩ := (he0_set.sdiff hfin).nonempty
      exact ⟨s.val, Nat.le_of_not_lt hs_not_lt, hs_mem⟩
    have he0_orig1 : e0 ∈ (originalPair B x).1 := by
      rw [← hs0_eq]
      exact ⟨htr.2 s0.val, trace_reachable htr s0.val, hx_acc0⟩
    have he0_mp1 : e0 ∈ (mergedPair B Id c).1 := ⟨xV, rfl, he0_orig1⟩
    have hc_act : c ∈ activeColours B Id :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨xV, Finset.mem_univ _, rfl⟩, ⟨e0, he0_mp1⟩⟩
    have hpers : ∀ k ≥ s0.val, x ∈ (ρ k).val.nodes :=
      persist_from htr hx_nodes0 (fun k hk => hstab k (le_trans hk0_ge hk))
    refine ⟨ρ, htr, mergedPair B Id c, Finset.mem_image.mpr ⟨c, hc_act, rfl⟩,
      ⟨⟨e0, he0_inf, he0_mp1⟩, ?_⟩⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e1 ⟨he1_inf, ⟨yV, hyId, he1_orig2⟩⟩
    obtain ⟨k1, hk1, hke1⟩ := he1_inf (max N1 s0.val)
    have hk1_N1 : N1 ≤ k1 := le_trans (le_max_left _ _) hk1
    have hk1_s0 : s0.val ≤ k1 := le_trans (le_max_right _ _) hk1
    have hy_unst : yV.val ∈ unstable B (ρ k1) (α k1) := by
      have hunst_eq : unstable B (ρ k1) (α k1) = unst B (edgeSequence α ρ k1) := rfl
      rw [hunst_eq, hke1]
      exact he1_orig2.2.2
    by_cases hxy : yV = xV
    · subst hxy
      exact hstab k1 hk1_N1 hy_unst
    · have hne_val : xV.val ≠ yV.val := fun h => hxy (Subtype.ext h.symm)
      have hx_k1 : xV.val ∈ (ρ k1).val.nodes := hpers k1 hk1_s0
      have hy_k1 : yV.val ∈ (ρ k1).val.nodes := (Finset.mem_filter.mp hy_unst).1
      have hcoex : ∃ T : Finset Node, Ordered T ∧ T.card ≤ n ∧ xV.val ∈ T ∧ yV.val ∈ T :=
        ⟨(ρ k1).val.nodes, (ρ k1).property.1, nodes_card_le (ρ k1), hx_k1, hy_k1⟩
      have hchain_le : (chain xV.val ∪ chain yV.val).card ≤ n :=
        (lemma_14 n hn xV.val yV.val xV.property yV.property hne_val).mp hcoex
      have hadj : (graph n).Adj xV yV := ⟨hne_val, hchain_le⟩
      exact hresp xV yV hadj hyId.symm

lemma correct_of_coexistenceRespecting_card {n : ℕ}
    {Q Sigma I : Type} [Fintype Q] [Nonempty Q] [Fintype Sigma]
    (hcard : Fintype.card Q = n) (B : NBW Q Sigma) (Id : Vertex n → I)
    (hresp : CoexistenceRespecting Id) :
    CorrectTransition B (mergedCondition B Id) := by
  subst hcard
  exact correct_of_coexistenceRespecting B Id hresp

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

lemma not_preLt_self (u : Node) : ¬ PreLt u u := by
  rintro (⟨_, hne⟩ | ⟨p, i, j, a, b, h1, h2, hij⟩)
  · exact hne rfl
  · have heq : i :: a = j :: b := List.append_cancel_left (h1.symm.trans h2)
    have hij_eq : i = j := (List.cons.inj heq).1
    omega

lemma rank_lt_card {T : Finset Node} {y : Node} (hy : y ∈ T) : rank T y < T.card := by
  have hsub : T.filter (PreLt · y) ⊆ T.erase y := by
    intro z hz
    obtain ⟨hzT, hlt⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_erase.mpr ⟨fun hzy => not_preLt_self y (hzy ▸ hlt), hzT⟩
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨y, hy⟩
  have hle : (T.filter (PreLt · y)).card ≤ (T.erase y).card := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hy] at hle
  unfold rank
  omega

lemma stateSet_canonical {n : ℕ} {T : Finset Node} {H : History (Fin n)}
    (hH : Htree n T = some H) (hcard : T.card ≤ n) :
    stateSet H.val = canonicalStates n T := by
  unfold Htree asHistory at hH
  split_ifs at hH with hv
  simp only [Option.some.injEq] at hH
  have hval : H.val = canonicalData n T := by rw [← hH]
  have hnodes : H.val.nodes = T := by rw [hval]; rfl
  have hsub : stateSet H.val ⊆ canonicalStates n T := by
    intro q hq
    unfold stateSet at hq
    rw [hval] at hq
    unfold canonicalData at hq
    dsimp only at hq
    split_ifs at hq with hnil
    · obtain ⟨_, y, hyT, _, hqr⟩ := Finset.mem_filter.mp hq
      have hlt : rank T y < T.card := rank_lt_card hyT
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    · simp at hq
  have hcs_card : (canonicalStates n T).card = T.card := by
    rw [← Finset.card_fin T.card]
    symm
    refine Finset.card_bij (fun (i : Fin T.card) _ => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hcard⟩ : Fin n)) ?_ ?_ ?_
    · intro i _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
    · intro i1 _ i2 _ heq
      exact Fin.ext (congrArg (Fin.val : Fin n → ℕ) heq)
    · intro q hq
      have hlt : q.val < T.card := (Finset.mem_filter.mp hq).2
      exact ⟨⟨q.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have hss_ge : T.card ≤ (stateSet H.val).card := by
    have hle := nodes_card_le_root H
    rwa [hnodes] at hle
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

lemma acc_acycle_sub_singleton (n : ℕ) (hn : 1 ≤ n) (x : Node) (hx : x ∈ fullTree n) :
    ∀ e ∈ Acycle n hn x, ∀ z ∈ acc (fullBuchi n hn) e, z = x := by
  let F := fullBuchi n hn
  obtain ⟨hpx, hw⟩ := pos_and_weight_of_mem_fullTree hx
  let T := chain x
  let P := canonicalStates n T
  let s := stateAt n hn (T.card - 1)
  have h30 := fact_30 x x hpx hpx
  have hLast : Last T x := h30.2.1
  have hT_ord : Ordered T := h30.2.2.2.2.1
  have hT_ne : T.Nonempty := ⟨x, hLast.1⟩
  have hT_card_eq : T.card = weight x + 1 := card_chain_eq x hpx
  have hT_card : T.card ≤ n := by omega
  obtain ⟨H, hHtree, _⟩ := lemma_39 n hn T hT_ord hT_ne hT_card
  have hSimple : Simple H := simple_of_htree hHtree
  have hP_eq : stateSet H.val = P := stateSet_canonical hHtree hT_card
  have hval : H.val = canonicalData n T := by
    unfold Htree asHistory at hHtree
    split_ifs at hHtree with hv
    simp only [Option.some.injEq] at hHtree
    rw [← hHtree]
  have hnodes : H.val.nodes = T := by rw [hval]; rfl
  have hLeafT : Leaf T x := (h30.2.2.2.2.2.2.2.2 T x hT_ord hLast).1
  have hLeafH : Leaf H.val.nodes x := by rwa [hnodes]
  have hrank_x : rank T x = T.card - 1 := by
    have hfilt : T.filter (PreLt · x) = T.erase x := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hyT, hlt⟩
        exact ⟨fun hyx => not_preLt_self x (hyx ▸ hlt), hyT⟩
      · rintro ⟨hne, hyT⟩
        exact ⟨hyT, (hLast.2 y hyT).resolve_left hne⟩
    unfold rank
    rw [hfilt, Finset.card_erase_of_mem hLast.1]
  have hs_val : s.val = T.card - 1 := Nat.mod_eq_of_lt (by omega)
  have hs_lbl : H.val.label x = {s} := by
    rw [hval]
    ext q
    simp only [canonicalData, if_pos hLast.1, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨y, hyT, hpref, hqr⟩
      obtain ⟨w, rfl⟩ := hpref
      cases w with
      | nil =>
        apply Fin.ext
        rw [List.append_nil] at hqr
        omega
      | cons i rest =>
        have hxi : x ++ [i] ∈ T := hT_ord.2.1 _ hyT (x ++ [i]) ⟨rest, by simp⟩
        have hch : x ++ [i] ∈ children T x := by simp [children, hxi]
        rw [hLeafT.2] at hch
        simp at hch
    · rintro rfl
      exact ⟨x, hLast.1, List.prefix_refl x, hs_val.trans hrank_x.symm⟩
  intro e he z hz
  unfold Acycle acceptingWord at he
  rw [hHtree] at he
  dsimp only at he
  by_cases hlt : T.card < n
  · rw [if_pos hlt] at he
    let π0 : Fin n → Fin n := fun q => if q = s then lastState n hn else q
    let π1 : Fin n → Fin n := fun q => if q = lastState n hn then s else q
    have hsP : s ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hlast_not_P : lastState n hn ∉ P := by
      simp only [P, canonicalStates, lastState, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hacc_perm : accLetter hn P s = permLetter (stateSet H.val) π0 := by
      rw [hP_eq]
      ext ⟨a, b⟩
      simp only [accLetter, idLetter, permLetter, π0, Finset.mem_insert, Finset.mem_image,
        Finset.mem_erase, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨q, ⟨hqne, hqP⟩, rfl, rfl⟩)
        · exact ⟨s, hsP, rfl, if_pos rfl⟩
        · exact ⟨q, hqP, rfl, if_neg hqne⟩
      · rintro ⟨q, hqP, rfl, rfl⟩
        by_cases hqs : q = s
        · subst hqs; left; exact ⟨rfl, if_pos rfl⟩
        · right; exact ⟨q, ⟨hqs, hqP⟩, rfl, (if_neg hqs).symm⟩
    have hinj0 : Set.InjOn π0 {q | q ∈ stateSet H.val} := by
      rw [hP_eq]
      intro q1 hq1 q2 hq2 heq
      dsimp only [π0] at heq
      split_ifs at heq with h1 h2
      · exact h1.trans h2.symm
      · exfalso; exact hlast_not_P (heq ▸ hq2)
      · exfalso; exact hlast_not_P (heq.symm ▸ hq1)
      · exact heq
    obtain ⟨H1, hsucc0, hH1val, hSimple1, hacc0, _⟩ :=
      (lemma_38 n hn H hSimple).2.2.1 x s π0 hLeafH hs_lbl hinj0 (if_pos rfl)
    rw [← hacc_perm] at hsucc0 hacc0
    have hss1 : stateSet H1.val = insert (lastState n hn) (P.erase s) := by
      ext q
      have hmem_ss1 : q ∈ stateSet H1.val ↔ ∃ q' ∈ P, π0 q' = q := by
        unfold stateSet
        rw [hH1val, mem_mapData_label]
        change (∃ a ∈ stateSet H.val, π0 a = q) ↔ _
        rw [hP_eq]
      rw [hmem_ss1]
      simp only [π0, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨q', hq'P, rfl⟩
        by_cases hqs : q' = s
        · subst hqs; left; exact if_pos rfl
        · right; rw [if_neg hqs]; exact ⟨hqs, hq'P⟩
      · rintro (rfl | ⟨hqne, hqP⟩)
        · exact ⟨s, hsP, if_pos rfl⟩
        · exact ⟨q, hqP, if_neg hqne⟩
    have hinj1 : Set.InjOn π1 {q | q ∈ stateSet H1.val} := by
      rw [hss1]
      intro q1 hq1 q2 hq2 heq
      change q1 ∈ insert (lastState n hn) (P.erase s) at hq1
      change q2 ∈ insert (lastState n hn) (P.erase s) at hq2
      simp only [Finset.mem_insert, Finset.mem_erase] at hq1 hq2
      dsimp only [π1] at heq
      split_ifs at heq with h1 h2
      · exact h1.trans h2.symm
      · rcases hq2 with h2' | ⟨h2ne, _⟩
        · exact absurd h2' h2
        · exfalso; exact h2ne heq.symm
      · rcases hq1 with h1' | ⟨h1ne, _⟩
        · exact absurd h1' h1
        · exfalso; exact h1ne heq
      · exact heq
    have hne_last1 : ∀ q ∈ stateSet H1.val, π1 q ≠ lastState n hn := by
      rw [hss1]
      intro q _
      simp only [π1]
      split_ifs with hql
      · intro hsl; exact hlast_not_P (hsl ▸ hsP)
      · exact hql
    obtain ⟨_, _, _, _, hacc1, _⟩ :=
      (lemma_38 n hn H1 hSimple1).2.1 π1 hinj1 hne_last1
    rw [hss1] at hacc1
    obtain ⟨i, hread, he21, _⟩ := he
    have hi_cases : i.val = 0 ∨ i.val = 1 := by
      have hi_lt : i.val < 2 := i.isLt
      omega
    rcases hi_cases with hi0 | hi1
    · simp only [hi0, List.take, readWord, Option.some.injEq] at hread
      have hi_fin : i = ⟨0, by simp⟩ := Fin.ext hi0
      have he21' : e.2.1 = accLetter hn P s := by
        rw [he21, hi_fin]; rfl
      have hacc_e : acc F e = acceptingNodes F H (accLetter hn P s) := by
        unfold acc; rw [← hread, he21']
      rw [hacc_e, hacc0, Finset.mem_singleton] at hz
      exact hz
    · simp only [hi1, List.take, readWord, Option.bind_some] at hread
      change successor F H (accLetter hn P s) = some e.1 at hread
      rw [hsucc0] at hread
      have he1_eq : H1 = e.1 := Option.some.inj hread
      have hi_fin : i = ⟨1, by simp⟩ := Fin.ext hi1
      have he21' : e.2.1 = permLetter (insert (lastState n hn) (P.erase s)) π1 := by
        rw [he21, hi_fin]; rfl
      have hacc_e : acc F e =
          acceptingNodes F H1 (permLetter (insert (lastState n hn) (P.erase s)) π1) := by
        unfold acc; rw [← he1_eq, he21']
      rw [hacc_e, hacc1] at hz
      simp at hz
  · rw [if_neg hlt] at he
    have hT_eq_n : T.card = n := by omega
    have hs_last : s = lastState n hn := by
      apply Fin.ext
      simp only [lastState, hs_val, hT_eq_n]
    have hid_perm : idLetter P = permLetter (stateSet H.val) id := by
      rw [hP_eq]; rfl
    have hinj_id : Set.InjOn (id : Fin n → Fin n) {q | q ∈ stateSet H.val} :=
      Function.injective_id.injOn
    obtain ⟨_, _, _, _, hacc0, _⟩ :=
      (lemma_38 n hn H hSimple).2.2.1 x s id hLeafH hs_lbl hinj_id hs_last
    rw [← hid_perm] at hacc0
    obtain ⟨i, hread, he21, _⟩ := he
    have hi0 : i.val = 0 := by
      have hi_lt : i.val < 1 := i.isLt
      omega
    simp only [hi0, List.take, readWord, Option.some.injEq] at hread
    have hi_fin : i = ⟨0, by simp⟩ := Fin.ext hi0
    have he21' : e.2.1 = idLetter P := by
      rw [he21, hi_fin]; rfl
    have hacc_e : acc F e = acceptingNodes F H (idLetter P) := by
      unfold acc; rw [← hread, he21']
    rw [hacc_e, hacc0, Finset.mem_singleton] at hz
    exact hz

lemma incorrect_of_adj_not_chain (n : ℕ) (hn : 1 ≤ n) {I : Type} (Id : Vertex n → I)
    (xV yV : Vertex n) (hadj : (graph n).Adj xV yV) (hy_not_cx : yV.val ∉ chain xV.val)
    (hId_eq : Id xV = Id yV) :
    transitionLanguage (fullBuchi n hn) (mergedCondition (fullBuchi n hn) Id) ≠
      language (fullBuchi n hn) := by
  intro heq_lang
  let F := fullBuchi n hn
  let x := xV.val
  let y := yV.val
  let S : Finset Node := {x, y}
  have hxy_ne : x ≠ y := hadj.1
  have hS : S ⊆ fullTree n := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact xV.property
    · rw [Finset.mem_singleton.mp hu]; exact yV.property
  have hclique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Adj n a b := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha <;>
      rcases Finset.mem_insert.mp hb with rfl | hb
    · exact absurd rfl hab
    · rw [Finset.mem_singleton.mp hb]; exact hadj
    · rw [Finset.mem_singleton.mp ha]; exact hadj.symm
    · rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb] at hab
      exact absurd rfl hab
  have hxS : x ∈ S := Finset.mem_insert_self x {y}
  have hyS : y ∈ S := Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  have h40 := lemma_40 n hn S hS hclique x hxS
  have h40_y := h40.1 y hyS hxy_ne hy_not_cx
  obtain ⟨e_y, hey_wxy, hy_unst⟩ := h40_y.2.2.1
  have hwxy_acc := h40_y.2.2.2.1
  have hAccC : AcceptingCycle F (Ccycle n hn S x) := h40.2.2
  have hErase : S.erase x = {y} := by
    ext u
    simp only [S, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun ⟨hne, h⟩ => h.resolve_left hne, fun h => ⟨h ▸ hxy_ne.symm, Or.inr h⟩⟩
  have hWx_eq : Wx n hn S x = Wxy n hn x y := by
    unfold Wx
    rw [hErase]
    simp
  have hC_sub : Ccycle n hn S x = Wxy n hn x y ∪ Acycle n hn x := by
    unfold Ccycle
    rw [hWx_eq]
  obtain ⟨α, ρ, htr, hinf⟩ := ((fact_31 n hn).1 (Ccycle n hn S x)).mp hAccC.1
  have hlang : α ∈ language F := hAccC.2 α ρ htr hinf
  rw [← heq_lang] at hlang
  obtain ⟨ρ', htr', p, hp_mem, hp_acc⟩ := hlang
  have hρ : ρ' = ρ := trace_unique htr' htr
  rw [hρ, hinf] at hp_acc
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp_mem
  obtain ⟨⟨e_a, hea_C, ⟨zV, hzId, _, _, hz_acc⟩⟩, hdisj⟩ := hp_acc
  have hzx : zV.val = x := by
    rw [hC_sub] at hea_C
    rcases hea_C with hea_w | hea_a
    · exact hwxy_acc e_a hea_w zV.val hz_acc
    · exact acc_acycle_sub_singleton n hn x xV.property e_a hea_a zV.val hz_acc
  have hc_eq : c = Id yV := by
    have hzV_eq : zV = xV := Subtype.ext hzx
    rw [← hzId, hzV_eq, hId_eq]
  have hey_C : e_y ∈ Ccycle n hn S x := by
    rw [hC_sub]; exact Or.inl hey_wxy
  have hey_inf : e_y ∈ infSet (edgeSequence α ρ) := hinf.symm ▸ hey_C
  obtain ⟨k, _, hke⟩ := hey_inf 0
  have hey_edge : IsEdge F e_y := hke ▸ htr.2 k
  have hey_reach : Reachable F e_y.1 := hke ▸ trace_reachable htr k
  have hey_mp2 : e_y ∈ (mergedPair F Id c).2 :=
    ⟨yV, hc_eq.symm, hey_edge, hey_reach, hy_unst⟩
  exact Set.eq_empty_iff_forall_notMem.mp hdisj e_y ⟨hey_C, hey_mp2⟩

lemma incorrect_of_not_coexistenceRespecting (n : ℕ) (hn : 1 ≤ n) {I : Type}
    (Id : Vertex n → I) (hnot : ¬ CoexistenceRespecting Id) :
    transitionLanguage (fullBuchi n hn) (mergedCondition (fullBuchi n hn) Id) ≠
      language (fullBuchi n hn) := by
  unfold CoexistenceRespecting at hnot
  push Not at hnot
  obtain ⟨xV, yV, hadj, hId_eq⟩ := hnot
  have hpx : Positive xV.val := (pos_and_weight_of_mem_fullTree xV.property).1
  have hpy : Positive yV.val := (pos_and_weight_of_mem_fullTree yV.property).1
  by_cases hy_cx : yV.val ∈ chain xV.val
  · have hx_not_cy : xV.val ∉ chain yV.val := fun hx_cy =>
      hadj.1 ((fact_30 xV.val yV.val hpx hpy).2.2.2.1 hx_cy hy_cx)
    exact incorrect_of_adj_not_chain n hn Id yV xV hadj.symm hx_not_cy hId_eq.symm
  · exact incorrect_of_adj_not_chain n hn Id xV yV hadj hy_cx hId_eq

lemma canonicalColour_coexistenceRespecting (n : ℕ) (hn : 1 ≤ n) :
    CoexistenceRespecting (canonicalColour n) := by
  intro x y hadj heq
  have hcid : canonicalId n x.val = canonicalId n y.val := congrArg Subtype.val heq
  have hw : weight x.val = weight y.val := congrArg Prod.fst hcid
  have hcf : cf n x.val = cf n y.val := congrArg Prod.snd hcid
  exact (theorem_19 n hn).1 x.val x.property y.val y.property hadj.1 hw hadj.2 hcf

lemma identifiers_card_eq_sum_sf (n : ℕ) (hn : 1 ≤ n) :
    (identifiers n).card = ∑ w ∈ Finset.range n, sf n w := by
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

lemma chi_le_of_colorable {n m : ℕ} (hcol : (graph n).Colorable m) : chi n ≤ m := by
  have hle : (graph n).chromaticNumber ≤ (m : ℕ∞) :=
    (graph n).chromaticNumber_le_iff_colorable.mpr hcol
  have hne : (graph n).chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top m) hle
  have hcoe : ((chi n : ℕ) : ℕ∞) = (graph n).chromaticNumber := ENat.natCast_toNat hne
  exact ENat.natCast_le_natCast.mp (hcoe.trans_le hle)

lemma colorable_of_coexistenceRespecting {n : ℕ} {I : Type} (Id : Vertex n → I)
    (hresp : CoexistenceRespecting Id) :
    (graph n).Colorable ((colourImage Id).card) := by
  let Img := colourImage Id
  let e : ↥Img ≃ Fin Img.card :=
    (Fintype.equivFin ↥Img).trans (finCongr (Fintype.card_coe Img))
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => e ⟨Id v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩) ?_⟩
  intro u v hadj heq
  exact hresp u v hadj (congrArg Subtype.val (e.injective heq))

lemma activeColours_card_le {Q Sigma I : Type} {n : ℕ} (B : NBW Q Sigma)
    (Id : Vertex n → I) : (activeColours B Id).card ≤ (colourImage Id).card := by
  unfold activeColours colourImage
  exact Finset.card_filter_le _ _

end BuchiRabinIndex.LowerBound.Supplement.Thm44Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
  BuchiRabinIndex.LowerBound.Supplement.Thm44Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ (I : Type) [Fintype I] (Id : Vertex n → I),
      (CoexistenceRespecting Id → UniversallyCorrect Id) ∧
      (¬ CoexistenceRespecting Id →
        transitionLanguage (fullBuchi n hn) (mergedCondition (fullBuchi n hn) Id) ≠
          language (fullBuchi n hn))) ∧
    IsLeast (uniformIndices n hn) (chi n) ∧
    IsLeast (fullIndices n hn) (chi n) ∧
    omega n ≤ chi n ∧ chi n ≤ ∑ w ∈ Finset.range n, sf n w := by
  have hpart1 : ∀ (I : Type) [Fintype I] (Id : Vertex n → I),
      (CoexistenceRespecting Id → UniversallyCorrect Id) ∧
      (¬ CoexistenceRespecting Id →
        transitionLanguage (fullBuchi n hn) (mergedCondition (fullBuchi n hn) Id) ≠
          language (fullBuchi n hn)) := by
    intro I _ Id
    refine ⟨?_, incorrect_of_not_coexistenceRespecting n hn Id⟩
    intro hresp Q Sigma _ _ _ hcard B
    exact correct_of_coexistenceRespecting_card hcard B Id hresp
  have hne_top : (graph n).chromaticNumber ≠ ⊤ :=
    (graph n).chromaticNumber_ne_top_iff_exists.mpr
      ⟨Fintype.card (Vertex n), (graph n).colorable_of_fintype⟩
  have hchi_col : (graph n).Colorable (chi n) :=
    SimpleGraph.colorable_of_chromaticNumber_ne_top hne_top
  obtain ⟨C⟩ := hchi_col
  let Id0 : Vertex n → Fin (chi n) := C
  have hresp0 : CoexistenceRespecting Id0 := fun x y hadj => C.valid hadj
  have himg0_le : (colourImage Id0).card ≤ chi n := by
    calc (colourImage Id0).card
        ≤ (Finset.univ : Finset (Fin (chi n))).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = chi n := Finset.card_fin (chi n)
  have himg0_ge : chi n ≤ (colourImage Id0).card :=
    chi_le_of_colorable (colorable_of_coexistenceRespecting Id0 hresp0)
  have himg0_eq : (colourImage Id0).card = chi n :=
    le_antisymm himg0_le himg0_ge
  have huniv0 : UniversallyCorrect Id0 := (hpart1 (Fin (chi n)) Id0).1 hresp0
  have hchi_mem_unif : chi n ∈ uniformIndices n hn := by
    refine ⟨chi n, Id0, huniv0, ?_, ?_⟩
    · intro Q Sigma _ _ _ _ B
      calc (mergedCondition B Id0).card
          ≤ (activeColours B Id0).card := Finset.card_image_le
        _ ≤ (colourImage Id0).card := activeColours_card_le B Id0
        _ = chi n := himg0_eq
    · rw [card_mergedCondition_fullBuchi n hn Id0, himg0_eq]
  have hunif_sub_full : uniformIndices n hn ⊆ fullIndices n hn := by
    rintro m ⟨k, Id, huniv, _, hcardF⟩
    haveI hneFin : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact ⟨k, Id, huniv (Fin n) (Letter n) (Fintype.card_fin n) (fullBuchi n hn), hcardF⟩
  have hchi_mem_full : chi n ∈ fullIndices n hn := hunif_sub_full hchi_mem_unif
  have hlb_full : ∀ m ∈ fullIndices n hn, chi n ≤ m := by
    rintro m ⟨k, Id, hcorrF, hcard_m⟩
    have hresp : CoexistenceRespecting Id := by
      by_contra hnot
      exact (hpart1 (Fin k) Id).2 hnot hcorrF
    have hcol : (graph n).Colorable ((colourImage Id).card) :=
      colorable_of_coexistenceRespecting Id hresp
    have hle := chi_le_of_colorable hcol
    rwa [← card_mergedCondition_fullBuchi n hn Id, hcard_m] at hle
  have hlb_unif : ∀ m ∈ uniformIndices n hn, chi n ≤ m :=
    fun m hm => hlb_full m (hunif_sub_full hm)
  have homega_le_chi : omega n ≤ chi n := by
    obtain ⟨k, Id, hcorrF, hcard_chi⟩ := hchi_mem_full
    have hle := ((theorem_42 n hn).1 (mergedCondition (fullBuchi n hn) Id) hcorrF).1
    rwa [hcard_chi] at hle
  have hchi_le_sum : chi n ≤ ∑ w ∈ Finset.range n, sf n w := by
    have hresp_can := canonicalColour_coexistenceRespecting n hn
    have hcol_can := colorable_of_coexistenceRespecting (canonicalColour n) hresp_can
    have hle := chi_le_of_colorable hcol_can
    have himg_can : (colourImage (canonicalColour n)).card = (identifiers n).card := by
      have himg_univ : colourImage (canonicalColour n) = Finset.univ := by
        ext u
        simp only [colourImage, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
        obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp u.property
        exact ⟨⟨x, hx⟩, Subtype.ext hxu⟩
      rw [himg_univ, Finset.card_univ, Fintype.card_coe]
    rw [himg_can, identifiers_card_eq_sum_sf n hn] at hle
    exact hle
  exact ⟨hpart1, ⟨hchi_mem_unif, hlb_unif⟩, ⟨hchi_mem_full, hlb_full⟩, homega_le_chi, hchi_le_sum⟩
