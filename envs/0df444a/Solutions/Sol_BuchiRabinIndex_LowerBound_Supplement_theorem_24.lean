-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.Supplement.theorem_24
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:57:30.17385+00:00
-- url     : https://prove2.me/submissions/f6594e6a-6a38-4055-9f5b-dfefaa6614bb

import Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Merging
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_9
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_lemma_14
import Theorems.Thm_BuchiRabinIndex_LowerBound_Supplement_theorem_19

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement.Thm24Aux
open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
open scoped Classical

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

lemma eventually_mem_infSet {X : Type} [Finite X] (f : ℕ → X) :
    ∃ N : ℕ, ∀ i ≥ N, f i ∈ infSet f := by
  have hft : Fintype X := Fintype.ofFinite X
  have hbad : ∀ x : X, x ∉ infSet f → ∃ Nx : ℕ, ∀ i ≥ Nx, f i ≠ x := by
    intro x hx
    change ¬ (∀ N, ∃ i ≥ N, f i = x) at hx
    push_neg at hx
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

lemma canonicalColour_coexistenceRespecting (n : ℕ) (hn : 1 ≤ n) :
    CoexistenceRespecting (canonicalColour n) := by
  intro x y hadj heq
  have hcid : canonicalId n x.val = canonicalId n y.val := congrArg Subtype.val heq
  have hw : weight x.val = weight y.val := congrArg Prod.fst hcid
  have hcf : cf n x.val = cf n y.val := congrArg Prod.snd hcid
  exact (theorem_19 n hn).1 x.val x.property y.val y.property hadj.1 hw hadj.2 hcf

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
      have hek_edge : IsEdge B (edgeSequence α ρ k) := htr.2 k
      have hek_reach : Reachable B (edgeSequence α ρ k).1 := trace_reachable htr k
      have hek_mp2 : edgeSequence α ρ k ∈ (mergedPair B Id c).2 :=
        ⟨xV, hxId, hek_edge, hek_reach, hx_unst⟩
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
    obtain ⟨e0, he0_fib⟩ := Finite.exists_infinite_fiber (fun s : ↥S_idx => edgeSequence α ρ s.val)
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

end BuchiRabinIndex.LowerBound.Supplement.Thm24Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Supplement
  BuchiRabinIndex.LowerBound.Supplement.Thm24Aux in
theorem solution {Q Sigma : Type} [Fintype Q] [Nonempty Q] [Fintype Sigma]
    (B : NBW Q Sigma) :
    transitionLanguage B (reducedCondition B) = language B :=
  correct_of_coexistenceRespecting B (canonicalColour (Fintype.card Q))
    (canonicalColour_coexistenceRespecting (Fintype.card Q) Fintype.card_pos)
