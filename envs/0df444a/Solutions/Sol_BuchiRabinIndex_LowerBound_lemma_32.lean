-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:43:40.680731+00:00
-- url     : https://prove2.me/submissions/ee6f1016-155d-4f9c-81b8-db02c0ac9740

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_31
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_9

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma32Aux
open BuchiRabinIndex.LowerBound
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

lemma history_finite {Q : Type} [Fintype Q] : Finite (History Q) := by
  by_cases hQ : Fintype.card Q = 0
  · have hisEmpty : IsEmpty (History Q) := ⟨fun H => by
      have hc := nodes_card_le H
      have hne : H.val.nodes.Nonempty := ⟨[], H.property.2.1⟩
      have := Finset.card_pos.mpr hne
      omega⟩
    exact @Finite.of_fintype (History Q) (@Fintype.ofIsEmpty _ hisEmpty)
  · have hk : 1 ≤ Fintype.card Q := Nat.pos_of_ne_zero hQ
    let k := Fintype.card Q
    have hsub : ∀ H : History Q, H.val.nodes ∈ (fullTree k).powerset := by
      intro H
      rw [Finset.mem_powerset]
      intro x hx
      have hpx : Positive x := H.property.1.1 x hx
      have hch_sub : chain x ⊆ H.val.nodes :=
        (fact_30 x x hpx hpx).2.2.2.2.2.1 H.val.nodes H.property.1 hx
      have hcard : (chain x).card ≤ k :=
        (Finset.card_le_card hch_sub).trans (nodes_card_le H)
      rw [card_chain_eq x hpx] at hcard
      exact mem_fullTree_of_pos_weight hk hpx (by omega)
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
      · have hxf : x ∈ fullTree k := Finset.mem_powerset.mp (hsub H1) hx
        exact hlbl_on ⟨x, hxf⟩
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

end BuchiRabinIndex.LowerBound.Lemma32Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma32Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (D : Set (Edge (Fin n) (Letter n)))
    (hD : Cycle (fullBuchi n hn) D) :
    AcceptingCycle (fullBuchi n hn) D ↔
    ∃ x : Node, Positive x ∧
      (∀ e ∈ D, x ∉ unst (fullBuchi n hn) e) ∧
      (∃ e ∈ D, x ∈ acc (fullBuchi n hn) e) := by
  let F := fullBuchi n hn
  haveI hfinH : Finite (History (Fin n)) := history_finite
  haveI hfinE : Finite (Edge (Fin n) (Letter n)) := inferInstance
  haveI hneF : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  constructor
  · intro hAcc
    obtain ⟨α, ρ, htr, hinf⟩ := ((fact_31 n hn).1 D).mp hD
    have hlang : α ∈ language F := hAcc.2 α ρ htr hinf
    obtain ⟨ρ', x, hxpos, htr', ⟨N1, hstab⟩, hacc_inf⟩ := (lemma_9 F α).mp hlang
    have hρ : ρ' = ρ := trace_unique htr' htr
    rw [hρ] at hstab hacc_inf
    obtain ⟨N0, hN0⟩ := eventually_mem_infSet (edgeSequence α ρ)
    refine ⟨x, hxpos, ?_, ?_⟩
    · intro e heD
      rw [← hinf] at heD
      obtain ⟨i, hiN, hie⟩ := heD N1
      have hunst_eq : unst F (edgeSequence α ρ i) = unstable F (ρ i) (α i) := rfl
      rw [← hie, hunst_eq]
      exact hstab i hiN
    · obtain ⟨i, hiN, hiacc⟩ := hacc_inf (max N0 N1)
      have hacc_eq : acc F (edgeSequence α ρ i) = acceptingNodes F (ρ i) (α i) := rfl
      refine ⟨edgeSequence α ρ i, ?_, ?_⟩
      · rw [← hinf]
        exact hN0 i (le_trans (le_max_left N0 N1) hiN)
      · rw [hacc_eq]; exact hiacc
  · rintro ⟨x, hxpos, hstab, ⟨e0, he0D, hxacc⟩⟩
    refine ⟨hD, fun α ρ htr hinf => ?_⟩
    rw [lemma_9 F α]
    obtain ⟨N0, hN0⟩ := eventually_mem_infSet (edgeSequence α ρ)
    refine ⟨ρ, x, hxpos, htr, ⟨N0, ?_⟩, ?_⟩
    · intro i hi
      have heD : edgeSequence α ρ i ∈ D := hinf ▸ hN0 i hi
      have hunst_eq : unstable F (ρ i) (α i) = unst F (edgeSequence α ρ i) := rfl
      rw [hunst_eq]
      exact hstab _ heD
    · intro N
      have he0inf : e0 ∈ infSet (edgeSequence α ρ) := hinf.symm ▸ he0D
      obtain ⟨i, hiN, hie⟩ := he0inf N
      have hacc_eq : acceptingNodes F (ρ i) (α i) = acc F (edgeSequence α ρ i) := rfl
      refine ⟨i, hiN, ?_⟩
      rw [hacc_eq, hie]
      exact hxacc
