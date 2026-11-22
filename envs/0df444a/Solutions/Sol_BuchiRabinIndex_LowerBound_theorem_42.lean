-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.theorem_42
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T06:44:59.194482+00:00
-- url     : https://prove2.me/submissions/65cb4a8e-efae-43d1-96d0-4912871ceef2

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin
import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_31
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_33
import Theorems.Thm_BuchiRabinIndex_LowerBound_theorem_37
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_40
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_41

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Thm42Aux
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

lemma exists_max_clique (n : ℕ) :
    ∃ S : Finset Node, S ⊆ fullTree n ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y) ∧ S.card = omega n := by
  obtain ⟨S0, hS0⟩ := (graph n).exists_isNClique_cliqueNum
  refine ⟨S0.image Subtype.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact v.property
  · intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hne (congrArg Subtype.val h)
    exact hS0.isClique hu hv huv
  · rw [Finset.card_image_of_injective _ Subtype.val_injective]
    exact hS0.card_eq

lemma transition_omega_le (n : ℕ) (hn : 1 ≤ n)
    (r : RabinCondition (Edge (Fin n) (Letter n)))
    (hr : CorrectTransition (fullBuchi n hn) r) :
    omega n ≤ r.card := by
  let F := fullBuchi n hn
  obtain ⟨S, hS, hclique, hcard⟩ := exists_max_clique n
  have hex : ∀ x ∈ S, ∃ p ∈ r, PairAccepts p (Ccycle n hn S x) := by
    intro x hx
    have hAcc : AcceptingCycle F (Ccycle n hn S x) :=
      (lemma_40 n hn S hS hclique x hx).2.2
    obtain ⟨α, ρ, htr, hinf⟩ := ((fact_31 n hn).1 (Ccycle n hn S x)).mp hAcc.1
    have hlang : α ∈ language F := hAcc.2 α ρ htr hinf
    rw [← hr] at hlang
    obtain ⟨ρ', htr', p, hpr, hpacc⟩ := hlang
    have hρ : ρ' = ρ := trace_unique htr' htr
    rw [hρ, hinf] at hpacc
    exact ⟨p, hpr, hpacc⟩
  let pick : Node → RabinPair (Edge (Fin n) (Letter n)) :=
    fun x => if hx : x ∈ S then Classical.choose (hex x hx) else (∅, ∅)
  have hmaps : Set.MapsTo pick S r := by
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    simpa [pick, hx] using (Classical.choose_spec (hex x hx)).1
  have hinj : Set.InjOn pick S := by
    intro x hx y hy heq
    simp only [Finset.mem_coe] at hx hy
    by_contra hne
    have hp1 : PairAccepts (pick x) (Ccycle n hn S x) := by
      simpa [pick, hx] using (Classical.choose_spec (hex x hx)).2
    have hp2 : PairAccepts (pick x) (Ccycle n hn S y) := by
      rw [heq]
      simpa [pick, hy] using (Classical.choose_spec (hex y hy)).2
    have hcx : Cycle F (Ccycle n hn S x) := (lemma_40 n hn S hS hclique x hx).2.2.1
    have hcy : Cycle F (Ccycle n hn S y) := (lemma_40 n hn S hS hclique y hy).2.2.1
    obtain ⟨D, hRej, hSand⟩ := lemma_41 n hn S hS hclique x y hx hy hne
    have hpD : PairAccepts (pick x) D := by
      rcases hSand with ⟨hsub, hsup⟩ | ⟨hsub, hsup⟩
      · exact lemma_33 n hn (pick x) (Ccycle n hn S x) (Ccycle n hn S y) D
          hcx hcy hRej.1 hp1 hp2 hsub hsup
      · exact lemma_33 n hn (pick x) (Ccycle n hn S y) (Ccycle n hn S x) D
          hcy hcx hRej.1 hp2 hp1 hsub (by simpa [Set.union_comm] using hsup)
    obtain ⟨α, ρ, htr, hinf⟩ := ((fact_31 n hn).1 D).mp hRej.1
    have hpr : pick x ∈ r := hmaps hx
    have hmem_tr : α ∈ transitionLanguage F r := by
      refine ⟨ρ, htr, pick x, hpr, ?_⟩
      rwa [hinf]
    rw [hr] at hmem_tr
    exact hRej.2 α ρ htr hinf hmem_tr
  rw [← hcard]
  exact Finset.card_le_card_of_injOn pick hmaps hinj

lemma bounds_from_omega (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : omega n ≤ m) :
    omega n ≤ m ∧ (Even n → 2 ^ (n / 2) ≤ m) ∧
      (Odd n → 3 ≤ n → 3 * 2 ^ ((n - 3) / 2) ≤ m) := by
  refine ⟨hm, ?_, ?_⟩
  · intro hev
    have h2 : 2 ≤ n := by
      rcases hev with ⟨k, rfl⟩
      omega
    have heq := (theorem_37.2.1 n h2).1 hev
    omega
  · intro hodd h3
    have heq := (theorem_37.2.1 n (by omega)).2 hodd
    omega

def liftPair {Q Sigma : Type} (p : RabinPair (History Q)) : RabinPair (Edge Q Sigma) :=
  ({e | e.1 ∈ p.1}, {e | e.1 ∈ p.2})

lemma infSet_state_iff_edge {n : ℕ} (α : ℕ → Letter n) (ρ : ℕ → History (Fin n))
    (H : History (Fin n)) :
    H ∈ infSet ρ ↔ ∃ e ∈ infSet (edgeSequence α ρ), e.1 = H := by
  haveI hfinH : Finite (History (Fin n)) := history_finite
  haveI hfinE : Finite (Edge (Fin n) (Letter n)) := inferInstance
  constructor
  · intro hH
    have hinf_idx : ({i : ℕ | ρ i = H} : Set ℕ).Infinite := by
      rw [Set.infinite_iff_exists_gt]
      intro a
      obtain ⟨i, hi, hρ⟩ := hH (a + 1)
      exact ⟨i, hρ, by omega⟩
    let S_idx : Type := ↥({i : ℕ | ρ i = H} : Set ℕ)
    haveI hinf_S : Infinite S_idx := Set.infinite_coe_iff.mpr hinf_idx
    obtain ⟨e, he_inf⟩ := Finite.exists_infinite_fiber (fun s : S_idx => edgeSequence α ρ s.val)
    have he_set : ((fun s : S_idx => edgeSequence α ρ s.val) ⁻¹' {e}).Infinite :=
      Set.infinite_coe_iff.mp he_inf
    obtain ⟨s0, hs0⟩ := he_set.nonempty
    have he1 : e.1 = H := by
      have hs_eq : edgeSequence α ρ s0.val = e := hs0
      have hρ_eq : ρ s0.val = H := s0.property
      simpa [edgeSequence, hρ_eq] using (congrArg Prod.fst hs_eq).symm
    refine ⟨e, ?_, he1⟩
    intro N
    have hfin : ({s : S_idx | s.val < N} : Set S_idx).Finite := by
      refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
      exact (Set.finite_lt_nat N).subset (by rintro _ ⟨s, hs, rfl⟩; exact hs)
    obtain ⟨s, hs_mem, hs_not_lt⟩ := (he_set.sdiff hfin).nonempty
    exact ⟨s.val, Nat.le_of_not_lt hs_not_lt, hs_mem⟩
  · rintro ⟨e, he, rfl⟩ N
    obtain ⟨i, hi, hie⟩ := he N
    exact ⟨i, hi, congrArg Prod.fst hie⟩

lemma pairAccepts_liftPair {n : ℕ} (p : RabinPair (History (Fin n)))
    (α : ℕ → Letter n) (ρ : ℕ → History (Fin n)) :
    PairAccepts (liftPair p) (infSet (edgeSequence α ρ)) ↔ PairAccepts p (infSet ρ) := by
  unfold PairAccepts liftPair
  constructor
  · rintro ⟨⟨e, he_inf, he1⟩, hempty⟩
    refine ⟨⟨e.1, (infSet_state_iff_edge α ρ e.1).mpr ⟨e, he_inf, rfl⟩, he1⟩, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hempty ⊢
    intro H ⟨hH_inf, hH2⟩
    obtain ⟨e', he'_inf, rfl⟩ := (infSet_state_iff_edge α ρ H).mp hH_inf
    exact hempty e' ⟨he'_inf, hH2⟩
  · rintro ⟨⟨H, hH_inf, hH1⟩, hempty⟩
    obtain ⟨e, he_inf, rfl⟩ := (infSet_state_iff_edge α ρ H).mp hH_inf
    refine ⟨⟨e, he_inf, hH1⟩, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem] at hempty ⊢
    intro e' ⟨he'_inf, he'2⟩
    exact hempty e'.1 ⟨(infSet_state_iff_edge α ρ e'.1).mpr ⟨e', he'_inf, rfl⟩, he'2⟩

end BuchiRabinIndex.LowerBound.Thm42Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Thm42Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ r : RabinCondition (Edge (Fin n) (Letter n)),
      CorrectTransition (fullBuchi n hn) r →
      omega n ≤ r.card ∧ (Even n → 2 ^ (n / 2) ≤ r.card) ∧
        (Odd n → 3 ≤ n → 3 * 2 ^ ((n - 3) / 2) ≤ r.card)) ∧
    (∀ r : RabinCondition (History (Fin n)),
      CorrectState (fullBuchi n hn) r →
      omega n ≤ r.card ∧ (Even n → 2 ^ (n / 2) ≤ r.card) ∧
        (Odd n → 3 ≤ n → 3 * 2 ^ ((n - 3) / 2) ≤ r.card)) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    exact bounds_from_omega n hn r.card (transition_omega_le n hn r hr)
  · intro r hr
    let r' : RabinCondition (Edge (Fin n) (Letter n)) := r.image liftPair
    have hr' : CorrectTransition (fullBuchi n hn) r' := by
      unfold CorrectTransition
      rw [← hr]
      ext α
      simp only [transitionLanguage, stateLanguage, r', Finset.mem_image]
      refine exists_congr fun ρ => and_congr_right fun _ => ?_
      constructor
      · rintro ⟨_, ⟨p, hpr, rfl⟩, hp⟩
        exact ⟨p, hpr, (pairAccepts_liftPair p α ρ).mp hp⟩
      · rintro ⟨p, hpr, hp⟩
        exact ⟨liftPair p, ⟨p, hpr, rfl⟩, (pairAccepts_liftPair p α ρ).mpr hp⟩
    have homega : omega n ≤ r.card :=
      (transition_omega_le n hn r' hr').trans Finset.card_image_le
    exact bounds_from_omega n hn r.card homega
