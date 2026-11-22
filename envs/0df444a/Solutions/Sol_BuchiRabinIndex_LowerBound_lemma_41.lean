-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_41
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:40:37.526632+00:00
-- url     : https://prove2.me/submissions/eb15628d-67bb-4ef5-a65f-cfb27c0bbcbd

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_31
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_9
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_32
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_38
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_39
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_40

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma41Aux
open BuchiRabinIndex.LowerBound
open scoped Classical

lemma treeData_ext {Q : Type} {A B : TreeData Q}
    (hn : A.nodes = B.nodes) (hl : ∀ x, A.label x = B.label x) : A = B := by
  cases A; cases B
  simp only [TreeData.mk.injEq]
  exact ⟨hn, funext hl⟩

lemma pos_bw (b : ℕ) : ∀ (d : ℕ) (x : Node), x ∈ boundedWords b d → Positive x
  | 0, x, hx => by simp [boundedWords] at hx; subst hx; intro i hi; simp at hi
  | d + 1, x, hx => by
    simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc,
      Finset.mem_image] at hx
    rcases hx with rfl | ⟨j, hj, u, hu, rfl⟩
    · intro i hi; simp at hi
    · intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · omega
      · exact pos_bw b d u hu i hi

lemma pos_of_mem_fullTree {n : ℕ} {x : Node} (hx : x ∈ fullTree n) : Positive x := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact pos_bw _ _ x (Finset.mem_filter.1 hx).1

lemma weight_le_of_mem_fullTree {n : ℕ} {x : Node} (hx : x ∈ fullTree n) : weight x ≤ n - 1 := by
  unfold fullTree at hx
  split_ifs at hx
  · simp at hx
  · exact (Finset.mem_filter.1 hx).2

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
    · obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
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
  | [], _ :: _ => Or.inl ((preLt_nil_left _).mpr (by simp))
  | _ :: _, [] => Or.inr (Or.inr ((preLt_nil_left _).mpr (by simp)))
  | a :: xs, b :: ys => by
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact Or.inl ((preLt_cons_iff _ _ _ _).mpr (Or.inl hab))
    · rcases preLt_trichotomy xs ys with h | rfl | h
      · exact Or.inl ((preLt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((preLt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩)))
    · exact Or.inr (Or.inr ((preLt_cons_iff _ _ _ _).mpr (Or.inl hba)))

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
    by_contra h
    apply hx
    intro N
    by_contra hN
    apply h ⟨N, fun i hi heq => hN ⟨i, hi, heq⟩⟩
  let B : Finset X := (@Finset.univ X hft).filter (fun x => x ∉ infSet f)
  let bound : X → ℕ := fun x => if hx : x ∉ infSet f then Classical.choose (hbad x hx) else 0
  refine ⟨B.sup bound, fun i hi => ?_⟩
  by_contra hni
  have hxB : f i ∈ B := Finset.mem_filter.mpr ⟨@Finset.mem_univ X hft _, hni⟩
  have hle : bound (f i) ≤ B.sup bound := Finset.le_sup hxB
  have hspec := Classical.choose_spec (hbad (f i) hni)
  have hbound_eq : bound (f i) = Classical.choose (hbad (f i) hni) := dif_pos hni
  exact hspec i (by omega) rfl

lemma rejectingCycle_of_not_accepting {n : ℕ} (hn : 1 ≤ n)
    {D : Set (Edge (Fin n) (Letter n))}
    (hD : Cycle (fullBuchi n hn) D)
    (hnot : ¬ AcceptingCycle (fullBuchi n hn) D) :
    RejectingCycle (fullBuchi n hn) D := by
  let F := fullBuchi n hn
  have hfinH : Finite (History (Fin n)) := history_finite
  have hfinE : Finite (Edge (Fin n) (Letter n)) := inferInstance
  have hneF : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨hD, fun α ρ htr hinf hlang => hnot ?_⟩
  obtain ⟨ρ', z, hzpos, htr', ⟨N1, hstab⟩, hacc_inf⟩ := (@lemma_9 _ _ _ hneF _ F α).mp hlang
  have hρ : ρ' = ρ := trace_unique htr' htr
  rw [hρ] at hstab hacc_inf
  obtain ⟨N0, hN0⟩ := @eventually_mem_infSet _ hfinE (edgeSequence α ρ)
  refine (lemma_32 n hn D hD).mpr ⟨z, hzpos, ?_, ?_⟩
  · intro e heD
    rw [← hinf] at heD
    obtain ⟨i, hiN, hie⟩ := heD N1
    rw [← hie]
    exact hstab i hiN
  · obtain ⟨i, hiN, hiacc⟩ := hacc_inf (max N0 N1)
    refine ⟨edgeSequence α ρ i, ?_, hiacc⟩
    rw [← hinf]
    exact hN0 i (le_trans (le_max_left N0 N1) hiN)

lemma readWord_none {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ v : List Sigma, readWord B none v = none
  | [] => rfl
  | _ :: v => readWord_none B v

lemma readWord_append {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ (u v : List Sigma) (H : Option (History Q)),
      readWord B H (u ++ v) = readWord B (readWord B H u) v
  | [], _, _ => rfl
  | σ :: u, v, H => readWord_append B u v (H.bind fun h => successor B h σ)

lemma drop_eq_getElem_cons {α : Type} :
    ∀ (w : List α) (i : ℕ) (hi : i < w.length), w.drop i = w[i] :: w.drop (i + 1)
  | [], _, hi => by simp at hi
  | a :: ws, 0, _ => by simp
  | _ :: ws, i + 1, hi => drop_eq_getElem_cons ws i (by simpa using hi)

lemma fst_mem_visited_of_mem_wordEdges {Q Sigma : Type} {B : NBW Q Sigma}
    {H : History Q} {v : List Sigma} {e : Edge Q Sigma}
    (he : e ∈ wordEdges B (some H) v) : e.1 ∈ visited B H v := by
  obtain ⟨i, hread, _, _⟩ := he
  exact ⟨i.val, Nat.le_of_lt i.isLt, hread⟩

lemma exists_mem_wordEdges_of_visited {Q Sigma : Type} {B : NBW Q Sigma}
    {H M : History Q} {w : List Sigma}
    (hcw : ClosedWalk B H w) (hM : M ∈ visited B H w) :
    ∃ e ∈ wordEdges B (some H) w, e.1 = M := by
  obtain ⟨hw_pos, _, hloop⟩ := hcw
  obtain ⟨i, hi_le, hread_i⟩ := hM
  by_cases hi_lt : i < w.length
  · have hsplit : w.take i ++ (w[i] :: w.drop (i + 1)) = w := by
      rw [← drop_eq_getElem_cons w i hi_lt, List.take_append_drop]
    have htail : readWord B (some M) (w[i] :: w.drop (i + 1)) = some H := by
      rw [← hsplit, readWord_append, hread_i] at hloop
      exact hloop
    dsimp only [readWord, Option.bind] at htail
    cases hsucc : successor B M w[i] with
    | none =>
      rw [hsucc, readWord_none] at htail
      cases htail
    | some M' =>
      refine ⟨(M, w[i], M'), ⟨⟨i, hi_lt⟩, hread_i, ?_, hsucc⟩, rfl⟩
      simp [Fin.getElem_fin]
  · have hi_eq : i = w.length := by omega
    subst hi_eq
    rw [List.take_length, hloop] at hread_i
    have hMH : M = H := Option.some.inj hread_i.symm
    subst hMH
    have hsplit : w[0]'hw_pos :: w.drop 1 = w :=
      (drop_eq_getElem_cons w 0 hw_pos).symm
    have htail : readWord B (some M) (w[0]'hw_pos :: w.drop 1) = some M := by
      rwa [← hsplit] at hloop
    dsimp only [readWord, Option.bind] at htail
    cases hsucc : successor B M (w[0]'hw_pos) with
    | none =>
      rw [hsucc, readWord_none] at htail
      cases htail
    | some M' =>
      refine ⟨(M, w[0]'hw_pos, M'), ⟨⟨0, hw_pos⟩, by simp [readWord], ?_, hsucc⟩, rfl⟩
      simp [Fin.getElem_fin]

lemma mem_mapData_label {Q R : Type} (H : TreeData Q) (π : Q → R) (x : Node) (r : R) :
    r ∈ (mapData H π).label x ↔ ∃ q ∈ H.label x, π q = r :=
  Finset.mem_image

lemma mapData_comp_eq_self {Q : Type} (H : TreeData Q) (π1 π2 : Q → Q)
    (hout : ∀ x, x ∉ H.nodes → H.label x = ∅)
    (hid : ∀ x ∈ H.nodes, ∀ q ∈ H.label x, π2 (π1 q) = q) :
    mapData (mapData H π1) π2 = H := by
  refine treeData_ext ?_ ?_
  · rfl
  · intro x
    dsimp only [mapData]
    by_cases hx : x ∈ H.nodes
    · rw [Finset.image_image]
      calc (H.label x).image (π2 ∘ π1)
          = (H.label x).image id := Finset.image_congr (hid x hx)
        _ = H.label x := Finset.image_id
    · rw [hout x hx, Finset.image_empty, Finset.image_empty]

lemma canonical_own_and_stateSet {n : ℕ} (hn : 1 ≤ n) {T : Finset Node}
    (hT : Ordered T) (hcard : T.card ≤ n) {H : History (Fin n)}
    (hHtree : Htree n T = some H) :
    H.val = canonicalData n T ∧
    Simple H ∧
    stateSet H.val = canonicalStates n T ∧
    (∀ x ∈ T, own H.val x = {stateAt n hn (rank T x)}) := by
  classical
  have hHval : H.val = canonicalData n T := by
    unfold Htree asHistory at hHtree
    split_ifs at hHtree with hv
    · exact congrArg Subtype.val (Option.some.inj hHtree).symm
  have hroot : [] ∈ T := by
    have hr : [] ∈ H.val.nodes := H.property.2.1
    rwa [hHval] at hr
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
  have hown : ∀ x ∈ T, own (canonicalData n T) x = {f x} := by
    intro x hx
    have hchild_lbl : childLabels (canonicalData n T) x =
        (T.filter fun y => x.IsPrefix y ∧ y ≠ x).image f := by
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
    rw [own, hl_in x hx, hchild_lbl]
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
  refine ⟨hHval, ?_, by rw [hHval]; exact hst, fun x hx => by rw [hHval]; exact hown x hx⟩
  intro x hx
  rw [hHval] at hx ⊢
  rw [hown x hx]
  simp

lemma acycle_closedWalk_and_acc {n : ℕ} (hn : 1 ≤ n) {y : Node} (hy : y ∈ fullTree n) :
    ∃ Hy, Htree n (chain y) = some Hy ∧
      ClosedWalk (fullBuchi n hn) Hy (acceptingWord n hn y) ∧
      (∀ e ∈ Acycle n hn y, ∀ z ∈ acc (fullBuchi n hn) e, z = y) := by
  classical
  let F := fullBuchi n hn
  let T := chain y
  have hpy : Positive y := pos_of_mem_fullTree hy
  have hf30 := fact_30 y y hpy hpy
  have hLast : Last T y := hf30.2.1
  have hord : Ordered T := hf30.2.2.2.2.1
  have hleaf_T : Leaf T y := (hf30.2.2.2.2.2.2.2.2 T y hord hLast).1
  have hcard : T.card ≤ n := by
    have hw := weight_le_of_mem_fullTree hy
    have hc := card_chain_eq y hpy
    change (chain y).card ≤ n
    omega
  have hcard_pos : 1 ≤ T.card := Finset.card_pos.mpr ⟨y, hLast.1⟩
  obtain ⟨Hy, hHtree, hreach⟩ := lemma_39 n hn T hord ⟨y, hLast.1⟩ hcard
  obtain ⟨hHy_val, hHy_simple, hHy_st, hHy_own⟩ :=
    canonical_own_and_stateSet hn hord hcard hHtree
  have hrank_y : rank T y = T.card - 1 := by
    have hfilt : T.filter (PreLt · y) = T.erase y := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨huT, huy⟩
        exact ⟨fun h => preLt_irrefl y (h ▸ huy), huT⟩
      · rintro ⟨huy, huT⟩
        exact ⟨huT, (hLast.2 u huT).resolve_left huy⟩
    unfold rank
    rw [hfilt]
    have := Finset.card_erase_add_one hLast.1
    omega
  let P := canonicalStates n T
  let s := stateAt n hn (T.card - 1)
  have hleaf_Hy : Leaf Hy.val.nodes y := by
    change Leaf (canonicalData n T).nodes y at *
    rwa [hHy_val]
  have hlbl_Hy_y : Hy.val.label y = {s} := by
    have hown_eq : own Hy.val y = Hy.val.label y := by
      simp [own, childLabels, hleaf_Hy.2]
    rw [← hown_eq, hHy_own y hLast.1, hrank_y]
  have hs_val : s.val = T.card - 1 := by
    simp [s, stateAt, Nat.mod_eq_of_lt (by omega : T.card - 1 < n)]
  have hs_mem_P : s ∈ P := by
    dsimp only [P]
    simp only [canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and, hs_val]
    omega
  by_cases hlt : T.card < n
  · let qn := lastState n hn
    let π1 : Fin n → Fin n := fun q => if q = s then qn else q
    have haccL_eq : accLetter hn P s = permLetter P π1 := by
      ext uv
      simp only [accLetter, idLetter, permLetter, Finset.mem_insert, Finset.mem_image,
        Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨q, ⟨hqs, hqP⟩, rfl⟩)
        · exact ⟨s, hs_mem_P, by simp [π1, qn]⟩
        · exact ⟨q, hqP, by simp [π1, hqs]⟩
      · rintro ⟨q, hqP, rfl⟩
        by_cases hqs : q = s
        · subst hqs; exact Or.inl (by simp [π1, qn])
        · exact Or.inr ⟨q, ⟨hqs, hqP⟩, by simp [π1, hqs]⟩
    have hinj_π1 : Set.InjOn π1 {q | q ∈ stateSet Hy.val} := by
      rw [hHy_st]
      intro q1 hq1 q2 hq2 heq
      change q1 ∈ canonicalStates n T at hq1
      change q2 ∈ canonicalStates n T at hq2
      simp only [canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
      by_cases c1 : q1 = s <;> by_cases c2 : q2 = s
      · rw [c1, c2]
      · simp only [π1, c1, c2, ↓reduceIte] at heq
        have hv := congrArg Fin.val heq
        simp [qn, lastState] at hv
        omega
      · simp only [π1, c1, c2, ↓reduceIte] at heq
        have hv := congrArg Fin.val heq
        simp [qn, lastState] at hv
        omega
      · simpa [π1, c1, c2] using heq
    have hl38_1 := (lemma_38 n hn Hy hHy_simple).2.2.1 y s π1 hleaf_Hy hlbl_Hy_y hinj_π1 (by simp [π1, qn])
    rw [hHy_st, ← haccL_eq] at hl38_1
    obtain ⟨H1, hsucc1, hH1_val, hH1_simple, hacc1, _⟩ := hl38_1
    let P1 := insert qn (P.erase s)
    let π2 : Fin n → Fin n := fun q => if q = qn then s else q
    have hst_H1 : stateSet H1.val = P1 := by
      ext r
      change r ∈ H1.val.label [] ↔ r ∈ P1
      rw [hH1_val, mem_mapData_label]
      change (∃ q ∈ stateSet Hy.val, π1 q = r) ↔ r ∈ P1
      rw [hHy_st]
      dsimp only [P1]
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨q, hqP, rfl⟩
        by_cases hqs : q = s
        · subst hqs; exact Or.inl (by simp [π1])
        · have hπq : π1 q = q := by dsimp only [π1]; exact if_neg hqs
          rw [hπq]
          exact Or.inr ⟨hqs, hqP⟩
      · rintro (rfl | ⟨hrs, hrP⟩)
        · exact ⟨s, hs_mem_P, by simp [π1]⟩
        · exact ⟨r, hrP, by simp [π1, hrs]⟩
    have hinj_π2 : Set.InjOn π2 {q | q ∈ stateSet H1.val} := by
      rw [hst_H1]
      intro q1 hq1 q2 hq2 heq
      change q1 ∈ insert qn (P.erase s) at hq1
      change q2 ∈ insert qn (P.erase s) at hq2
      dsimp only [P] at hq1 hq2
      simp only [canonicalStates, Finset.mem_insert, Finset.mem_erase,
        Finset.mem_filter, Finset.mem_univ, true_and] at hq1 hq2
      by_cases c1 : q1 = qn <;> by_cases c2 : q2 = qn
      · rw [c1, c2]
      · rcases hq2 with rfl | ⟨h2s, _⟩
        · exact absurd rfl c2
        · simp only [π2, c1, c2, ↓reduceIte] at heq
          exact absurd heq.symm h2s
      · rcases hq1 with rfl | ⟨h1s, _⟩
        · exact absurd rfl c1
        · simp only [π2, c1, c2, ↓reduceIte] at heq
          exact absurd heq h1s
      · simpa [π2, c1, c2] using heq
    have hno_qn_π2 : ∀ q ∈ stateSet H1.val, π2 q ≠ qn := by
      rw [hst_H1]
      intro q hq
      change q ∈ insert qn (P.erase s) at hq
      dsimp only [P] at hq
      simp only [canonicalStates, Finset.mem_insert, Finset.mem_erase,
        Finset.mem_filter, Finset.mem_univ, true_and] at hq
      by_cases cq : q = qn
      · intro heq
        have hv := congrArg Fin.val heq
        simp [π2, cq, hs_val, qn, lastState] at hv
        omega
      · rcases hq with rfl | ⟨_, hqlt⟩
        · exact absurd rfl cq
        · dsimp only [π2]
          rw [if_neg cq]
          exact cq
    have hl38_2 := (lemma_38 n hn H1 hH1_simple).2.1 π2 hinj_π2 hno_qn_π2
    rw [hst_H1] at hl38_2
    obtain ⟨H2, hsucc2, hH2_val, _, hacc2, _⟩ := hl38_2
    have hH2_eq_Hy : H2 = Hy := by
      apply Subtype.ext
      rw [hH2_val, hH1_val]
      apply mapData_comp_eq_self Hy.val π1 π2 Hy.property.2.2.1
      intro x hxT q hqx
      have hsub_P : Hy.val.label x ⊆ P := by
        dsimp only [P]
        rw [← hHy_st]
        simpa [stateSet] using label_sub_of_prefix Hy.property [] x (by simpa using hxT)
      have hqP := hsub_P hqx
      dsimp only [P] at hqP
      simp only [canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and] at hqP
      by_cases hqs : q = s
      · subst hqs; simp [π1, π2]
      · have hq_ne_qn : q ≠ qn := by
          intro heq; subst heq; simp [qn, lastState] at hqP; omega
        simp [π1, π2, hqs, hq_ne_qn]
    subst H2
    refine ⟨Hy, hHtree, ⟨?_, hreach, ?_⟩, ?_⟩
    · simp [acceptingWord, T, hlt]
    · unfold acceptingWord
      dsimp only [T] at hlt
      rw [if_pos hlt]
      dsimp only [readWord, Option.bind]
      change (successor F Hy (accLetter hn P s)).bind
        (fun h => successor F h (permLetter P1 π2)) = some Hy
      rw [hsucc1]
      exact hsucc2
    · intro e he z hz
      rw [Acycle, hHtree] at he
      obtain ⟨i, hread_i, hlet_i, _⟩ := he
      have hlet_opt : (acceptingWord n hn y)[i.val]? = some e.2.1 := by
        rw [List.getElem?_eq_getElem i.isLt, ← Fin.getElem_fin, hlet_i]
      have hi_lt2 : i.val < 2 := by simpa [acceptingWord, T, hlt] using i.isLt
      rcases (by omega : i.val = 0 ∨ i.val = 1) with hi0 | hi1
      · have he1 : e.1 = Hy := by
          simpa [hi0, readWord] using hread_i.symm
        have he2 : e.2.1 = accLetter hn P s := by
          rw [hi0] at hlet_opt
          unfold acceptingWord at hlet_opt
          dsimp only [T] at hlt
          rw [if_pos hlt] at hlet_opt
          exact (Option.some.inj hlet_opt).symm
        change z ∈ acceptingNodes F e.1 e.2.1 at hz
        rw [he1, he2, hacc1, Finset.mem_singleton] at hz
        exact hz
      · have he1 : e.1 = H1 := by
          rw [hi1] at hread_i
          unfold acceptingWord at hread_i
          dsimp only [T] at hlt
          rw [if_pos hlt] at hread_i
          dsimp only [List.take, readWord, Option.bind] at hread_i
          change successor F Hy (accLetter hn P s) = some e.1 at hread_i
          rw [hsucc1] at hread_i
          exact (Option.some.inj hread_i).symm
        have he2 : e.2.1 = permLetter P1 π2 := by
          rw [hi1] at hlet_opt
          unfold acceptingWord at hlet_opt
          dsimp only [T] at hlt
          rw [if_pos hlt] at hlet_opt
          exact (Option.some.inj hlet_opt).symm
        change z ∈ acceptingNodes F e.1 e.2.1 at hz
        rw [he1, he2, hacc2] at hz
        simp at hz
  · have heq_n : T.card = n := by omega
    have hs_eq_qn : s = lastState n hn := by
      ext; simp [hs_val, heq_n, lastState]
    have hidL_eq : idLetter P = permLetter (stateSet Hy.val) id := by
      rw [hHy_st]; rfl
    have hinj_id : Set.InjOn (id : Fin n → Fin n) {q | q ∈ stateSet Hy.val} :=
      fun _ _ _ _ h => h
    have hl38 := (lemma_38 n hn Hy hHy_simple).2.2.1 y s id hleaf_Hy hlbl_Hy_y hinj_id hs_eq_qn
    rw [← hidL_eq] at hl38
    obtain ⟨H1, hsucc1, hH1_val, _, hacc1, _⟩ := hl38
    have hH1_eq_Hy : H1 = Hy := by
      apply Subtype.ext
      rw [hH1_val]
      refine treeData_ext ?_ ?_
      · rfl
      · intro x
        simp [mapData]
    subst H1
    refine ⟨Hy, hHtree, ⟨?_, hreach, ?_⟩, ?_⟩
    · simp [acceptingWord, T, hlt]
    · unfold acceptingWord
      dsimp only [T] at hlt
      rw [if_neg hlt]
      exact hsucc1
    · intro e he z hz
      rw [Acycle, hHtree] at he
      obtain ⟨i, hread_i, hlet_i, _⟩ := he
      have hlet_opt : (acceptingWord n hn y)[i.val]? = some e.2.1 := by
        rw [List.getElem?_eq_getElem i.isLt, ← Fin.getElem_fin, hlet_i]
      have hi0 : i.val = 0 := by
        have := i.isLt
        simp [acceptingWord, T, hlt] at this
        exact this
      have he1 : e.1 = Hy := by
        simpa [hi0, readWord] using hread_i.symm
      have he2 : e.2.1 = idLetter P := by
        rw [hi0] at hlet_opt
        unfold acceptingWord at hlet_opt
        dsimp only [T] at hlt
        rw [if_neg hlt] at hlet_opt
        exact (Option.some.inj hlet_opt).symm
      change z ∈ acceptingNodes F e.1 e.2.1 at hz
      rw [he1, he2, hacc1, Finset.mem_singleton] at hz
      exact hz

lemma lemma_41_asym (n : ℕ) (hn : 1 ≤ n) (S : Finset Node)
    (hS : S ⊆ fullTree n) (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y)
    (x y : Node) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) (hy_not : y ∉ chain x) :
    ∃ D, RejectingCycle (fullBuchi n hn) D ∧
      Ccycle n hn S y ⊆ D ∧ D ⊆ Ccycle n hn S x ∪ Ccycle n hn S y := by
  let F := fullBuchi n hn
  let D := Wxy n hn x y ∪ Ccycle n hn S y
  have hpx : Positive x := pos_of_mem_fullTree (hS hx)
  have hpy : Positive y := pos_of_mem_fullTree (hS hy)
  have hsub1 : Ccycle n hn S y ⊆ D := Set.subset_union_right
  have hsub2 : D ⊆ Ccycle n hn S x ∪ Ccycle n hn S y := by
    rintro e (he_xy | he_cy)
    · left
      left
      exact Set.mem_biUnion (Finset.mem_erase.mpr ⟨hne.symm, hy⟩) he_xy
    · exact Or.inr he_cy
  have hl40_xy := (lemma_40 n hn S hS hclique x hx).1 y hy hne hy_not
  obtain ⟨⟨Hx, K, hHx_tree, hK_tree, hcw_xy, hK_vis_xy⟩, _, ⟨ey_unst, hey_mem, hy_unst⟩, hacc_xy_only, hacc_xy_imp⟩ := hl40_xy
  have hCy_cycle : Cycle F (Ccycle n hn S y) := (lemma_40 n hn S hS hclique y hy).2.2.1
  obtain ⟨H0, v0, hcw0, hv0_edges⟩ := hCy_cycle
  obtain ⟨Hy, hHy_tree, hcw_ay, hacc_ay_only⟩ := acycle_closedWalk_and_acc hn (hS hy)
  have hK_vis_0 : K ∈ visited F H0 v0 := by
    by_cases hxy_in : x ∈ chain y
    · have hch_sub : chain x ⊆ chain y := (fact_30 y x hpy hpx).2.2.1 hxy_in
      have hunion_eq : chain x ∪ chain y = chain y := Finset.union_eq_right.mpr hch_sub
      rw [hunion_eq, hHy_tree] at hK_tree
      have hK_eq_Hy : K = Hy := Option.some.inj hK_tree.symm
      subst hK_eq_Hy
      have hHy_vis_ay : K ∈ visited F K (acceptingWord n hn y) :=
        ⟨0, Nat.zero_le _, by simp [readWord]⟩
      obtain ⟨e_ay, he_ay, he1⟩ := exists_mem_wordEdges_of_visited hcw_ay hHy_vis_ay
      have he_in_Cy : e_ay ∈ wordEdges F (some H0) v0 := by
        rw [hv0_edges]
        right
        simpa [Acycle, hHy_tree] using he_ay
      rw [← he1]
      exact fst_mem_visited_of_mem_wordEdges he_in_Cy
    · have hl40_yx := (lemma_40 n hn S hS hclique y hy).1 x hx hne.symm hxy_in
      obtain ⟨⟨Hy', Kyx, hHy'_tree, hKyx_tree, hcw_yx, hKyx_vis⟩, _, _, _, _⟩ := hl40_yx
      rw [Finset.union_comm, hK_tree] at hKyx_tree
      have hKyx_eq : Kyx = K := Option.some.inj hKyx_tree.symm
      subst hKyx_eq
      obtain ⟨e_yx, he_yx, he1⟩ := exists_mem_wordEdges_of_visited hcw_yx hKyx_vis
      have he_in_Cy : e_yx ∈ wordEdges F (some H0) v0 := by
        rw [hv0_edges]
        left
        refine Set.mem_biUnion (Finset.mem_erase.mpr ⟨hne, hx⟩) ?_
        simpa [Wxy, hHy'_tree] using he_yx
      rw [← he1]
      exact fst_mem_visited_of_mem_wordEdges he_in_Cy
  have hD_cycle : Cycle F D := by
    let famH : Fin 2 → History (Fin n) := ![H0, Hx]
    let famV : Fin 2 → List (Letter n) := ![v0, connectingWord n hn x y]
    have hcw_fam : ∀ i : Fin 2, ClosedWalk F (famH i) (famV i) := by
      intro i
      fin_cases i
      · exact hcw0
      · exact hcw_xy
    have hconn_fam : ∀ j : Fin 2, 0 < j.val → ∃ i : Fin 2, i.val < j.val ∧
        (visited F (famH i) (famV i) ∩ visited F (famH j) (famV j)).Nonempty := by
      intro j hj
      have hj1 : j = 1 := Fin.ext (by omega)
      subst hj1
      exact ⟨0, by decide, K, hK_vis_0, hK_vis_xy⟩
    have hc_union := (fact_31 n hn).2 2 famH famV (by decide) hcw_fam hconn_fam
    have hunion_D : (⋃ i : Fin 2, wordEdges F (some (famH i)) (famV i)) = D := by
      ext e
      simp only [Set.mem_iUnion, Fin.exists_fin_two, famH, famV, Matrix.cons_val_zero,
        Matrix.cons_val_one, hv0_edges]
      have hwxy_eq : wordEdges F (some Hx) (connectingWord n hn x y) = Wxy n hn x y := by
        dsimp only [F]
        simp [Wxy, hHx_tree]
      rw [hwxy_eq]
      exact Or.comm
    rwa [hunion_D] at hc_union
  have hCy_acc_only : ∀ e ∈ Ccycle n hn S y, ∀ z ∈ acc F e, z = y := by
    rintro e (he_wx | he_ay) z hz
    · simp only [Wx, Set.mem_iUnion] at he_wx
      obtain ⟨w, hw_er, he_yw⟩ := he_wx
      obtain ⟨hw_ne, hwS⟩ := Finset.mem_erase.mp hw_er
      have hw_not_cy : w ∉ chain y := by
        intro hw_in
        obtain ⟨i, _⟩ := he_yw
        have hi := i.isLt
        simp [connectingWord, if_pos hw_in] at hi
      exact ((lemma_40 n hn S hS hclique y hy).1 w hwS hw_ne.symm hw_not_cy).2.2.2.1 e he_yw z hz
    · exact hacc_ay_only e he_ay z hz
  have hnot_acc : ¬ AcceptingCycle F D := by
    intro hAcc
    obtain ⟨z, _, hz_stab, ⟨e0, he0D, hz_acc⟩⟩ := (lemma_32 n hn D hD_cycle).mp hAcc
    have hzx_or_y : z = x ∨ z = y := by
      rcases he0D with he0_xy | he0_cy
      · exact Or.inl (hacc_xy_only e0 he0_xy z hz_acc)
      · exact Or.inr (hCy_acc_only e0 he0_cy z hz_acc)
    rcases hzx_or_y with hzx | hzy
    · subst z
      by_cases hxy_in : x ∈ chain y
      · rcases he0D with he0_xy | he0_cy
        · have ⟨_, hpre_yx⟩ := hacc_xy_imp ⟨e0, he0_xy, hz_acc⟩
          have hLast_y : Last (chain y) y := (fact_30 y y hpy hpy).2.1
          have hpre_xy : PreLt x y := (hLast_y.2 x hxy_in).resolve_left hne
          exact preLt_irrefl x (preLt_trans hpre_xy hpre_yx)
        · exact hne (hCy_acc_only e0 he0_cy x hz_acc)
      · obtain ⟨ex, hex_mem, hx_unst⟩ :=
          ((lemma_40 n hn S hS hclique y hy).1 x hx hne.symm hxy_in).2.2.1
        have hex_D : ex ∈ D :=
          Or.inr (Or.inl (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hne, hx⟩) hex_mem))
        exact hz_stab ex hex_D hx_unst
    · subst z
      exact hz_stab ey_unst (Or.inl hey_mem) hy_unst
  exact ⟨D, rejectingCycle_of_not_accepting hn hD_cycle hnot_acc, hsub1, hsub2⟩

end BuchiRabinIndex.LowerBound.Lemma41Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma41Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (S : Finset Node)
    (hS : S ⊆ fullTree n) (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y)
    (x y : Node) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
    ∃ D, RejectingCycle (fullBuchi n hn) D ∧
      ((Ccycle n hn S y ⊆ D ∧ D ⊆ Ccycle n hn S x ∪ Ccycle n hn S y) ∨
       (Ccycle n hn S x ⊆ D ∧ D ⊆ Ccycle n hn S x ∪ Ccycle n hn S y)) := by
  classical
  have hpx : Positive x := pos_of_mem_fullTree (hS hx)
  have hpy : Positive y := pos_of_mem_fullTree (hS hy)
  by_cases hy_not : y ∉ chain x
  · obtain ⟨D, hrej, h1, h2⟩ := lemma_41_asym n hn S hS hclique x y hx hy hne hy_not
    exact ⟨D, hrej, Or.inl ⟨h1, h2⟩⟩
  · have hy_in : y ∈ chain x := not_not.mp hy_not
    have hx_not : x ∉ chain y := fun hx_in =>
      hne ((fact_30 x y hpx hpy).2.2.2.1 hx_in hy_in)
    obtain ⟨D, hrej, h1, h2⟩ := lemma_41_asym n hn S hS hclique y x hy hx hne.symm hx_not
    exact ⟨D, hrej, Or.inr ⟨h1, by simpa [Set.union_comm] using h2⟩⟩
