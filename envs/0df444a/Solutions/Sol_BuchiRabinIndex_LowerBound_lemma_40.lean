-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_40
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:54:24.331603+00:00
-- url     : https://prove2.me/submissions/e554494d-364f-42b0-86c5-9801a645bad7

import Definitions.Def_BuchiRabinIndex_LowerBound_Witness
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_30
import Theorems.Thm_BuchiRabinIndex_LowerBound_fact_31
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_32
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_38
import Theorems.Thm_BuchiRabinIndex_LowerBound_lemma_39

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma40Aux
noncomputable section
open BuchiRabinIndex.LowerBound
open scoped Classical

lemma mem_own_iff {Q : Type} (H : TreeData Q) (x : Node) (q : Q) :
    q ∈ own H x ↔ q ∈ H.label x ∧ q ∉ childLabels H x := by
  unfold own
  exact Finset.mem_sdiff

lemma mem_mapData_iff {Q R : Type} (H : TreeData Q) (π : Q → R) (x : Node) (r : R) :
    r ∈ (mapData H π).label x ↔ ∃ q ∈ H.label x, π q = r := by
  unfold mapData
  exact Finset.mem_image

lemma treeData_ext {Q : Type} {A B : TreeData Q}
    (h1 : A.nodes = B.nodes) (h2 : A.label = B.label) : A = B := by
  cases A; cases B; simp only at h1 h2; subst h1 h2; rfl

/-! ### `PreLt` strict total order -/

lemma preLt_nil_cons (a : ℕ) (xs : List ℕ) : PreLt [] (a :: xs) :=
  Or.inl ⟨List.nil_prefix, by simp⟩

lemma not_preLt_nil (x : Node) : ¬ PreLt x [] := by
  rintro (⟨hp, hne⟩ | ⟨p, i, j, u, v, _, hy, _⟩)
  · exact hne (List.prefix_nil.mp hp)
  · simp at hy

lemma preLt_cons_iff (a b : ℕ) (xs ys : List ℕ) :
    PreLt (a :: xs) (b :: ys) ↔ a < b ∨ (a = b ∧ PreLt xs ys) := by
  constructor
  · rintro (⟨hp, hne⟩ | ⟨p, i, j, u, v, hx, hy, hij⟩)
    · obtain ⟨hab, hpre⟩ := List.cons_prefix_cons.mp hp
      exact Or.inr ⟨hab, Or.inl ⟨hpre, fun h => hne (by rw [hab, h])⟩⟩
    · cases p with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hx hy
        rw [hx.1, hy.1]
        exact Or.inl hij
      | cons c p' =>
        simp only [List.cons_append, List.cons.injEq] at hx hy
        refine Or.inr ⟨hx.1.trans hy.1.symm, Or.inr ⟨p', i, j, u, v, hx.2, hy.2, hij⟩⟩
  · rintro (hab | ⟨rfl, hpre⟩)
    · exact Or.inr ⟨[], a, b, xs, ys, rfl, rfl, hab⟩
    · rcases hpre with ⟨hp, hne⟩ | ⟨p, i, j, u, v, hx, hy, hij⟩
      · exact Or.inl ⟨List.cons_prefix_cons.mpr ⟨rfl, hp⟩, fun h => hne (List.cons.inj h).2⟩
      · exact Or.inr ⟨a :: p, i, j, u, v, by simp [hx], by simp [hy], hij⟩

lemma preLt_irrefl : ∀ x : Node, ¬ PreLt x x
  | [] => not_preLt_nil []
  | a :: xs => by
    rw [preLt_cons_iff]
    rintro (hlt | ⟨_, hpre⟩)
    · omega
    · exact preLt_irrefl xs hpre

lemma preLt_trans : ∀ {x y z : Node}, PreLt x y → PreLt y z → PreLt x z
  | [], _, [], _, hyz => absurd hyz (not_preLt_nil _)
  | [], _, c :: zs, _, _ => preLt_nil_cons c zs
  | a :: _, [], _, hxy, _ => absurd hxy (not_preLt_nil _)
  | _ :: _, _ :: _, [], _, hyz => absurd hyz (not_preLt_nil _)
  | a :: xs, b :: ys, c :: zs, hxy, hyz => by
    rw [preLt_cons_iff] at hxy hyz ⊢
    rcases hxy with hab | ⟨rfl, hxy'⟩
    · rcases hyz with hbc | ⟨rfl, _⟩
      · exact Or.inl (lt_trans hab hbc)
      · exact Or.inl hab
    · rcases hyz with hbc | ⟨rfl, hyz'⟩
      · exact Or.inl hbc
      · exact Or.inr ⟨rfl, preLt_trans hxy' hyz'⟩

lemma preLt_asymm {x y : Node} (h : PreLt x y) : ¬ PreLt y x :=
  fun h' => preLt_irrefl x (preLt_trans h h')

lemma preLt_trichotomy : ∀ (x y : Node), PreLt x y ∨ x = y ∨ PreLt y x
  | [], [] => Or.inr (Or.inl rfl)
  | [], b :: ys => Or.inl (preLt_nil_cons b ys)
  | a :: xs, [] => Or.inr (Or.inr (preLt_nil_cons a xs))
  | a :: xs, b :: ys => by
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact Or.inl ((preLt_cons_iff a b xs ys).mpr (Or.inl hab))
    · rcases preLt_trichotomy xs ys with hlt | rfl | hgt
      · exact Or.inl ((preLt_cons_iff a a xs ys).mpr (Or.inr ⟨rfl, hlt⟩))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((preLt_cons_iff a a ys xs).mpr (Or.inr ⟨rfl, hgt⟩)))
    · exact Or.inr (Or.inr ((preLt_cons_iff b a ys xs).mpr (Or.inl hba)))

/-! ### `fullTree`, `chain`, and `rank` -/

lemma positive_of_mem_boundedWords (b : ℕ) : ∀ (d : ℕ) {x : Node},
    x ∈ boundedWords b d → Positive x
  | 0, x, hx => by
    simp [boundedWords] at hx; subst hx
    intro i hi; simp at hi
  | d + 1, x, hx => by
    simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc,
      Finset.mem_image] at hx
    rcases hx with rfl | ⟨a, ⟨ha1, _⟩, t, ht, rfl⟩
    · intro i hi; simp at hi
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hit
      · omega
      · exact positive_of_mem_boundedWords b d ht i hit

lemma mem_fullTree_props {n : ℕ} {x : Node} (hx : x ∈ fullTree n) :
    Positive x ∧ weight x ≤ n - 1 := by
  unfold fullTree at hx
  split_ifs at hx with hn0
  · simp at hx
  · obtain ⟨hbw, hw⟩ := Finset.mem_filter.mp hx
    exact ⟨positive_of_mem_boundedWords (n - 1) (n - 1) hbw, hw⟩

lemma nil_mem_chain : ∀ x : Node, [] ∈ chain x
  | [] => by simp [chain]
  | _ :: _ => by simp [chain]

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

lemma rank_lt_card {T : Finset Node} {x : Node} (hx : x ∈ T) :
    rank T x < T.card := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨x, hx, by simp [preLt_irrefl x]⟩

lemma rank_strict_mono {T : Finset Node} {x y : Node}
    (hx : x ∈ T) (_hy : y ∈ T) (hxy : PreLt x y) :
    rank T x < rank T y := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩, by simp [preLt_irrefl x]⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, preLt_trans hz.2 hxy⟩

lemma rank_inj {T : Finset Node} {x y : Node}
    (hx : x ∈ T) (hy : y ∈ T) (heq : rank T x = rank T y) : x = y := by
  rcases preLt_trichotomy x y with hlt | rfl | hgt
  · have := rank_strict_mono hx hy hlt; omega
  · rfl
  · have := rank_strict_mono hy hx hgt; omega

lemma rank_lt_iff {T : Finset Node} {x y : Node} (hx : x ∈ T) (hy : y ∈ T) :
    rank T x < rank T y ↔ PreLt x y := by
  constructor
  · intro hlt
    rcases preLt_trichotomy x y with h | rfl | h
    · exact h
    · omega
    · have := rank_strict_mono hy hx h; omega
  · exact rank_strict_mono hx hy

lemma image_rank_eq_range (T : Finset Node) :
    T.image (rank T) = Finset.range T.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_range.mpr (rank_lt_card hx)
  · rw [Finset.card_range, Finset.card_image_of_injOn]
    intro x hx y hy heq
    exact rank_inj hx hy heq

lemma rank_of_last {T : Finset Node} {x : Node} (hl : Last T x) :
    rank T x = T.card - 1 := by
  unfold rank
  have hflt : T.filter (PreLt · x) = T.erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hy, hlt⟩
      exact ⟨fun heq => preLt_irrefl x (heq ▸ hlt), hy⟩
    · rintro ⟨hne, hy⟩
      refine ⟨hy, ?_⟩
      rcases hl.2 y hy with rfl | hlt
      · exact absurd rfl hne
      · exact hlt
  rw [hflt, Finset.card_erase_of_mem hl.1]

lemma rank_insert_of_notMem {T : Finset Node} {z w : Node}
    (hz : z ∉ T) (hw : w ∈ T) :
    rank (insert z T) w = if PreLt w z then rank T w else rank T w + 1 := by
  unfold rank
  have hzne : z ≠ w := fun h => hz (h ▸ hw)
  by_cases hwz : PreLt w z
  · rw [if_pos hwz]
    have hzw : ¬ PreLt z w := preLt_asymm hwz
    have hflt : (insert z T).filter (PreLt · w) = T.filter (PreLt · w) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      exact ⟨fun ⟨hu, hlt⟩ => ⟨hu.resolve_left (fun h => hzw (h ▸ hlt)), hlt⟩,
             fun ⟨hu, hlt⟩ => ⟨Or.inr hu, hlt⟩⟩
    rw [hflt]
  · rw [if_neg hwz]
    have hzw : PreLt z w := by
      rcases preLt_trichotomy w z with h | rfl | h
      · exact absurd h hwz
      · exact absurd rfl hzne.symm
      · exact h
    have hflt : (insert z T).filter (PreLt · w) = insert z (T.filter (PreLt · w)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hu, hlt⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hu, hlt⟩
      · rintro (rfl | ⟨hu, hlt⟩)
        · exact ⟨Or.inl rfl, hzw⟩
        · exact ⟨Or.inr hu, hlt⟩
    rw [hflt, Finset.card_insert_of_notMem (by simp [hz])]

/-! ### `enumerateNodes` -/

lemma enumerateNodes_props (D : Finset Node) :
    (enumerateNodes D).Perm D.toList ∧
    (enumerateNodes D).Nodup ∧
    (enumerateNodes D).length = D.card ∧
    (enumerateNodes D).toFinset = D ∧
    (enumerateNodes D).Pairwise PreLt := by
  let rel : Node → Node → Prop := fun x y => x = y ∨ PreLt x y
  have hperm : (enumerateNodes D).Perm D.toList :=
    List.mergeSort_perm D.toList (fun x y => decide (rel x y))
  have hnodup : (enumerateNodes D).Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList D)
  have hlen : (enumerateNodes D).length = D.card := by
    rw [hperm.length_eq, Finset.length_toList]
  have hfin : (enumerateNodes D).toFinset = D := by
    ext z
    simp [hperm.mem_iff]
  have : Std.Total rel := ⟨fun x y => by
    rcases preLt_trichotomy x y with h | rfl | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr h)⟩
  have : IsTrans Node rel := ⟨fun x y z h1 h2 => by
    rcases h1 with rfl | h1
    · exact h2
    · rcases h2 with rfl | h2
      · exact Or.inr h1
      · exact Or.inr (preLt_trans h1 h2)⟩
  have hpw_le : (enumerateNodes D).Pairwise rel :=
    List.pairwise_mergeSort' rel D.toList
  have hpw : (enumerateNodes D).Pairwise PreLt := by
    have hnodup' : (enumerateNodes D).Pairwise (· ≠ ·) := hnodup
    rw [List.pairwise_iff_getElem] at hpw_le hnodup' ⊢
    intro i j hi hj hij
    have h1 := hpw_le i j hi hj hij
    have h2 := hnodup' i j hi hj hij
    exact h1.resolve_left h2
  exact ⟨hperm, hnodup, hlen, hfin, hpw⟩

lemma getElem_take_eq {α : Type} (L : List α) {i k : ℕ}
    (hk_tk : k < (L.take i).length) :
    k < i ∧ k < L.length ∧ (L.take i)[k] = L[k]'(by simp at hk_tk; omega) := by
  simp only [List.length_take] at hk_tk
  exact ⟨by omega, by omega, List.getElem_take⟩

/-! ### Valid History & Canonical Tree Helpers -/

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

lemma exists_own_of_mem_label {Q : Type} {H : TreeData Q} (_hv : Valid H)
    {u : Node} (hu : u ∈ H.nodes) {q : Q} (hq : q ∈ H.label u) :
    ∃ x ∈ H.nodes, u.IsPrefix x ∧ q ∈ own H x := by
  let S := H.nodes.filter (fun z => u.IsPrefix z ∧ q ∈ H.label z)
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨hu, List.prefix_refl u, hq⟩
  obtain ⟨x, hxS, hm_sup⟩ := Finset.exists_mem_eq_sup S ⟨u, huS⟩ List.length
  have hx_mem : x ∈ H.nodes := (Finset.mem_filter.mp hxS).1
  have hux : u.IsPrefix x := (Finset.mem_filter.mp hxS).2.1
  have hqx : q ∈ H.label x := (Finset.mem_filter.mp hxS).2.2
  refine ⟨x, hx_mem, hux, (mem_own_iff H x q).mpr ⟨hqx, ?_⟩⟩
  intro hch
  obtain ⟨y, hy_ch, hqy⟩ := Finset.mem_biUnion.mp hch
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hy_mem, j, rfl⟩ := hy_ch
  have huy : u.IsPrefix (x ++ [j]) := hux.trans ⟨[j], rfl⟩
  have hyS : x ++ [j] ∈ S := Finset.mem_filter.mpr ⟨hy_mem, huy, hqy⟩
  have hle : (x ++ [j]).length ≤ S.sup List.length := Finset.le_sup (f := List.length) hyS
  rw [hm_sup] at hle
  simp at hle

lemma owner_eq_of_own {Q : Type} {H : TreeData Q} (hv : Valid H)
    {u : Node} (hu : u ∈ H.nodes) {p : Q} (hp : p ∈ own H u) :
    owner H p = u := by
  unfold owner
  have hex : ∃ x ∈ H.nodes, p ∈ own H x := ⟨u, hu, hp⟩
  rw [dif_pos hex]
  obtain ⟨hw, hp_w⟩ := Classical.choose_spec hex
  by_contra hne
  exact Finset.disjoint_left.mp (own_disjoint hv hw hu hne) hp_w hp

lemma stateAt_val_of_lt {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : k < n) :
    (stateAt n hn k).val = k :=
  Nat.mod_eq_of_lt hk

lemma htree_some_iff (n : ℕ) (T : Finset Node) (H : History (Fin n)) :
    Htree n T = some H ↔ H.val = canonicalData n T := by
  unfold Htree asHistory
  split_ifs with hv
  · simp [Subtype.ext_iff, eq_comm]
  · constructor
    · intro h; cases h
    · intro heq; exact absurd (heq ▸ H.property) hv

lemma canonical_stateSet (n : ℕ) {T : Finset Node} (hroot : [] ∈ T) :
    stateSet (canonicalData n T) = canonicalStates n T := by
  ext q
  simp only [stateSet, canonicalData, hroot, ↓reduceIte, canonicalStates, Finset.mem_filter,
    Finset.mem_univ, true_and, List.nil_prefix]
  constructor
  · rintro ⟨y, hy, hq⟩
    rw [hq]
    exact rank_lt_card hy
  · intro hlt
    have hm : q.val ∈ Finset.range T.card := Finset.mem_range.mpr hlt
    rw [← image_rank_eq_range T] at hm
    obtain ⟨y, hy, hq⟩ := Finset.mem_image.mp hm
    exact ⟨y, hy, hq.symm⟩

lemma canonical_own {n : ℕ} (hn : 1 ≤ n) {T : Finset Node}
    (hord : Ordered T) (hcard : T.card ≤ n) {u : Node} (hu : u ∈ T) :
    own (canonicalData n T) u = {stateAt n hn (rank T u)} := by
  ext q
  rw [mem_own_iff]
  simp only [childLabels, children, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_singleton]
  have hrk_lt : rank T u < n := lt_of_lt_of_le (rank_lt_card hu) hcard
  constructor
  · rintro ⟨hqu, hno_ch⟩
    simp only [canonicalData, hu, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hqu
    obtain ⟨y, hyT, huy, hqval⟩ := hqu
    by_cases hyu : y = u
    · subst hyu
      apply Fin.ext
      rw [hqval, stateAt_val_of_lt hn hrk_lt]
    · exfalso
      obtain ⟨w, rfl⟩ := huy
      cases w with
      | nil => exact hyu (by simp)
      | cons j rest =>
        have hujT : u ++ [j] ∈ T := hord.2.1 (u ++ j :: rest) hyT (u ++ [j]) ⟨rest, by simp⟩
        apply hno_ch
        refine ⟨u ++ [j], ⟨hujT, j, rfl⟩, ?_⟩
        simp only [canonicalData, hujT, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨u ++ j :: rest, hyT, ⟨rest, by simp⟩, hqval⟩
  · rintro rfl
    have hval : (stateAt n hn (rank T u)).val = rank T u := stateAt_val_of_lt hn hrk_lt
    refine ⟨?_, ?_⟩
    · simp only [canonicalData, hu, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨u, hu, List.prefix_refl u, hval⟩
    · rintro ⟨w, ⟨hwT, j, rfl⟩, hqw⟩
      change u ++ [j] ∈ T at hwT
      change stateAt n hn (rank T u) ∈ (canonicalData n T).label (u ++ [j]) at hqw
      simp only [canonicalData, if_pos hwT, Finset.mem_filter, Finset.mem_univ, true_and] at hqw
      obtain ⟨y, hyT, hujy, hval_y⟩ := hqw
      have hy_eq : y = u := rank_inj hyT hu (hval_y.symm.trans hval)
      subst hy_eq
      have hlen := hujy.length_le
      simp at hlen

lemma canonical_simple {n : ℕ} (hn : 1 ≤ n) {T : Finset Node}
    (hord : Ordered T) (hcard : T.card ≤ n) {H : History (Fin n)}
    (hH : H.val = canonicalData n T) : Simple H := by
  intro u hu
  rw [hH] at hu ⊢
  change u ∈ T at hu
  rw [canonical_own hn hord hcard hu, Finset.card_singleton]

lemma canonical_leaf_label {n : ℕ} (hn : 1 ≤ n) {T : Finset Node}
    (hord : Ordered T) (hcard : T.card ≤ n) {u : Node} (hleaf : Leaf T u) :
    (canonicalData n T).label u = {stateAt n hn (rank T u)} := by
  have hu : u ∈ T := hleaf.1
  have hrk_lt : rank T u < n := lt_of_lt_of_le (rank_lt_card hu) hcard
  ext q
  simp only [canonicalData, hu, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨y, hyT, huy, hqval⟩
    obtain ⟨w, rfl⟩ := huy
    cases w with
    | nil =>
      simp only [List.append_nil] at hqval
      apply Fin.ext
      rw [hqval, stateAt_val_of_lt hn hrk_lt]
    | cons j rest =>
      exfalso
      have huj_T : u ++ [j] ∈ T := hord.2.1 (u ++ j :: rest) hyT (u ++ [j]) ⟨rest, by simp⟩
      have huj_ch : u ++ [j] ∈ children T u := by simp [children, huj_T]
      rw [hleaf.2] at huj_ch
      simp at huj_ch
  · rintro rfl
    exact ⟨u, hu, List.prefix_refl u, stateAt_val_of_lt hn hrk_lt⟩

/-! ### `restoringLetter` universal lemma -/

lemma effect_restoringLetter {n : ℕ} (hn : 1 ≤ n) {T : Finset Node}
    (hcard_lt : T.card < n) (M : History (Fin n)) (hM_simp : Simple M)
    (hM_nodes : M.val.nodes = T) {H_T : History (Fin n)}
    (hHT : H_T.val = canonicalData n T) :
    ∃ H', successor (fullBuchi n hn) M (restoringLetter n T M.val) = some H' ∧
      H' = H_T ∧
      acceptingNodes (fullBuchi n hn) M (restoringLetter n T M.val) = ∅ ∧
      unstable (fullBuchi n hn) M (restoringLetter n T M.val) = ∅ := by
  have hv := M.property
  let π : Fin n → Fin n := fun q => stateAt n hn (rank T (owner M.val q))
  have hmem_stateSet : ∀ q, q ∈ stateSet M.val ↔ ∃ u ∈ T, q ∈ own M.val u := by
    intro q
    constructor
    · intro hq
      obtain ⟨u, hu, _, hown⟩ := exists_own_of_mem_label hv hv.2.1 hq
      exact ⟨u, hM_nodes ▸ hu, hown⟩
    · rintro ⟨u, huT, hown⟩
      have hu : u ∈ M.val.nodes := hM_nodes.symm ▸ huT
      exact label_sub_of_prefix hv [] u (by simpa using hu) ((mem_own_iff M.val u q).mp hown).1
  have hlet_eq : restoringLetter n T M.val = permLetter (stateSet M.val) π := by
    ext ⟨q1, q2⟩
    simp only [restoringLetter, permLetter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨u, huT, hown, hq2val⟩
      have huM : u ∈ M.val.nodes := hM_nodes.symm ▸ huT
      have hown_eq : owner M.val q1 = u := owner_eq_of_own hv huM hown
      have hq1P : q1 ∈ stateSet M.val := (hmem_stateSet q1).mpr ⟨u, huT, hown⟩
      refine ⟨q1, hq1P, rfl, ?_⟩
      apply Fin.ext
      simp only [π, hown_eq, stateAt_val_of_lt hn (lt_trans (rank_lt_card huT) hcard_lt), hq2val]
    · rintro ⟨q, hqP, rfl, rfl⟩
      obtain ⟨u, huT, hown⟩ := (hmem_stateSet q).mp hqP
      have huM : u ∈ M.val.nodes := hM_nodes.symm ▸ huT
      have hown_eq : owner M.val q = u := owner_eq_of_own hv huM hown
      refine ⟨u, huT, hown, ?_⟩
      simp only [π, hown_eq, stateAt_val_of_lt hn (lt_trans (rank_lt_card huT) hcard_lt)]
  have hinj : Set.InjOn π {q | q ∈ stateSet M.val} := by
    intro q1 hq1 q2 hq2 heq
    obtain ⟨u1, hu1T, hown1⟩ := (hmem_stateSet q1).mp hq1
    obtain ⟨u2, hu2T, hown2⟩ := (hmem_stateSet q2).mp hq2
    have hu1M : u1 ∈ M.val.nodes := hM_nodes.symm ▸ hu1T
    have hu2M : u2 ∈ M.val.nodes := hM_nodes.symm ▸ hu2T
    have ho1 : owner M.val q1 = u1 := owner_eq_of_own hv hu1M hown1
    have ho2 : owner M.val q2 = u2 := owner_eq_of_own hv hu2M hown2
    have hrk_eq : rank T u1 = rank T u2 := by
      have hv_eq := congrArg Fin.val heq
      simpa [π, ho1, ho2,
        stateAt_val_of_lt hn (lt_trans (rank_lt_card hu1T) hcard_lt),
        stateAt_val_of_lt hn (lt_trans (rank_lt_card hu2T) hcard_lt)] using hv_eq
    have hu_eq : u1 = u2 := rank_inj hu1T hu2T hrk_eq
    subst hu_eq
    have hcard1 : (own M.val u1).card = 1 := hM_simp u1 hu1M
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    rw [ha] at hown1 hown2
    simp only [Finset.mem_singleton] at hown1 hown2
    exact hown1.trans hown2.symm
  have havoid : ∀ q ∈ stateSet M.val, π q ≠ lastState n hn := by
    intro q hq heq
    obtain ⟨u, huT, hown⟩ := (hmem_stateSet q).mp hq
    have ho : owner M.val q = u := owner_eq_of_own hv (hM_nodes.symm ▸ huT) hown
    have hval := congrArg Fin.val heq
    simp only [π, ho, stateAt_val_of_lt hn (lt_trans (rank_lt_card huT) hcard_lt),
      lastState] at hval
    have := rank_lt_card huT
    omega
  have heff := (lemma_38 n hn M hM_simp).2.1 π hinj havoid
  rw [← hlet_eq] at heff
  obtain ⟨H', hsucc, hval, _, hacc, hunst⟩ := heff
  have hmap_eq : mapData M.val π = canonicalData n T := by
    have hnodes : (mapData M.val π).nodes = (canonicalData n T).nodes := hM_nodes
    have hlbl : (mapData M.val π).label = (canonicalData n T).label := by
      funext u
      by_cases huT : u ∈ T
      · have huM : u ∈ M.val.nodes := hM_nodes.symm ▸ huT
        ext q
        simp only [mapData, canonicalData, huT, ↓reduceIte, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨q0, hq0_lbl, rfl⟩
          obtain ⟨y, hyM, huy, hown_y⟩ := exists_own_of_mem_label hv huM hq0_lbl
          have hyT : y ∈ T := hM_nodes ▸ hyM
          have ho : owner M.val q0 = y := owner_eq_of_own hv hyM hown_y
          refine ⟨y, hyT, huy, ?_⟩
          simp [π, ho, stateAt_val_of_lt hn (lt_trans (rank_lt_card hyT) hcard_lt)]
        · rintro ⟨y, hyT, huy, hqval⟩
          have hyM : y ∈ M.val.nodes := hM_nodes.symm ▸ hyT
          have hcard1 : (own M.val y).card = 1 := hM_simp y hyM
          obtain ⟨q0, hq0_eq⟩ := Finset.card_eq_one.mp hcard1
          have hq0_own : q0 ∈ own M.val y := by simp [hq0_eq]
          have hq0_y : q0 ∈ M.val.label y := ((mem_own_iff M.val y q0).mp hq0_own).1
          have ho : owner M.val q0 = y := owner_eq_of_own hv hyM hq0_own
          obtain ⟨w, rfl⟩ := huy
          have hq0_u : q0 ∈ M.val.label u :=
            label_sub_of_prefix hv u w hyM hq0_y
          refine ⟨q0, hq0_u, ?_⟩
          apply Fin.ext
          simp [π, ho, stateAt_val_of_lt hn (lt_trans (rank_lt_card hyT) hcard_lt), hqval]
      · have huM : u ∉ M.val.nodes := hM_nodes ▸ huT
        simp [mapData, canonicalData, huT, hv.2.2.1 u huM]
    cases h1 : mapData M.val π with
    | mk n1 l1 =>
      cases h2 : canonicalData n T with
      | mk n2 l2 =>
        rw [h1, h2] at hnodes hlbl
        cases hnodes; cases hlbl; rfl
  have hH'_eq : H' = H_T := Subtype.ext (hval.trans (hmap_eq.trans hHT.symm))
  exact ⟨H', hsucc, hH'_eq, hacc, hunst⟩

/-! ### `readWord`, `wordEdges`, and `visited` combinatorics -/

lemma readWord_append {Q Sigma : Type} (B : NBW Q Sigma) :
    ∀ (u v : List Sigma) (H : Option (History Q)),
      readWord B H (u ++ v) = readWord B (readWord B H u) v
  | [], _, _ => rfl
  | σ :: u, v, H => readWord_append B u v (H.bind fun h => successor B h σ)

lemma take_append_of_le {α : Type} (u v : List α) {i : ℕ} (hi : i ≤ u.length) :
    (u ++ v).take i = u.take i := by
  induction u generalizing i with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    subst hi0; simp
  | cons a u ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.cons_append, List.take_succ_cons]
      exact congrArg (a :: ·) (ih (by simpa using hi))

lemma take_append_add {α : Type} (u v : List α) (j : ℕ) :
    (u ++ v).take (u.length + j) = u ++ v.take j := by
  induction u with
  | nil => simp
  | cons a u ih =>
    simp only [List.length_cons, Nat.succ_add, List.cons_append, List.take_succ_cons]
    exact congrArg (a :: ·) ih

lemma wordEdges_append {Q Sigma : Type} (B : NBW Q Sigma)
    {H : Option (History Q)} {u v : List Sigma} {K : History Q}
    (hu : readWord B H u = some K) :
    wordEdges B H (u ++ v) = wordEdges B H u ∪ wordEdges B (some K) v := by
  ext e
  simp only [wordEdges, Set.mem_union, Set.mem_ofPred]
  constructor
  · rintro ⟨i, hread, hlet, hsucc⟩
    simp only [Fin.getElem_fin] at hlet
    by_cases hlt : i.val < u.length
    · left
      refine ⟨⟨i.val, hlt⟩, ?_, ?_, hsucc⟩
      · rwa [take_append_of_le u v (Nat.le_of_lt hlt)] at hread
      · simp only [Fin.getElem_fin]
        rwa [List.getElem_append_left hlt] at hlet
    · right
      have hge : u.length ≤ i.val := Nat.le_of_not_lt hlt
      have hj : i.val - u.length < v.length := by
        have := i.isLt; simp at this; omega
      refine ⟨⟨i.val - u.length, hj⟩, ?_, ?_, hsucc⟩
      · have heq : i.val = u.length + (i.val - u.length) := by omega
        rw [heq, take_append_add, readWord_append, hu] at hread
        exact hread
      · simp only [Fin.getElem_fin]
        rwa [List.getElem_append_right hge] at hlet
  · rintro (⟨i, hread, hlet, hsucc⟩ | ⟨j, hread, hlet, hsucc⟩)
    · simp only [Fin.getElem_fin] at hlet
      have hi : i.val < (u ++ v).length := by simp; omega
      refine ⟨⟨i.val, hi⟩, ?_, ?_, hsucc⟩
      · rwa [take_append_of_le u v (Nat.le_of_lt i.isLt)]
      · simp only [Fin.getElem_fin]
        rw [List.getElem_append_left i.isLt]
        exact hlet
    · simp only [Fin.getElem_fin] at hlet
      have hj : u.length + j.val < (u ++ v).length := by simp
      refine ⟨⟨u.length + j.val, hj⟩, ?_, ?_, hsucc⟩
      · rw [take_append_add, readWord_append, hu]; exact hread
      · simp only [Fin.getElem_fin]
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simpa [Nat.add_sub_cancel_left] using hlet

lemma wordEdges_nil {Q Sigma : Type} (B : NBW Q Sigma) (H : Option (History Q)) :
    wordEdges B H [] = ∅ := by
  ext e
  simp [wordEdges]

lemma wordEdges_singleton {Q Sigma : Type} (B : NBW Q Sigma)
    {H H' : History Q} {σ : Sigma} (h : successor B H σ = some H') :
    wordEdges B (some H) [σ] = {(H, σ, H')} := by
  ext ⟨e1, e2, e3⟩
  simp only [wordEdges, Set.mem_ofPred, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨i, hi⟩, hread, hlet, hsucc⟩
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simp [readWord] at hread hlet
    rcases hread with rfl
    rcases hlet with rfl
    rw [h] at hsucc
    exact ⟨rfl, rfl, Option.some.inj hsucc.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨⟨0, by simp⟩, rfl, rfl, h⟩

lemma readWord_pair {Q Sigma : Type} (B : NBW Q Sigma)
    {H H1 H2 : History Q} {σ1 σ2 : Sigma}
    (h1 : successor B H σ1 = some H1) (h2 : successor B H1 σ2 = some H2) :
    readWord B (some H) [σ1, σ2] = some H2 := by
  change readWord B (successor B H σ1) [σ2] = some H2
  rw [h1]
  exact h2

lemma wordEdges_pair {Q Sigma : Type} (B : NBW Q Sigma)
    {H H1 H2 : History Q} {σ1 σ2 : Sigma}
    (h1 : successor B H σ1 = some H1) (h2 : successor B H1 σ2 = some H2) :
    wordEdges B (some H) [σ1, σ2] = {(H, σ1, H1), (H1, σ2, H2)} := by
  have heq : ([σ1, σ2] : List Sigma) = [σ1] ++ [σ2] := rfl
  have hr1 : readWord B (some H) [σ1] = some H1 := by simpa [readWord] using h1
  rw [heq, wordEdges_append B hr1, wordEdges_singleton B h1, wordEdges_singleton B h2]
  ext e
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-! ### `acceptingWord` analysis -/

lemma acceptingWord_props (n : ℕ) (hn : 1 ≤ n) {x : Node} (hx_ft : x ∈ fullTree n) :
    ∃ Hx : History (Fin n),
      Htree n (chain x) = some Hx ∧
      ClosedWalk (fullBuchi n hn) Hx (acceptingWord n hn x) ∧
      (∀ e ∈ Acycle n hn x, unst (fullBuchi n hn) e = ∅) ∧
      (∃ e ∈ Acycle n hn x, x ∈ acc (fullBuchi n hn) e) := by
  let F := fullBuchi n hn
  let T := chain x
  obtain ⟨hpx, hwx⟩ := mem_fullTree_props hx_ft
  have hf30 := fact_30 x x hpx hpx
  have hlast : Last T x := hf30.2.1
  have hord : Ordered T := hf30.2.2.2.2.1
  have hleaf : Leaf T x := (hf30.2.2.2.2.2.2.2.2 T x hord hlast).1
  have hne : T.Nonempty := ⟨[], nil_mem_chain x⟩
  have hcard : T.card ≤ n := by rw [card_chain_eq x hpx]; omega
  have hcard_pos : 1 ≤ T.card := Finset.card_pos.mpr hne
  obtain ⟨Hx, hHx_tree, hHx_reach⟩ := lemma_39 n hn T hord hne hcard
  have hHx_val : Hx.val = canonicalData n T := (htree_some_iff n T Hx).mp hHx_tree
  have hHx_simp : Simple Hx := canonical_simple hn hord hcard hHx_val
  let P := canonicalStates n T
  have hP_eq : stateSet Hx.val = P := by rw [hHx_val, canonical_stateSet n (nil_mem_chain x)]
  let s := stateAt n hn (T.card - 1)
  have hrk_x : rank T x = T.card - 1 := rank_of_last hlast
  have hHx_lbl_x : Hx.val.label x = {s} := by
    rw [hHx_val, canonical_leaf_label hn hord hcard hleaf, hrk_x]
  have hHx_leaf_x : Leaf Hx.val.nodes x := by rw [hHx_val]; exact hleaf
  refine ⟨Hx, hHx_tree, ?_⟩
  by_cases hlt : T.card < n
  · -- 2-step acceptingWord
    let σ1 := accLetter hn P s
    let π2 : Fin n → Fin n := fun q => if q = lastState n hn then s else q
    let σ2 := permLetter (insert (lastState n hn) (P.erase s)) π2
    have haw_eq : acceptingWord n hn x = [σ1, σ2] := by unfold acceptingWord; rw [if_pos hlt]
    let π1 : Fin n → Fin n := fun q => if q = s then lastState n hn else q
    have hs_mem_P : s ∈ P := by
      simp only [P, canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [stateAt_val_of_lt hn (by omega)]
      omega
    have hlast_not_P : lastState n hn ∉ P := by
      simp only [P, canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and, lastState]
      omega
    have hs_ne_last : s ≠ lastState n hn := fun h => hlast_not_P (h ▸ hs_mem_P)
    have hσ1_perm : σ1 = permLetter (stateSet Hx.val) π1 := by
      rw [hP_eq]
      ext ⟨a, b⟩
      simp only [σ1, accLetter, idLetter, permLetter, Finset.mem_insert, Finset.mem_image,
        Finset.mem_erase, Prod.mk.injEq, π1]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨q, ⟨hqne, hqP⟩, rfl, rfl⟩)
        · exact ⟨s, hs_mem_P, rfl, by simp⟩
        · exact ⟨q, hqP, rfl, if_neg hqne⟩
      · rintro ⟨q, hqP, rfl, rfl⟩
        by_cases hqs : q = s
        · subst hqs; exact Or.inl ⟨rfl, by simp⟩
        · exact Or.inr ⟨q, ⟨hqs, hqP⟩, rfl, by simp [hqs]⟩
    have hinj1 : Set.InjOn π1 {q | q ∈ stateSet Hx.val} := by
      intro q1 hq1 q2 hq2 heq
      change q1 ∈ stateSet Hx.val at hq1
      change q2 ∈ stateSet Hx.val at hq2
      rw [hP_eq] at hq1 hq2
      by_cases h1 : q1 = s
      · by_cases h2 : q2 = s
        · exact h1.trans h2.symm
        · simp [π1, h1, h2] at heq
          exact absurd (heq ▸ hq2) hlast_not_P
      · by_cases h2 : q2 = s
        · simp [π1, h1, h2] at heq
          exact absurd (heq.symm ▸ hq1) hlast_not_P
        · simpa [π1, h1, h2] using heq
    have heff1 := (lemma_38 n hn Hx hHx_simp).2.2.1 x s π1 hHx_leaf_x hHx_lbl_x hinj1 (by simp [π1])
    rw [← hσ1_perm] at heff1
    obtain ⟨H1, hsucc1, hH1_val, hH1_simp, hacc1, hunst1⟩ := heff1
    have hH1_stateSet : stateSet H1.val = insert (lastState n hn) (P.erase s) := by
      unfold stateSet
      rw [hH1_val]
      ext q
      rw [mem_mapData_iff]
      change (∃ q0 ∈ stateSet Hx.val, π1 q0 = q) ↔ _
      rw [hP_eq]
      simp only [Finset.mem_insert, Finset.mem_erase, π1]
      constructor
      · rintro ⟨q0, hq0P, rfl⟩
        by_cases hq0s : q0 = s
        · subst hq0s; simp
        · rw [if_neg hq0s]; exact Or.inr ⟨hq0s, hq0P⟩
      · rintro (rfl | ⟨hqne, hqP⟩)
        · exact ⟨s, hs_mem_P, by simp⟩
        · exact ⟨q, hqP, if_neg hqne⟩
    have hinj2 : Set.InjOn π2 {q | q ∈ stateSet H1.val} := by
      intro q1 hq1 q2 hq2 heq
      change q1 ∈ stateSet H1.val at hq1
      change q2 ∈ stateSet H1.val at hq2
      rw [hH1_stateSet] at hq1 hq2
      simp only [Finset.mem_insert, Finset.mem_erase] at hq1 hq2
      rcases hq1 with rfl | ⟨hq1_nes, hq1P⟩
      · rcases hq2 with rfl | ⟨hq2_nes, hq2P⟩
        · rfl
        · have h2ne : q2 ≠ lastState n hn := fun h => hlast_not_P (h ▸ hq2P)
          simp [π2, h2ne] at heq
          exact absurd heq.symm hq2_nes
      · have h1ne : q1 ≠ lastState n hn := fun h => hlast_not_P (h ▸ hq1P)
        rcases hq2 with rfl | ⟨_, hq2P⟩
        · simp [π2, h1ne] at heq
          exact absurd heq hq1_nes
        · have h2ne : q2 ≠ lastState n hn := fun h => hlast_not_P (h ▸ hq2P)
          simpa [π2, h1ne, h2ne] using heq
    have havoid2 : ∀ q ∈ stateSet H1.val, π2 q ≠ lastState n hn := by
      intro q hq
      rw [hH1_stateSet] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq_er
      · simp [π2, hs_ne_last]
      · obtain ⟨_, hqP⟩ := Finset.mem_erase.mp hq_er
        have hqne : q ≠ lastState n hn := fun h => hlast_not_P (h ▸ hqP)
        simp [π2, hqne]
    have heff2 := (lemma_38 n hn H1 hH1_simp).2.1 π2 hinj2 havoid2
    rw [hH1_stateSet] at heff2
    obtain ⟨H2, hsucc2, hH2_val, _, hacc2, hunst2⟩ := heff2
    have hH2_eq : H2 = Hx := by
      apply Subtype.ext
      rw [hH2_val, hH1_val]
      have hlbl_eq : (mapData (mapData Hx.val π1) π2).label = Hx.val.label := by
        funext u
        ext q
        rw [mem_mapData_iff]
        simp only [mem_mapData_iff]
        by_cases hu : u ∈ Hx.val.nodes
        · have hsub_u : Hx.val.label u ⊆ P := by
            rw [← hP_eq]
            exact label_sub_of_prefix Hx.property [] u (by simpa using hu)
          constructor
          · rintro ⟨_, ⟨q0, hq0u, rfl⟩, rfl⟩
            have hq0P : q0 ∈ P := hsub_u hq0u
            by_cases hq0s : q0 = s
            · subst hq0s; simpa [π1, π2] using hq0u
            · have hq0_last : q0 ≠ lastState n hn := fun h => hlast_not_P (h ▸ hq0P)
              simpa [π1, π2, hq0s, hq0_last] using hq0u
          · intro hqu
            have hqP : q ∈ P := hsub_u hqu
            refine ⟨π1 q, ⟨q, hqu, rfl⟩, ?_⟩
            by_cases hqs : q = s
            · subst hqs; simp [π1, π2]
            · have hq_last : q ≠ lastState n hn := fun h => hlast_not_P (h ▸ hqP)
              simp [π1, π2, hqs, hq_last]
        · simp [Hx.property.2.2.1 u hu]
      exact treeData_ext rfl hlbl_eq
    rw [hH2_eq] at hsucc2
    have hread : readWord F (some Hx) [σ1, σ2] = some Hx :=
      readWord_pair F hsucc1 hsucc2
    have hcw : ClosedWalk F Hx (acceptingWord n hn x) := by
      rw [haw_eq]
      exact ⟨by simp, hHx_reach, hread⟩
    have hedges : Acycle n hn x = {(Hx, σ1, H1), (H1, σ2, Hx)} := by
      unfold Acycle
      rw [hHx_tree, haw_eq, wordEdges_pair F hsucc1 hsucc2]
    refine ⟨hcw, ?_, ?_⟩
    · intro e he
      rw [hedges] at he
      rcases he with rfl | rfl
      · exact hunst1
      · exact hunst2
    · refine ⟨(Hx, σ1, H1), ?_, ?_⟩
      · rw [hedges]; simp
      · simp [acc, hacc1]
  · -- 1-step self-loop acceptingWord (T.card = n)
    have hcard_eq : T.card = n := by omega
    have haw_eq : acceptingWord n hn x = [idLetter P] := by
      unfold acceptingWord; rw [if_neg hlt]
    have hs_eq_last : s = lastState n hn := by
      apply Fin.ext
      have hlt_n : n - 1 < n := by omega
      change (stateAt n hn (T.card - 1)).val = n - 1
      rw [hcard_eq, stateAt_val_of_lt hn hlt_n]
    have hid_perm : idLetter P = permLetter (stateSet Hx.val) id := by
      rw [hP_eq]; rfl
    have heff := (lemma_38 n hn Hx hHx_simp).2.2.1 x s id hHx_leaf_x hHx_lbl_x
      (fun _ _ _ _ h => h) (by simp [hs_eq_last])
    rw [← hid_perm] at heff
    obtain ⟨H1, hsucc1, hH1_val, _, hacc1, hunst1⟩ := heff
    have hH1_eq : H1 = Hx := by
      apply Subtype.ext
      rw [hH1_val]
      have hlbl_eq : (mapData Hx.val id).label = Hx.val.label := by
        funext u; ext q; rw [mem_mapData_iff]; simp
      exact treeData_ext rfl hlbl_eq
    rw [hH1_eq] at hsucc1
    have hcw : ClosedWalk F Hx (acceptingWord n hn x) := by
      rw [haw_eq]
      exact ⟨by simp, hHx_reach, by simpa [readWord] using hsucc1⟩
    have hedges : Acycle n hn x = {(Hx, idLetter P, Hx)} := by
      unfold Acycle
      rw [hHx_tree, haw_eq, wordEdges_singleton F hsucc1]
    refine ⟨hcw, ?_, ?_⟩
    · intro e he
      rw [hedges] at he; subst he; exact hunst1
    · exact ⟨(Hx, idLetter P, Hx), by rw [hedges]; simp, by simp [acc, hacc1]⟩

/-! ### Intermediate Trees `U_i` & Block Analysis -/

lemma intermediate_props {n : ℕ} (_hn : 1 ≤ n) {x y : Node}
    (hx_ft : x ∈ fullTree n) (hy_ft : y ∈ fullTree n)
    (hadj : (chain x ∪ chain y).card ≤ n) (_hy_not : y ∉ chain x) :
    let D := chain y \ chain x
    let L := enumerateNodes D
    let r := D.card
    (∀ i ≤ r, Ordered (intermediate x y i) ∧ (intermediate x y i).Nonempty ∧
      (intermediate x y i).card ≤ n) ∧
    intermediate x y 0 = chain x ∧
    intermediate x y r = chain x ∪ chain y ∧
    (∀ i (hi : i < r),
      let z := L[i]!
      let T := intermediate x y i
      let U := insert z T
      z = L[i]'(by rw [(enumerateNodes_props D).2.2.1]; exact hi) ∧
      z ∈ D ∧ z ∉ T ∧ U = intermediate x y (i + 1) ∧
      T.card < n ∧ U.card = T.card + 1 ∧ U.card ≤ n ∧
      z ≠ [] ∧ z.dropLast ∈ T ∧
      Leaf U z ∧ Youngest U z ∧
      z = z.dropLast ++ [degree T z.dropLast + 1]) := by
  intro D L r
  obtain ⟨hpx, _⟩ := mem_fullTree_props hx_ft
  obtain ⟨hpy, _⟩ := mem_fullTree_props hy_ft
  have hord_x : Ordered (chain x) := (fact_30 x x hpx hpx).2.2.2.2.1
  have hord_y : Ordered (chain y) := (fact_30 y y hpy hpy).2.2.2.2.1
  have hord_xy : Ordered (chain x ∪ chain y) := (fact_30 x y hpx hpy).2.2.2.2.2.2.1
  obtain ⟨hperm, hnodup, hL_len, hL_fin, hpw⟩ := enumerateNodes_props D
  have hsub_xy : ∀ i, intermediate x y i ⊆ chain x ∪ chain y := by
    intro i w hw
    rcases Finset.mem_union.mp hw with hwx | hwt
    · exact Finset.mem_union_left _ hwx
    · have hwL : w ∈ L := List.mem_of_mem_take (List.mem_toFinset.mp hwt)
      have hwD : w ∈ D := hL_fin ▸ List.mem_toFinset.mpr hwL
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hwD).1
  have hord_i : ∀ i ≤ r, Ordered (intermediate x y i) := by
    intro i hi
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      exact hord_xy.1 w (hsub_xy i hw)
    · intro w hw p hp
      rcases Finset.mem_union.mp hw with hwx | hwt
      · exact Finset.mem_union_left _ (hord_x.2.1 w hwx p hp)
      · by_cases hpeq : p = w
        · subst hpeq; exact hw
        · have hw_mem_tk : w ∈ L.take i := List.mem_toFinset.mp hwt
          obtain ⟨k, hk_lt_tk, hwk_eq⟩ := List.getElem_of_mem hw_mem_tk
          obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt_tk
          have hLk_w : L[k] = w := htk_k.symm.trans hwk_eq
          have hwk_D : L[k] ∈ D := hL_fin ▸ List.mem_toFinset.mpr (List.getElem_mem hk_lt_L)
          have hpy_mem : p ∈ chain y := hord_y.2.1 L[k] (Finset.mem_sdiff.mp hwk_D).1 p (hLk_w ▸ hp)
          by_cases hpx_mem : p ∈ chain x
          · exact Finset.mem_union_left _ hpx_mem
          · have hpD : p ∈ D := Finset.mem_sdiff.mpr ⟨hpy_mem, hpx_mem⟩
            have hpL : p ∈ L := List.mem_toFinset.mp (hL_fin.symm ▸ hpD)
            obtain ⟨m, hm_lt_L, hLm_p⟩ := List.getElem_of_mem hpL
            have hpre_lt : PreLt L[m] L[k] := Or.inl ⟨hLm_p.symm ▸ hLk_w.symm ▸ hp, hLm_p.symm ▸ hLk_w.symm ▸ hpeq⟩
            have hmk : m < k := by
              rcases lt_trichotomy m k with h | rfl | h
              · exact h
              · exact absurd hpre_lt (preLt_irrefl _)
              · exact absurd (List.pairwise_iff_getElem.mp hpw k m hk_lt_L hm_lt_L h) (preLt_asymm hpre_lt)
            refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
            have hm_lt_tk : m < (L.take i).length := by simp; omega
            obtain ⟨_, _, htk_m⟩ := getElem_take_eq L hm_lt_tk
            rw [← hLm_p, ← htk_m]
            exact List.getElem_mem hm_lt_tk
    · intro p a hpa b hb0 hble
      by_cases hba : b = a
      · subst hba; exact hpa
      · rcases Finset.mem_union.mp hpa with hpax | hpat
        · exact Finset.mem_union_left _ (hord_x.2.2 p a hpax b hb0 hble)
        · have hpa_tk : p ++ [a] ∈ L.take i := List.mem_toFinset.mp hpat
          obtain ⟨k, hk_lt_tk, hpak⟩ := List.getElem_of_mem hpa_tk
          obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt_tk
          have hLk_eq : L[k] = p ++ [a] := htk_k.symm.trans hpak
          have hLk_D : p ++ [a] ∈ D := hLk_eq ▸ (hL_fin ▸ List.mem_toFinset.mpr (List.getElem_mem hk_lt_L))
          have hpby : p ++ [b] ∈ chain y := hord_y.2.2 p a (Finset.mem_sdiff.mp hLk_D).1 b hb0 hble
          by_cases hpbx : p ++ [b] ∈ chain x
          · exact Finset.mem_union_left _ hpbx
          · have hpbD : p ++ [b] ∈ D := Finset.mem_sdiff.mpr ⟨hpby, hpbx⟩
            have hpbL : p ++ [b] ∈ L := List.mem_toFinset.mp (hL_fin.symm ▸ hpbD)
            obtain ⟨m, hm_lt_L, hLm_eq⟩ := List.getElem_of_mem hpbL
            have hpre_lt : PreLt L[m] L[k] := by
              rw [hLm_eq, hLk_eq]
              exact Or.inr ⟨p, b, a, [], [], rfl, rfl, by omega⟩
            have hmk : m < k := by
              rcases lt_trichotomy m k with h | rfl | h
              · exact h
              · exact absurd hpre_lt (preLt_irrefl _)
              · exact absurd (List.pairwise_iff_getElem.mp hpw k m hk_lt_L hm_lt_L h) (preLt_asymm hpre_lt)
            refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
            have hm_lt_tk : m < (L.take i).length := by simp; omega
            obtain ⟨_, _, htk_m⟩ := getElem_take_eq L hm_lt_tk
            rw [← hLm_eq, ← htk_m]
            exact List.getElem_mem hm_lt_tk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨hord_i i hi, ⟨[], Finset.mem_union_left _ (nil_mem_chain x)⟩, ?_⟩
    exact (Finset.card_le_card (hsub_xy i)).trans hadj
  · simp [intermediate]
  · unfold intermediate
    have htk_all : L.take r = L := List.take_of_length_le (le_of_eq hL_len)
    rw [htk_all, hL_fin]
    ext w
    simp only [Finset.mem_union, Finset.mem_sdiff, D]
    tauto
  · intro i hi
    have hiL : i < L.length := hL_len.symm ▸ hi
    let z := L[i]!
    let T := intermediate x y i
    let U := insert z T
    have hz_eq : z = L[i] := by
      simp [z, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hiL]
    have hzD : z ∈ D := by
      rw [hz_eq, ← hL_fin]
      exact List.mem_toFinset.mpr (List.getElem_mem hiL)
    have hz_not_T : z ∉ T := by
      intro hzT
      rcases Finset.mem_union.mp hzT with hzx | hztk
      · exact (Finset.mem_sdiff.mp hzD).2 hzx
      · have hmem_tk : L[i] ∈ L.take i := hz_eq ▸ List.mem_toFinset.mp hztk
        obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hmem_tk
        obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt
        have hk_eq' : L[k] = L[i] := htk_k.symm.trans hk_eq
        exact List.pairwise_iff_getElem.mp hnodup k i hk_lt_L hiL hk_lt_i hk_eq'
    have hU_eq : U = intermediate x y (i + 1) := by
      unfold U T intermediate
      have htk_succ : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem hiL
      rw [htk_succ, List.toFinset_append, ← hz_eq]
      ext w
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_singleton, Finset.mem_insert]
      tauto
    have hU_card_le : U.card ≤ n := by
      rw [hU_eq]
      exact (Finset.card_le_card (hsub_xy (i + 1))).trans hadj
    have hU_card : U.card = T.card + 1 := Finset.card_insert_of_notMem hz_not_T
    have hT_card_lt : T.card < n := by omega
    have hz_ne_nil : z ≠ [] := fun h => (Finset.mem_sdiff.mp hzD).2 (h ▸ nil_mem_chain x)
    have hpos_z : Positive z := hord_y.1 z (Finset.mem_sdiff.mp hzD).1
    let a := z.getLast hz_ne_nil
    have hz_split : z = z.dropLast ++ [a] := (List.dropLast_append_getLast hz_ne_nil).symm
    have ha_pos : 0 < a := hpos_z a (by rw [hz_split]; simp)
    have hord_U : Ordered U := by rw [hU_eq]; exact hord_i (i + 1) (by omega)
    have hdl_mem_T : z.dropLast ∈ T := by
      have hdl_U : z.dropLast ∈ U := hord_U.2.1 z (Finset.mem_insert_self z T) z.dropLast ⟨[a], hz_split.symm⟩
      rcases Finset.mem_insert.mp hdl_U with heq | hmem
      · exfalso
        have hl := congrArg List.length heq
        rw [hz_split] at hl; simp at hl
      · exact hmem
    have hleaf_U : Leaf U z := by
      refine ⟨Finset.mem_insert_self z T, ?_⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      simp only [children, Finset.mem_filter] at hw
      obtain ⟨hwU, c, rfl⟩ := hw
      have hw_ne_z : z ++ [c] ≠ z := by simp
      have hwT : z ++ [c] ∈ T := (Finset.mem_insert.mp hwU).resolve_left hw_ne_z
      rcases Finset.mem_union.mp hwT with hwcx | hwtk
      · exact (Finset.mem_sdiff.mp hzD).2 (hord_x.2.1 (z ++ [c]) hwcx z ⟨[c], rfl⟩)
      · obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hwtk)
        obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt
        have hk_eq' : L[k] = z ++ [c] := htk_k.symm.trans hk_eq
        have hlt1 : PreLt L[k] L[i] := List.pairwise_iff_getElem.mp hpw k i hk_lt_L hiL hk_lt_i
        rw [hk_eq', ← hz_eq] at hlt1
        have hlt2 : PreLt z (z ++ [c]) := Or.inl ⟨⟨[c], rfl⟩, by simp⟩
        exact preLt_asymm hlt2 hlt1
    have hno_larger_sib : ∀ c, z.dropLast ++ [c] ∈ U → c ≤ a := by
      intro c hcU
      by_contra hnot
      have hgt : a < c := by omega
      have hc_ne_z : z.dropLast ++ [c] ≠ z := by
        rw [hz_split]; intro h; have := (append_singleton_inj h).2; omega
      have hcT : z.dropLast ++ [c] ∈ T := (Finset.mem_insert.mp hcU).resolve_left hc_ne_z
      rcases Finset.mem_union.mp hcT with hcx | hctk
      · have hzx : z ∈ chain x := by
          rw [hz_split]
          exact hord_x.2.2 z.dropLast c hcx a ha_pos (Nat.le_of_lt hgt)
        exact (Finset.mem_sdiff.mp hzD).2 hzx
      · obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hctk)
        obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt
        have hk_eq' : L[k] = z.dropLast ++ [c] := htk_k.symm.trans hk_eq
        have hlt1 : PreLt L[k] L[i] := List.pairwise_iff_getElem.mp hpw k i hk_lt_L hiL hk_lt_i
        rw [hk_eq', ← hz_eq] at hlt1
        conv_rhs at hlt1 => rw [hz_split]
        have hlt2 : PreLt (z.dropLast ++ [a]) (z.dropLast ++ [c]) :=
          Or.inr ⟨z.dropLast, a, c, [], [], rfl, rfl, hgt⟩
        exact preLt_asymm hlt2 hlt1
    have hdeg_U : degree U z.dropLast = a := by
      unfold degree
      apply le_antisymm
      · refine Finset.sup_le fun m hm => ?_
        obtain ⟨w, hw_ch, rfl⟩ := Finset.mem_image.mp hm
        simp only [children, Finset.mem_filter] at hw_ch
        obtain ⟨hwU, c, rfl⟩ := hw_ch
        rw [getLast!_concat]
        exact hno_larger_sib c hwU
      · have hz_ch : z ∈ children U z.dropLast := by
          simp only [children, Finset.mem_filter]
          exact ⟨Finset.mem_insert_self z T, a, hz_split⟩
        have ha_img : a ∈ (children U z.dropLast).image (fun w => w.getLast!) :=
          Finset.mem_image.mpr ⟨z, hz_ch, by rw [hz_split, getLast!_concat]⟩
        exact Finset.le_sup (f := id) ha_img
    have hyoung_U : Youngest U z := ⟨z.dropLast, a, hz_split, ha_pos, hdeg_U.symm⟩
    have hdeg_T : degree T z.dropLast + 1 = a := by
      have hdeg_le : degree T z.dropLast ≤ a - 1 := by
        unfold degree
        refine Finset.sup_le fun m hm => ?_
        obtain ⟨w, hw_ch, rfl⟩ := Finset.mem_image.mp hm
        simp only [children, Finset.mem_filter] at hw_ch
        obtain ⟨hwT, c, rfl⟩ := hw_ch
        rw [getLast!_concat]
        dsimp only [id]
        have hcle : c ≤ a := hno_larger_sib c (Finset.mem_insert_of_mem hwT)
        have hcne : c ≠ a := fun hca => hz_not_T (hz_split ▸ hca ▸ hwT)
        have : 0 < a := ha_pos
        omega
      by_cases ha1 : a = 1
      · omega
      · have ha1_mem_U : z.dropLast ++ [a - 1] ∈ U := by
          have hzU : z.dropLast ++ [a] ∈ U := hz_split ▸ Finset.mem_insert_self z T
          exact hord_U.2.2 z.dropLast a hzU (a - 1) (by omega) (by omega)
        have ha1_ne_z : z.dropLast ++ [a - 1] ≠ z := by
          rw [hz_split]; intro h; have := (append_singleton_inj h).2; omega
        have ha1_mem_T : z.dropLast ++ [a - 1] ∈ T :=
          (Finset.mem_insert.mp ha1_mem_U).resolve_left ha1_ne_z
        have ha1_ge : a - 1 ≤ degree T z.dropLast := by
          unfold degree
          have hch : z.dropLast ++ [a - 1] ∈ children T z.dropLast := by
            simp [children, ha1_mem_T]
          have hle_sup := Finset.le_sup (f := id)
            (Finset.mem_image.mpr ⟨_, hch, getLast!_concat _ _⟩)
          exact hle_sup
        omega
    exact ⟨hz_eq, hzD, hz_not_T, hU_eq, hT_card_lt, hU_card, hU_card_le,
      hz_ne_nil, hdl_mem_T, hleaf_U, hyoung_U, hz_split.trans (by rw [← hdeg_T])⟩

lemma insertBlock_props {n : ℕ} (hn : 1 ≤ n) {x y : Node}
    (hx_ft : x ∈ fullTree n) (hy_ft : y ∈ fullTree n)
    (hxy : x ≠ y) (hadj : (chain x ∪ chain y).card ≤ n) (hy_not : y ∉ chain x)
    {i : ℕ} (hi : i < (chain y \ chain x).card)
    {H_T H_U : History (Fin n)}
    (hHT : Htree n (intermediate x y i) = some H_T)
    (hHU : Htree n (intermediate x y (i + 1)) = some H_U) :
    0 < (insertBlock n hn x y i).length ∧
    readWord (fullBuchi n hn) (some H_T) (insertBlock n hn x y i) = some H_U ∧
    (∀ e ∈ wordEdges (fullBuchi n hn) (some H_T) (insertBlock n hn x y i),
      unst (fullBuchi n hn) e = ∅) ∧
    (∀ e ∈ wordEdges (fullBuchi n hn) (some H_T) (insertBlock n hn x y i),
      ∀ z ∈ acc (fullBuchi n hn) e, z = x) ∧
    ((∃ e ∈ wordEdges (fullBuchi n hn) (some H_T) (insertBlock n hn x y i),
        x ∈ acc (fullBuchi n hn) e) →
      (chain x ∪ chain y).card = n ∧ PreLt y x) := by
  let F := fullBuchi n hn
  let D := chain y \ chain x
  let L := enumerateNodes D
  let r := D.card
  obtain ⟨hU_all, _, hUr_eq, hstep_all⟩ := intermediate_props hn hx_ft hy_ft hadj hy_not
  obtain ⟨hz_eq, hzD, hz_not_T, hU_eq, hT_card_lt, hU_card_eq, hU_card_le,
    _, hdl_mem_T, hleaf_U, _, hz_deg⟩ := hstep_all i hi
  let z := L[i]!
  let T := intermediate x y i
  let U := insert z T
  obtain ⟨hord_T, _, hT_card_le⟩ := hU_all i (Nat.le_of_lt hi)
  obtain ⟨hord_U, _, _⟩ := hU_all (i + 1) hi
  have hord_U'' : Ordered (insert z T) := by
    have heqU : insert z T = intermediate x y (i + 1) := hU_eq
    rwa [heqU]
  have hHT_val : H_T.val = canonicalData n T := (htree_some_iff n T H_T).mp hHT
  have hHU_val : H_U.val = canonicalData n U := by
    have heqU : insert z T = intermediate x y (i + 1) := hU_eq
    rw [← heqU] at hHU
    exact (htree_some_iff n U H_U).mp hHU
  have hHT_simp : Simple H_T := canonical_simple hn hord_T hT_card_le hHT_val
  let P := canonicalStates n T
  have hP_eq : stateSet H_T.val = P := by
    unfold stateSet
    rw [hHT_val]
    exact canonical_stateSet n (Finset.mem_union_left _ (nil_mem_chain x))
  let p := stateAt n hn (rank T z.dropLast)
  have hp_mem_P : p ∈ P := by
    simp only [P, canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [stateAt_val_of_lt hn (lt_trans (rank_lt_card hdl_mem_T) hT_card_lt)]
    exact rank_lt_card hdl_mem_T
  have hlast_not_P : lastState n hn ∉ P := by
    simp only [P, canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and, lastState]
    have : T.card < n := hT_card_lt
    omega
  have hown_dl : owner H_T.val p = z.dropLast := by
    apply owner_eq_of_own H_T.property (by rw [hHT_val]; exact hdl_mem_T)
    rw [hHT_val, canonical_own hn hord_T hT_card_le hdl_mem_T]
    exact Finset.mem_singleton_self p
  -- Step 1: genLetter
  have heff_gen := ((lemma_38 n hn H_T hHT_simp).1 p (hP_eq ▸ hp_mem_P) (hP_eq ▸ hlast_not_P)).1
  rw [hP_eq] at heff_gen
  obtain ⟨H_mid, hsucc_gen, hHmid_val, hHmid_simp, hacc_gen, hunst_gen⟩ := heff_gen
  have hz_gen_eq : owner H_T.val p ++ [degree H_T.val.nodes (owner H_T.val p) + 1] = z := by
    rw [hown_dl, show H_T.val.nodes = T by rw [hHT_val]; rfl]
    exact hz_deg.symm
  have hHmid_nodes : H_mid.val.nodes = U := by
    rw [hHmid_val]
    change insert (owner H_T.val p ++ [degree H_T.val.nodes (owner H_T.val p) + 1]) H_T.val.nodes = insert z T
    rw [hz_gen_eq, hHT_val]
    rfl
  have hHmid_stateSet : stateSet H_mid.val = insert (lastState n hn) P := by
    change H_mid.val.label [] = _
    rw [hHmid_val]
    simp only [generatedData, List.nil_prefix, ↓reduceIte]
    rw [show H_T.val.label [] = P from hP_eq, Finset.union_comm, Finset.singleton_union]
  let m := rank U z
  have hm_lt_U : m < U.card := rank_lt_card (Finset.mem_insert_self z T)
  have hm_lt_n : m < n := lt_of_lt_of_le hm_lt_U hU_card_le
  let π : Fin n → Fin n := fun q =>
    if q = lastState n hn then stateAt n hn m
    else if m ≤ q.val ∧ q.val < T.card then stateAt n hn (q.val + 1) else q
  -- Key identity: mapData H_mid.val π = canonicalData n U
  have hπ_on_rank : ∀ w ∈ T,
      π (stateAt n hn (rank T w)) = stateAt n hn (rank U w) := by
    intro w hwT
    have hrw_lt_T : rank T w < T.card := rank_lt_card hwT
    have hrw_lt_n : rank T w < n := lt_trans hrw_lt_T hT_card_lt
    have hrw_val : (stateAt n hn (rank T w)).val = rank T w := stateAt_val_of_lt hn hrw_lt_n
    have hne_last : stateAt n hn (rank T w) ≠ lastState n hn := by
      intro h
      have hv := congrArg Fin.val h
      simp only [hrw_val, lastState] at hv
      have : T.card < n := hT_card_lt
      omega
    have hrkU := rank_insert_of_notMem hz_not_T hwT
    simp only [π, if_neg hne_last, hrw_val]
    by_cases hwz : PreLt w z
    · rw [hrkU, if_pos hwz]
      have hlt_m : rank T w < m := by
        have := rank_strict_mono (Finset.mem_insert_of_mem hwT) (Finset.mem_insert_self z T) hwz
        rwa [hrkU, if_pos hwz] at this
      rw [if_neg (by omega)]
    · rw [hrkU, if_neg hwz]
      have hzw : PreLt z w := by
        rcases preLt_trichotomy w z with h | rfl | h
        · exact absurd h hwz
        · exact absurd hwT hz_not_T
        · exact h
      have hge_m : m ≤ rank T w := by
        have hlt_rk : m < rank U w :=
          rank_strict_mono (Finset.mem_insert_self z T) (Finset.mem_insert_of_mem hwT) hzw
        rw [hrkU, if_neg hwz] at hlt_rk
        exact Nat.le_of_lt_succ hlt_rk
      rw [if_pos ⟨hge_m, hrw_lt_T⟩]
  have hmap_eq : mapData H_mid.val π = canonicalData n U := by
    have hnodes : (mapData H_mid.val π).nodes = (canonicalData n U).nodes := hHmid_nodes
    have hlbl : (mapData H_mid.val π).label = (canonicalData n U).label := by
      funext u
      ext q
      rw [mem_mapData_iff]
      by_cases huU : u ∈ U
      · simp only [hHmid_val, generatedData, hz_gen_eq, canonicalData, huU, ↓reduceIte,
          Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨q0, hq0_T | hq0_z, rfl⟩
          · have huT : u ∈ T := by
              by_contra hnotT
              rw [hHT_val] at hq0_T
              simp [canonicalData, hnotT] at hq0_T
            rw [hHT_val] at hq0_T
            simp only [canonicalData, huT, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hq0_T
            obtain ⟨w, hwT, huw, hq0_val⟩ := hq0_T
            have hq0_eq : q0 = stateAt n hn (rank T w) := by
              apply Fin.ext
              rw [hq0_val, stateAt_val_of_lt hn (lt_trans (rank_lt_card hwT) hT_card_lt)]
            rw [hq0_eq, hπ_on_rank w hwT]
            exact ⟨w, Finset.mem_insert_of_mem hwT, huw,
              stateAt_val_of_lt hn (lt_of_lt_of_le (rank_lt_card (Finset.mem_insert_of_mem hwT)) hU_card_le)⟩
          · split_ifs at hq0_z with huz
            · simp only [Finset.mem_singleton] at hq0_z
              subst hq0_z
              simp only [π, ↓reduceIte]
              exact ⟨z, Finset.mem_insert_self z T, huz, stateAt_val_of_lt hn hm_lt_n⟩
            · simp at hq0_z
        · rintro ⟨w, hwU, huw, hqval⟩
          rcases Finset.mem_insert.mp hwU with rfl | hwT
          · refine ⟨lastState n hn, Or.inr (by simp [huw]), ?_⟩
            apply Fin.ext
            simp [π, stateAt_val_of_lt hn hm_lt_n, hqval, m]
          · have huT : u ∈ T := hord_T.2.1 w hwT u huw
            let q0 := stateAt n hn (rank T w)
            refine ⟨q0, Or.inl ?_, ?_⟩
            · rw [hHT_val]
              simp only [canonicalData, huT, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨w, hwT, huw, stateAt_val_of_lt hn (lt_trans (rank_lt_card hwT) hT_card_lt)⟩
            · rw [hπ_on_rank w hwT]
              apply Fin.ext
              rw [stateAt_val_of_lt hn (lt_of_lt_of_le (rank_lt_card hwU) hU_card_le), hqval]
      · have hu_not_mid : u ∉ H_mid.val.nodes := hHmid_nodes ▸ huU
        simp [canonicalData, huU, H_mid.property.2.2.1 u hu_not_mid]
    exact treeData_ext hnodes hlbl
  -- Direct arithmetic characterization of (π q).val on stateSet H_mid.val
  have hπ_val_on_P : ∀ q ∈ P,
      q ≠ lastState n hn ∧ q.val < T.card ∧
      ((m ≤ q.val ∧ (π q).val = q.val + 1) ∨ (q.val < m ∧ (π q).val = q.val)) := by
    intro q hqP
    have hq_lt_T : q.val < T.card := by
      simpa [P, canonicalStates] using hqP
    have hq_ne_last : q ≠ lastState n hn := by
      intro h; have hv := congrArg Fin.val h; simp only [lastState] at hv
      have : T.card < n := hT_card_lt; omega
    refine ⟨hq_ne_last, hq_lt_T, ?_⟩
    by_cases hmq : m ≤ q.val
    · left
      refine ⟨hmq, ?_⟩
      have hcond_q : m ≤ q.val ∧ q.val < T.card := ⟨hmq, hq_lt_T⟩
      simp only [π, if_neg hq_ne_last, if_pos hcond_q]
      exact stateAt_val_of_lt hn (by have : T.card < n := hT_card_lt; omega)
    · right
      refine ⟨by omega, ?_⟩
      simp only [π, if_neg hq_ne_last, if_neg (show ¬ (m ≤ q.val ∧ q.val < T.card) by omega)]
  have hinj_π : Set.InjOn π {q | q ∈ stateSet H_mid.val} := by
    intro q1 hq1 q2 hq2 heq
    change q1 ∈ stateSet H_mid.val at hq1
    change q2 ∈ stateSet H_mid.val at hq2
    rw [hHmid_stateSet] at hq1 hq2
    have hv_eq := congrArg Fin.val heq
    rcases Finset.mem_insert.mp hq1 with rfl | hq1P
    · have hv1 : (π (lastState n hn)).val = m := by
        simp [π, stateAt_val_of_lt hn hm_lt_n]
      rcases Finset.mem_insert.mp hq2 with rfl | hq2P
      · rfl
      · obtain ⟨_, _, (⟨hm2, hv2⟩ | ⟨hm2, hv2⟩)⟩ := hπ_val_on_P q2 hq2P <;> omega
    · obtain ⟨_, _, h1cases⟩ := hπ_val_on_P q1 hq1P
      rcases Finset.mem_insert.mp hq2 with rfl | hq2P
      · have hv2 : (π (lastState n hn)).val = m := by
          simp [π, stateAt_val_of_lt hn hm_lt_n]
        rcases h1cases with ⟨hm1, hv1⟩ | ⟨hm1, hv1⟩ <;> omega
      · obtain ⟨_, _, h2cases⟩ := hπ_val_on_P q2 hq2P
        apply Fin.ext
        rcases h1cases with ⟨hm1, hv1⟩ | ⟨hm1, hv1⟩ <;>
          rcases h2cases with ⟨hm2, hv2⟩ | ⟨hm2, hv2⟩ <;> omega
  -- Helper when U.card < n
  have havoid_of_lt : U.card < n → ∀ q ∈ stateSet H_mid.val, π q ≠ lastState n hn := by
    intro hU_lt q hq heq
    have hv_eq : (π q).val = n - 1 := congrArg Fin.val heq
    rw [hHmid_stateSet] at hq
    have hm_lt_U' : m < U.card := hm_lt_U
    have hU_eq_T1 : U.card = T.card + 1 := hU_card_eq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · have hv1 : (π (lastState n hn)).val = m := by
        simp [π, stateAt_val_of_lt hn hm_lt_n]
      omega
    · obtain ⟨_, hqT, (⟨_, hv1⟩ | ⟨_, hv1⟩)⟩ := hπ_val_on_P q hqP <;> omega
  -- Case split on `if U.card < n ∨ m ≠ n - 1`
  by_cases hcond : U.card < n ∨ m ≠ n - 1
  · have hib_eq : insertBlock n hn x y i =
        [genLetter hn P p, permLetter (insert (lastState n hn) P) π] := by
      unfold insertBlock
      dsimp only
      change [genLetter hn P p] ++ (if U.card < n ∨ m ≠ n - 1 then [permLetter (insert (lastState n hn) P) π] else []) = _
      rw [if_pos hcond]
      rfl
    by_cases hU_lt_n : U.card < n
    · -- Case 2a: U.card < n -> lemma_38 (P), no acc, no unst
      have heff_p := (lemma_38 n hn H_mid hHmid_simp).2.1 π hinj_π (havoid_of_lt hU_lt_n)
      rw [hHmid_stateSet] at heff_p
      obtain ⟨H2, hsucc2, hH2_val, _, hacc2, hunst2⟩ := heff_p
      have hH2_eq : H2 = H_U := Subtype.ext (hH2_val.trans (hmap_eq.trans hHU_val.symm))
      rw [hH2_eq] at hsucc2
      have hedges := wordEdges_pair F hsucc_gen hsucc2
      rw [hib_eq]
      refine ⟨by simp, readWord_pair F hsucc_gen hsucc2, ?_, ?_, ?_⟩
      · intro e he
        rw [hedges] at he
        rcases he with rfl | rfl
        · exact hunst_gen
        · exact hunst2
      · intro e he w hw
        rw [hedges] at he
        rcases he with rfl | rfl
        · change w ∈ acceptingNodes (fullBuchi n hn) H_T _ at hw
          rw [hacc_gen] at hw
          exact absurd hw (Finset.notMem_empty w)
        · change w ∈ acceptingNodes (fullBuchi n hn) H_mid _ at hw
          rw [hacc2] at hw
          exact absurd hw (Finset.notMem_empty w)
      · rintro ⟨e, he, hxacc⟩
        rw [hedges] at he
        rcases he with rfl | rfl
        · change x ∈ acceptingNodes (fullBuchi n hn) H_T _ at hxacc
          rw [hacc_gen] at hxacc
          exact absurd hxacc (Finset.notMem_empty x)
        · change x ∈ acceptingNodes (fullBuchi n hn) H_mid _ at hxacc
          rw [hacc2] at hxacc
          exact absurd hxacc (Finset.notMem_empty x)
    · -- Pure Case 2b: U.card = n and m ≠ n - 1
      have hm_ne : m ≠ n - 1 := hcond.resolve_left hU_lt_n
      have hU_eq_n : U.card = n := by have : U.card ≤ n := hU_card_le; omega
      obtain ⟨hpx, _⟩ := mem_fullTree_props hx_ft
      obtain ⟨hpy, _⟩ := mem_fullTree_props hy_ft
      have hU_sub_xy' : U ⊆ chain x ∪ chain y := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwT
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hzD).1
        · rcases Finset.mem_union.mp hwT with hwx | hwtk
          · exact Finset.mem_union_left _ hwx
          · have hwL : w ∈ L := List.mem_of_mem_take (List.mem_toFinset.mp hwtk)
            have hwD : w ∈ D := (enumerateNodes_props D).2.2.2.1 ▸ List.mem_toFinset.mpr hwL
            exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hwD).1
      have hU_eq_xy : U = chain x ∪ chain y :=
        Finset.eq_of_subset_of_card_le hU_sub_xy' (by omega)
      have hxy_card_n : (chain x ∪ chain y).card = n := hU_eq_xy ▸ hU_eq_n
      have hzy : z = y := by
        have hyU : y ∈ U := by
          rw [hU_eq_xy]
          exact Finset.mem_union_right _ (fact_30 y y hpy hpy).2.1.1
        rcases Finset.mem_insert.mp hyU with hyz | hyT
        · exact hyz.symm
        · exfalso
          rcases Finset.mem_union.mp hyT with hycx | hytk
          · exact hy_not hycx
          · obtain ⟨_, _, hL_len, _, hpw⟩ := enumerateNodes_props D
            obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hytk)
            obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt
            have hk_eq' : L[k] = y := htk_k.symm.trans hk_eq
            have hiL : i < L.length := hL_len.symm ▸ hi
            have hlt1 : PreLt L[k] L[i] :=
              List.pairwise_iff_getElem.mp hpw k i hk_lt_L hiL hk_lt_i
            rw [hk_eq', ← hz_eq] at hlt1
            rcases (fact_30 y y hpy hpy).2.1.2 z (Finset.mem_sdiff.mp hzD).1 with hzeqy | hzy_lt
            · change PreLt y z at hlt1
              rw [hzeqy] at hlt1
              exact preLt_irrefl y hlt1
            · exact preLt_asymm hlt1 hzy_lt
      have hpre_yx : PreLt y x := by
        rcases preLt_trichotomy y x with h | rfl | h
        · exact h
        · exact absurd rfl hxy.symm
        · exfalso
          have hlast_U_y : Last U y := by
            rw [hU_eq_xy]
            refine ⟨Finset.mem_union_right _ (fact_30 y y hpy hpy).2.1.1, ?_⟩
            intro w hw
            rcases Finset.mem_union.mp hw with hwx | hwy
            · rcases (fact_30 x x hpx hpx).2.1.2 w hwx with rfl | hwx_lt
              · exact Or.inr h
              · exact Or.inr (preLt_trans hwx_lt h)
            · exact (fact_30 y y hpy hpy).2.1.2 w hwy
          have hrk_y : rank U y = n - 1 := by rw [rank_of_last hlast_U_y, hU_eq_n]
          exact hm_ne (by simpa [m, hzy] using hrk_y)
      have hlast_U_x : Last U x := by
        rw [hU_eq_xy]
        refine ⟨Finset.mem_union_left _ (fact_30 x x hpx hpx).2.1.1, ?_⟩
        intro w hw
        rcases Finset.mem_union.mp hw with hwx | hwy
        · exact (fact_30 x x hpx hpx).2.1.2 w hwx
        · rcases (fact_30 y y hpy hpy).2.1.2 w hwy with rfl | hwy_lt
          · exact Or.inr hpre_yx
          · exact Or.inr (preLt_trans hwy_lt hpre_yx)
      have hleaf_U_x : Leaf U x :=
        ((fact_30 x x hpx hpx).2.2.2.2.2.2.2.2 U x hord_U'' hlast_U_x).1
      have hleaf_mid_x : Leaf H_mid.val.nodes x := by rw [hHmid_nodes]; exact hleaf_U_x
      have hx_mem_T : x ∈ T := Finset.mem_union_left _ (fact_30 x x hpx hpx).2.1.1
      have hleaf_T_x : Leaf T x := by
        refine ⟨hx_mem_T, ?_⟩
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have hwU : w ∈ children U x := by
          simp only [children, Finset.mem_filter] at hw ⊢
          exact ⟨Finset.mem_insert_of_mem hw.1, hw.2⟩
        rw [hleaf_U_x.2] at hwU; simp at hwU
      have hx_not_pre_z : ¬ x.IsPrefix z := by
        intro hpre
        rw [hzy] at hpre
        exact preLt_asymm hpre_yx (Or.inl ⟨hpre, hxy⟩)
      let sx := stateAt n hn (rank T x)
      have hmid_lbl_x : H_mid.val.label x = {sx} := by
        rw [hHmid_val]
        simp only [generatedData, hz_gen_eq, if_neg hx_not_pre_z, Finset.union_empty]
        rw [hHT_val, canonical_leaf_label hn hord_T hT_card_le hleaf_T_x]
      have hπ_sx : π sx = lastState n hn := by
        rw [hπ_on_rank x hx_mem_T, rank_of_last hlast_U_x, hU_eq_n]
        apply Fin.ext
        have hlt_n : n - 1 < n := by omega
        change (stateAt n hn (n - 1)).val = n - 1
        exact stateAt_val_of_lt hn hlt_n
      have heff_a := (lemma_38 n hn H_mid hHmid_simp).2.2.1 x sx π hleaf_mid_x hmid_lbl_x hinj_π hπ_sx
      rw [hHmid_stateSet] at heff_a
      obtain ⟨H2, hsucc2, hH2_val, _, hacc2, hunst2⟩ := heff_a
      have hH2_eq : H2 = H_U := Subtype.ext (hH2_val.trans (hmap_eq.trans hHU_val.symm))
      rw [hH2_eq] at hsucc2
      have hedges := wordEdges_pair F hsucc_gen hsucc2
      rw [hib_eq]
      refine ⟨by simp, readWord_pair F hsucc_gen hsucc2, ?_, ?_, ?_⟩
      · intro e he
        rw [hedges] at he
        rcases he with rfl | rfl
        · exact hunst_gen
        · exact hunst2
      · intro e he w hw
        rw [hedges] at he
        rcases he with rfl | rfl
        · change w ∈ acceptingNodes (fullBuchi n hn) H_T _ at hw
          rw [hacc_gen] at hw
          exact absurd hw (Finset.notMem_empty w)
        · change w ∈ acceptingNodes (fullBuchi n hn) H_mid _ at hw
          rw [hacc2] at hw
          exact Finset.mem_singleton.mp hw
      · intro _; exact ⟨hxy_card_n, hpre_yx⟩
  · -- Case 1: ¬ (U.card < n ∨ m ≠ n - 1), i.e., U.card = n and m = n - 1 -> 1-step [genLetter]
    have hU_ge_n : ¬ U.card < n := fun h => hcond (Or.inl h)
    have hm_eq : m = n - 1 := Classical.not_not.mp (fun h => hcond (Or.inr h))
    have hU_eq_n : U.card = n := by have : U.card ≤ n := hU_card_le; omega
    have hib_eq : insertBlock n hn x y i = [genLetter hn P p] := by
      unfold insertBlock
      dsimp only
      change [genLetter hn P p] ++ (if U.card < n ∨ m ≠ n - 1 then [permLetter (insert (lastState n hn) P) π] else []) = _
      rw [if_neg hcond, List.append_nil]
    have hπ_id : ∀ q ∈ stateSet H_mid.val, π q = q := by
      intro q hq
      rw [hHmid_stateSet] at hq
      rcases Finset.mem_insert.mp hq with rfl | hqP
      · simp only [π, ↓reduceIte, hm_eq]
        apply Fin.ext
        have hlt_n : n - 1 < n := by omega
        change (stateAt n hn (n - 1)).val = n - 1
        exact stateAt_val_of_lt hn hlt_n
      · obtain ⟨hq_ne_last, hq_lt_T, _⟩ := hπ_val_on_P q hqP
        have hT_eq : T.card = n - 1 := by have : U.card = T.card + 1 := hU_card_eq; omega
        simp [π, hq_ne_last, hm_eq, hT_eq]
    have hHmid_eq_map : H_mid.val = mapData H_mid.val π := by
      have hlbl : H_mid.val.label = (mapData H_mid.val π).label := by
        funext u
        ext q
        rw [mem_mapData_iff]
        by_cases hu : u ∈ H_mid.val.nodes
        · have hsub : H_mid.val.label u ⊆ stateSet H_mid.val :=
            label_sub_of_prefix H_mid.property [] u (by simpa using hu)
          exact ⟨fun hqu => ⟨q, hqu, hπ_id q (hsub hqu)⟩,
                 fun ⟨q0, hq0u, hq0eq⟩ => (hq0eq.symm.trans (hπ_id q0 (hsub hq0u))) ▸ hq0u⟩
        · simp [H_mid.property.2.2.1 u hu]
      exact treeData_ext rfl hlbl
    have hHmid_eq_HU : H_mid = H_U :=
      Subtype.ext (hHmid_eq_map.trans (hmap_eq.trans hHU_val.symm))
    rw [hHmid_eq_HU] at hsucc_gen
    have hedges := wordEdges_singleton F hsucc_gen
    rw [hib_eq]
    refine ⟨by simp, by simpa [readWord] using hsucc_gen, ?_, ?_, ?_⟩
    · intro e he; rw [hedges] at he; rcases he with rfl; exact hunst_gen
    · intro e he w hw; rw [hedges] at he; rcases he with rfl
      change w ∈ acceptingNodes (fullBuchi n hn) H_T _ at hw
      rw [hacc_gen] at hw
      exact absurd hw (Finset.notMem_empty w)
    · rintro ⟨e, he, hxacc⟩; rw [hedges] at he; rcases he with rfl
      change x ∈ acceptingNodes (fullBuchi n hn) H_T _ at hxacc
      rw [hacc_gen] at hxacc
      exact absurd hxacc (Finset.notMem_empty x)

lemma deleteBlock_props {n : ℕ} (hn : 1 ≤ n) {x y : Node}
    (hx_ft : x ∈ fullTree n) (hy_ft : y ∈ fullTree n)
    (hxy : x ≠ y) (hadj : (chain x ∪ chain y).card ≤ n) (hy_not : y ∉ chain x)
    {i : ℕ} (hi : i < (chain y \ chain x).card)
    {H_T H_U : History (Fin n)}
    (hHT : Htree n (intermediate x y i) = some H_T)
    (hHU : Htree n (intermediate x y (i + 1)) = some H_U) :
    readWord (fullBuchi n hn) (some H_U) (deleteBlock n hn x y i) = some H_T ∧
    (∀ w, (∃ e ∈ wordEdges (fullBuchi n hn) (some H_U) (deleteBlock n hn x y i),
        w ∈ unst (fullBuchi n hn) e) ↔
      w = (enumerateNodes (chain y \ chain x))[i]!) ∧
    (∀ e ∈ wordEdges (fullBuchi n hn) (some H_U) (deleteBlock n hn x y i),
      acc (fullBuchi n hn) e = ∅) := by
  let F := fullBuchi n hn
  let D := chain y \ chain x
  let L := enumerateNodes D
  obtain ⟨hU_all, _, _, hstep_all⟩ := intermediate_props hn hx_ft hy_ft hadj hy_not
  obtain ⟨hz_eq, hzD, hz_not_T, hU_eq, hT_card_lt, _, hU_card_le,
    _, _, hleaf_U, hyoung_U, _⟩ := hstep_all i hi
  let z := L[i]!
  let T := intermediate x y i
  let U := insert z T
  obtain ⟨hord_U, _, _⟩ := hU_all (i + 1) hi
  have hord_U' : Ordered U := by
    have heqU : insert z T = intermediate x y (i + 1) := hU_eq
    change Ordered (insert z T)
    rwa [heqU]
  have hHT_val : H_T.val = canonicalData n T := (htree_some_iff n T H_T).mp hHT
  have hHU_val : H_U.val = canonicalData n U := by
    have heqU : insert z T = intermediate x y (i + 1) := hU_eq
    rw [← heqU] at hHU
    exact (htree_some_iff n U H_U).mp hHU
  have hHU_simp : Simple H_U := canonical_simple hn hord_U' hU_card_le hHU_val
  let P := canonicalStates n U
  have hP_eq : stateSet H_U.val = P := by
    unfold stateSet
    rw [hHU_val]
    exact canonical_stateSet n (Finset.mem_insert_of_mem (Finset.mem_union_left _ (nil_mem_chain x)))
  let s := stateAt n hn (rank U z)
  have hHU_leaf_z : Leaf H_U.val.nodes z := by rw [hHU_val]; exact hleaf_U
  have hHU_young_z : Youngest H_U.val.nodes z := by rw [hHU_val]; exact hyoung_U
  have hHU_lbl_z : H_U.val.label z = {s} := by
    rw [hHU_val, canonical_leaf_label hn hord_U' hU_card_le hleaf_U]
  have hU_erase_z : U.erase z = T := Finset.erase_insert hz_not_T
  by_cases hcond : U.card = n ∧ s ≠ lastState n hn
  · -- Branch 1: delPrimeLetter
    obtain ⟨hU_eq_n, hs_ne_last⟩ := hcond
    have hdb_eq : deleteBlock n hn x y i =
        [delPrimeLetter hn P s, restoringLetter n T (deletedPrimeData hn (canonicalData n U) z s)] := by
      unfold deleteBlock
      dsimp only
      exact if_pos ⟨hU_eq_n, hs_ne_last⟩
    have hlast_mem_er : lastState n hn ∈ P.erase s := by
      refine Finset.mem_erase.mpr ⟨hs_ne_last.symm, ?_⟩
      simp only [P, canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and, lastState]
      have : U.card = n := hU_eq_n
      omega
    -- Show x ≠ z, Leaf U x, H_U.val.label x = {lastState n hn}
    obtain ⟨hpx, _⟩ := mem_fullTree_props hx_ft
    obtain ⟨hpy, _⟩ := mem_fullTree_props hy_ft
    have hU_sub_xy : U ⊆ chain x ∪ chain y := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwT
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hzD).1
      · rcases Finset.mem_union.mp hwT with hwx | hwtk
        · exact Finset.mem_union_left _ hwx
        · have hwL : w ∈ L := List.mem_of_mem_take (List.mem_toFinset.mp hwtk)
          have hwD : w ∈ D := (enumerateNodes_props D).2.2.2.1 ▸ List.mem_toFinset.mpr hwL
          exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hwD).1
    have hU_eq_xy : U = chain x ∪ chain y :=
      Finset.eq_of_subset_of_card_le hU_sub_xy (by have : U.card = n := hU_eq_n; omega)
    have hzy : z = y := by
      have hyU : y ∈ U := hU_eq_xy ▸ Finset.mem_union_right _ (fact_30 y y hpy hpy).2.1.1
      rcases Finset.mem_insert.mp hyU with hyz | hyT
      · exact hyz.symm
      · exfalso
        rcases Finset.mem_union.mp hyT with hycx | hytk
        · exact hy_not hycx
        · obtain ⟨_, _, hL_len, _, hpw⟩ := enumerateNodes_props D
          obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hytk)
          obtain ⟨hk_lt_i, hk_lt_L, htk_k⟩ := getElem_take_eq L hk_lt
          have hk_eq' : L[k] = y := htk_k.symm.trans hk_eq
          have hiL : i < L.length := hL_len.symm ▸ hi
          have hlt1 : PreLt L[k] L[i] :=
            List.pairwise_iff_getElem.mp hpw k i hk_lt_L hiL hk_lt_i
          rw [hk_eq', ← hz_eq] at hlt1
          rcases (fact_30 y y hpy hpy).2.1.2 z (Finset.mem_sdiff.mp hzD).1 with hzeqy | hzy_lt
          · change PreLt y z at hlt1
            rw [hzeqy] at hlt1
            exact preLt_irrefl y hlt1
          · exact preLt_asymm hlt1 hzy_lt
    have hrk_z_ne : rank U z ≠ n - 1 := by
      intro hrk
      apply hs_ne_last
      apply Fin.ext
      have hlt_n : n - 1 < n := by omega
      change (stateAt n hn (rank U z)).val = n - 1
      rw [hrk]
      exact stateAt_val_of_lt hn hlt_n
    have hpre_yx : PreLt y x := by
      rcases preLt_trichotomy y x with h | rfl | h
      · exact h
      · exact absurd rfl hxy.symm
      · exfalso
        have hlast_U_y : Last U y := by
          rw [hU_eq_xy]
          refine ⟨Finset.mem_union_right _ (fact_30 y y hpy hpy).2.1.1, ?_⟩
          intro w hw
          rcases Finset.mem_union.mp hw with hwx | hwy
          · rcases (fact_30 x x hpx hpx).2.1.2 w hwx with rfl | hwx_lt
            · exact Or.inr h
            · exact Or.inr (preLt_trans hwx_lt h)
          · exact (fact_30 y y hpy hpy).2.1.2 w hwy
        exact hrk_z_ne (by rw [hzy, rank_of_last hlast_U_y, hU_eq_n])
    have hlast_U_x : Last U x := by
      rw [hU_eq_xy]
      refine ⟨Finset.mem_union_left _ (fact_30 x x hpx hpx).2.1.1, ?_⟩
      intro w hw
      rcases Finset.mem_union.mp hw with hwx | hwy
      · exact (fact_30 x x hpx hpx).2.1.2 w hwx
      · rcases (fact_30 y y hpy hpy).2.1.2 w hwy with rfl | hwy_lt
        · exact Or.inr hpre_yx
        · exact Or.inr (preLt_trans hwy_lt hpre_yx)
    have hleaf_U_x : Leaf U x :=
      ((fact_30 x x hpx hpx).2.2.2.2.2.2.2.2 U x hord_U' hlast_U_x).1
    have hHU_leaf_x : Leaf H_U.val.nodes x := by rw [hHU_val]; exact hleaf_U_x
    have hHU_lbl_x : H_U.val.label x = {lastState n hn} := by
      rw [hHU_val, canonical_leaf_label hn hord_U' hU_card_le hleaf_U_x, rank_of_last hlast_U_x, hU_eq_n]
      congr 1
      apply Fin.ext
      have hlt_n : n - 1 < n := by omega
      change (stateAt n hn (n - 1)).val = n - 1
      exact stateAt_val_of_lt hn hlt_n
    have hxz_ne : x ≠ z := hzy ▸ hxy
    have heff_del := ((lemma_38 n hn H_U hHU_simp).2.2.2 z s hHU_leaf_z hHU_young_z hHU_lbl_z).2
      x hxz_ne hHU_leaf_x hHU_lbl_x (hP_eq ▸ hlast_mem_er)
    rw [hP_eq] at heff_del
    obtain ⟨⟨H_del, hsucc1, hHdel_val, hHdel_simp, hacc1, hunst1⟩, _, _⟩ := heff_del
    have hHdel_val' : H_del.val = deletedPrimeData hn (canonicalData n U) z s := by
      rwa [hHU_val] at hHdel_val
    have hHdel_nodes : H_del.val.nodes = T := by
      rw [hHdel_val']; simp [deletedPrimeData, mapData, deletedData, canonicalData, hU_erase_z]
    obtain ⟨H2, hsucc2, hH2_eq, hacc2, hunst2⟩ :=
      effect_restoringLetter hn hT_card_lt H_del hHdel_simp hHdel_nodes hHT_val
    rw [hH2_eq] at hsucc2
    rw [← hHdel_val'] at hdb_eq
    have hedges := wordEdges_pair F hsucc1 hsucc2
    rw [hdb_eq]
    refine ⟨readWord_pair F hsucc1 hsucc2, ?_, ?_⟩
    · intro w
      rw [hedges]
      constructor
      · rintro ⟨e, he, hw⟩
        rcases he with rfl | rfl
        · change w ∈ unstable (fullBuchi n hn) H_U _ at hw
          rw [hunst1] at hw
          exact Finset.mem_singleton.mp hw
        · change w ∈ unstable (fullBuchi n hn) H_del _ at hw
          rw [hunst2] at hw
          exact absurd hw (Finset.notMem_empty w)
      · intro hw
        refine ⟨(H_U, delPrimeLetter hn P s, H_del), Or.inl rfl, ?_⟩
        change w ∈ unstable (fullBuchi n hn) H_U _
        rw [hunst1]
        exact Finset.mem_singleton.mpr hw
    · intro e he
      rw [hedges] at he
      rcases he with rfl | rfl
      · exact hacc1
      · exact hacc2
  · -- Branch 2: delLetter
    have hdb_eq : deleteBlock n hn x y i =
        [delLetter P s, restoringLetter n T (deletedData (canonicalData n U) z s)] := by
      unfold deleteBlock
      dsimp only
      exact if_neg hcond
    have hlast_not_er : lastState n hn ∉ P.erase s := by
      intro hmem
      obtain ⟨hne_s, hlast_P⟩ := Finset.mem_erase.mp hmem
      simp only [P, canonicalStates, Finset.mem_filter, Finset.mem_univ, true_and, lastState] at hlast_P
      have : U.card ≤ n := hU_card_le
      exact hcond ⟨by omega, hne_s.symm⟩
    have heff_del := ((lemma_38 n hn H_U hHU_simp).2.2.2 z s hHU_leaf_z hHU_young_z hHU_lbl_z).1
      (hP_eq ▸ hlast_not_er)
    rw [hP_eq] at heff_del
    obtain ⟨⟨H_del, hsucc1, hHdel_val, hHdel_simp, hacc1, hunst1⟩, _⟩ := heff_del
    have hHdel_val' : H_del.val = deletedData (canonicalData n U) z s := by
      rwa [hHU_val] at hHdel_val
    have hHdel_nodes : H_del.val.nodes = T := by
      rw [hHdel_val']; simp [deletedData, canonicalData, hU_erase_z]
    obtain ⟨H2, hsucc2, hH2_eq, hacc2, hunst2⟩ :=
      effect_restoringLetter hn hT_card_lt H_del hHdel_simp hHdel_nodes hHT_val
    rw [hH2_eq] at hsucc2
    rw [← hHdel_val'] at hdb_eq
    have hedges := wordEdges_pair F hsucc1 hsucc2
    rw [hdb_eq]
    refine ⟨readWord_pair F hsucc1 hsucc2, ?_, ?_⟩
    · intro w
      rw [hedges]
      constructor
      · rintro ⟨e, he, hw⟩
        rcases he with rfl | rfl
        · change w ∈ unstable (fullBuchi n hn) H_U _ at hw
          rw [hunst1] at hw
          exact Finset.mem_singleton.mp hw
        · change w ∈ unstable (fullBuchi n hn) H_del _ at hw
          rw [hunst2] at hw
          exact absurd hw (Finset.notMem_empty w)
      · intro hw
        refine ⟨(H_U, delLetter P s, H_del), Or.inl rfl, ?_⟩
        change w ∈ unstable (fullBuchi n hn) H_U _
        rw [hunst1]
        exact Finset.mem_singleton.mpr hw
    · intro e he
      rw [hedges] at he
      rcases he with rfl | rfl
      · exact hacc1
      · exact hacc2

/-! ### Full `connectingWord` (`Wxy`) Analysis -/

lemma connectingWord_props (n : ℕ) (hn : 1 ≤ n) {x y : Node}
    (hx_ft : x ∈ fullTree n) (hy_ft : y ∈ fullTree n)
    (hxy : x ≠ y) (hadj : (chain x ∪ chain y).card ≤ n) (hy_not : y ∉ chain x) :
    (∃ H K, Htree n (chain x) = some H ∧
      Htree n (chain x ∪ chain y) = some K ∧
      ClosedWalk (fullBuchi n hn) H (connectingWord n hn x y) ∧
      K ∈ visited (fullBuchi n hn) H (connectingWord n hn x y)) ∧
    (∀ z, (∃ e ∈ Wxy n hn x y, z ∈ unst (fullBuchi n hn) e) ↔
      z ∈ chain y \ chain x) ∧
    (∃ e ∈ Wxy n hn x y, y ∈ unst (fullBuchi n hn) e) ∧
    (∀ e ∈ Wxy n hn x y, ∀ z ∈ acc (fullBuchi n hn) e, z = x) ∧
    ((∃ e ∈ Wxy n hn x y, x ∈ acc (fullBuchi n hn) e) →
      (chain x ∪ chain y).card = n ∧ PreLt y x) := by
  let F := fullBuchi n hn
  let D := chain y \ chain x
  let L := enumerateNodes D
  let r := D.card
  obtain ⟨hpy, _⟩ := mem_fullTree_props hy_ft
  have hy_mem_D : y ∈ D := Finset.mem_sdiff.mpr ⟨(fact_30 y y hpy hpy).2.1.1, hy_not⟩
  have hr_pos : 0 < r := Finset.card_pos.mpr ⟨y, hy_mem_D⟩
  obtain ⟨hU_all, hU0_eq, hUr_eq, _⟩ := intermediate_props hn hx_ft hy_ft hadj hy_not
  have hH_ex : ∀ k ≤ r, ∃ Hk, Htree n (intermediate x y k) = some Hk ∧ Reachable F Hk := by
    intro k hk
    obtain ⟨hord_k, hne_k, hcard_k⟩ := hU_all k hk
    exact lemma_39 n hn (intermediate x y k) hord_k hne_k hcard_k
  let Hseq : (k : ℕ) → k ≤ r → History (Fin n) :=
    fun k hk => Classical.choose (hH_ex k hk)
  have hHseq_tree : ∀ k (hk : k ≤ r), Htree n (intermediate x y k) = some (Hseq k hk) :=
    fun k hk => (Classical.choose_spec (hH_ex k hk)).1
  have hHseq_reach : ∀ k (hk : k ≤ r), Reachable F (Hseq k hk) :=
    fun k hk => (Classical.choose_spec (hH_ex k hk)).2
  let H0 := Hseq 0 (Nat.zero_le r)
  let Hr := Hseq r le_rfl
  have hH0_cx : Htree n (chain x) = some H0 := hU0_eq ▸ hHseq_tree 0 (Nat.zero_le r)
  have hHr_cxy : Htree n (chain x ∪ chain y) = some Hr := hUr_eq ▸ hHseq_tree r le_rfl
  -- Phase 1 induction
  have hphase1 : ∀ k (hk : k ≤ r),
      readWord F (some H0) ((List.range k).flatMap (insertBlock n hn x y)) = some (Hseq k hk) ∧
      wordEdges F (some H0) ((List.range k).flatMap (insertBlock n hn x y)) =
        ⋃ (i : ℕ) (hi : i < k),
          wordEdges F (some (Hseq i (by omega))) (insertBlock n hn x y i) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have heq0 : Hseq 0 hk = H0 := rfl
      simp [heq0, readWord, wordEdges_nil]
    | succ k ih =>
      intro hk1
      have hk : k ≤ r := Nat.le_of_lt hk1
      obtain ⟨hread_k, hedges_k⟩ := ih hk
      obtain ⟨_, hread_blk, _, _, _⟩ :=
        insertBlock_props hn hx_ft hy_ft hxy hadj hy_not hk1
          (hHseq_tree k hk) (hHseq_tree (k + 1) hk1)
      have hfm : (List.range (k + 1)).flatMap (insertBlock n hn x y) =
          (List.range k).flatMap (insertBlock n hn x y) ++ insertBlock n hn x y k := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine ⟨?_, ?_⟩
      · rw [hfm, readWord_append, hread_k, hread_blk]
      · rw [hfm, wordEdges_append F hread_k, hedges_k]
        ext e
        simp only [Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro (⟨i, hik, he⟩ | he)
          · exact ⟨i, by omega, he⟩
          · exact ⟨k, by omega, he⟩
        · rintro ⟨i, hik1, he⟩
          by_cases hik : i < k
          · exact Or.inl ⟨i, hik, he⟩
          · have hik_eq : i = k := by omega
            subst hik_eq
            exact Or.inr he
  -- Phase 2 induction
  have hphase2 : ∀ k (hk : k ≤ r),
      readWord F (some (Hseq k hk)) ((List.range k).reverse.flatMap (deleteBlock n hn x y)) = some H0 ∧
      wordEdges F (some (Hseq k hk)) ((List.range k).reverse.flatMap (deleteBlock n hn x y)) =
        ⋃ (i : ℕ) (hi : i < k),
          wordEdges F (some (Hseq (i + 1) (by omega))) (deleteBlock n hn x y i) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have heq0 : Hseq 0 hk = H0 := rfl
      simp [heq0, readWord, wordEdges_nil]
    | succ k ih =>
      intro hk1
      have hk : k ≤ r := Nat.le_of_lt hk1
      obtain ⟨hread_k, hedges_k⟩ := ih hk
      obtain ⟨hread_blk, _, _⟩ :=
        deleteBlock_props hn hx_ft hy_ft hxy hadj hy_not hk1
          (hHseq_tree k hk) (hHseq_tree (k + 1) hk1)
      have hfm : (List.range (k + 1)).reverse.flatMap (deleteBlock n hn x y) =
          deleteBlock n hn x y k ++ (List.range k).reverse.flatMap (deleteBlock n hn x y) := by
        rw [List.range_succ, List.reverse_append, List.reverse_singleton,
          List.flatMap_append, List.flatMap_singleton]
      refine ⟨?_, ?_⟩
      · rw [hfm, readWord_append, hread_blk, hread_k]
      · rw [hfm, wordEdges_append F hread_blk, hedges_k]
        ext e
        simp only [Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro (he | ⟨i, hik, he⟩)
          · exact ⟨k, by omega, he⟩
          · exact ⟨i, by omega, he⟩
        · rintro ⟨i, hik1, he⟩
          by_cases hik : i < k
          · exact Or.inr ⟨i, hik, he⟩
          · have hik_eq : i = k := by omega
            subst hik_eq
            exact Or.inl he
  obtain ⟨hread1, hedges1⟩ := hphase1 r le_rfl
  obtain ⟨hread2, hedges2⟩ := hphase2 r le_rfl
  let w1 := (List.range r).flatMap (insertBlock n hn x y)
  let w2 := (List.range r).reverse.flatMap (deleteBlock n hn x y)
  have hcw_eq : connectingWord n hn x y = w1 ++ w2 := by
    unfold connectingWord
    rw [if_neg hy_not]
  have hlen_pos : 0 < (connectingWord n hn x y).length := by
    obtain ⟨hlen0, _, _, _, _⟩ :=
      insertBlock_props hn hx_ft hy_ft hxy hadj hy_not hr_pos
        (hHseq_tree 0 (Nat.zero_le r)) (hHseq_tree 1 hr_pos)
    have hmem0 : 0 ∈ List.range r := List.mem_range.mpr hr_pos
    have hsub_len : (insertBlock n hn x y 0).length ≤ w1.length := by
      have : List.range r = [0] ++ (List.range r).tail := by
        cases hrr : List.range r with
        | nil => simp [hrr] at hmem0
        | cons a tl =>
          have ha0 : a = 0 := by
            have := congrArg (fun l => l[0]?) hrr
            simpa [List.getElem?_range hr_pos] using this.symm
          subst ha0; simp
      dsimp only [w1]
      rw [this, List.flatMap_append, List.flatMap_singleton]
      simp
    rw [hcw_eq, List.length_append]
    omega
  have hread_all : readWord F (some H0) (connectingWord n hn x y) = some H0 := by
    rw [hcw_eq, readWord_append, hread1, hread2]
  have hvis_Hr : Hr ∈ visited F H0 (connectingWord n hn x y) := by
    refine ⟨w1.length, ?_, ?_⟩
    · rw [hcw_eq, List.length_append]; omega
    · rw [hcw_eq, List.take_left, hread1]
  have hedges_all : Wxy n hn x y =
      (⋃ (i : ℕ) (hi : i < r),
        wordEdges F (some (Hseq i (by omega))) (insertBlock n hn x y i)) ∪
      (⋃ (i : ℕ) (hi : i < r),
        wordEdges F (some (Hseq (i + 1) (by omega))) (deleteBlock n hn x y i)) := by
    unfold Wxy
    rw [hH0_cx, hcw_eq, wordEdges_append F hread1, hedges1, hedges2]
  have hunst_iff : ∀ z, (∃ e ∈ Wxy n hn x y, z ∈ unst F e) ↔ z ∈ D := by
    intro z
    rw [hedges_all]
    obtain ⟨_, _, hL_len, hL_fin, _⟩ := enumerateNodes_props D
    constructor
    · rintro ⟨e, he1 | he2, hz_unst⟩
      · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he1
        have hemp := (insertBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
          (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.2.1 e hei
        rw [hemp] at hz_unst; simp at hz_unst
      · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he2
        have hd_iff := (deleteBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
          (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.1 z
        have hz_eq_Li : z = L[i]! := hd_iff.mp ⟨e, hei, hz_unst⟩
        have hiL : i < L.length := hL_len.symm ▸ hi
        have hz_Li : z = L[i] := by
          simpa [L, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hiL] using hz_eq_Li
        rw [hz_Li, ← hL_fin]
        exact List.mem_toFinset.mpr (List.getElem_mem hiL)
    · intro hzD
      have hzL : z ∈ L := List.mem_toFinset.mp (hL_fin.symm ▸ hzD)
      obtain ⟨i, hiL, rfl⟩ := List.getElem_of_mem hzL
      have hi : i < r := by
        change i < D.card
        rwa [← hL_len]
      have hd_iff := (deleteBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
        (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.1 L[i]
      have hLi_bang : L[i] = L[i]! := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hiL]
      obtain ⟨e, hei, hz_unst⟩ := hd_iff.mpr hLi_bang
      exact ⟨e, Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hei⟩), hz_unst⟩
  refine ⟨⟨H0, Hr, hH0_cx, hHr_cxy, ⟨hlen_pos, hHseq_reach 0 (Nat.zero_le r), hread_all⟩, hvis_Hr⟩,
    hunst_iff, (hunst_iff y).mpr hy_mem_D, ?_, ?_⟩
  · intro e he z hz_acc
    rw [hedges_all] at he
    rcases he with he1 | he2
    · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he1
      exact (insertBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
        (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.2.2.1 e hei z hz_acc
    · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he2
      have hemp := (deleteBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
        (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.2 e hei
      rw [hemp] at hz_acc; simp at hz_acc
  · rintro ⟨e, he, hx_acc⟩
    rw [hedges_all] at he
    rcases he with he1 | he2
    · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he1
      exact (insertBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
        (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.2.2.2 ⟨e, hei, hx_acc⟩
    · obtain ⟨i, hi, hei⟩ := Set.mem_iUnion₂.mp he2
      have hemp := (deleteBlock_props hn hx_ft hy_ft hxy hadj hy_not hi
        (hHseq_tree i (by omega)) (hHseq_tree (i + 1) hi)).2.2 e hei
      rw [hemp] at hx_acc; simp at hx_acc

end
end BuchiRabinIndex.LowerBound.Lemma40Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma40Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (S : Finset Node)
    (hS : S ⊆ fullTree n) (hclique : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Adj n x y)
    (x : Node) (hx : x ∈ S) :
    (∀ y ∈ S, x ≠ y → y ∉ chain x →
      (∃ H K, Htree n (chain x) = some H ∧
        Htree n (chain x ∪ chain y) = some K ∧
        ClosedWalk (fullBuchi n hn) H (connectingWord n hn x y) ∧
        K ∈ visited (fullBuchi n hn) H (connectingWord n hn x y)) ∧
      (∀ z, (∃ e ∈ Wxy n hn x y, z ∈ unst (fullBuchi n hn) e) ↔
        z ∈ chain y \ chain x) ∧
      (∃ e ∈ Wxy n hn x y, y ∈ unst (fullBuchi n hn) e) ∧
      (∀ e ∈ Wxy n hn x y, ∀ z ∈ acc (fullBuchi n hn) e, z = x) ∧
      ((∃ e ∈ Wxy n hn x y, x ∈ acc (fullBuchi n hn) e) →
        (chain x ∪ chain y).card = n ∧ PreLt y x)) ∧
    (∀ e ∈ Wx n hn S x, ∀ z ∈ chain x, z ∉ unst (fullBuchi n hn) e) ∧
    AcceptingCycle (fullBuchi n hn) (Ccycle n hn S x) := by
  let F := fullBuchi n hn
  have hx_ft : x ∈ fullTree n := hS hx
  have hpart1 : ∀ y ∈ S, x ≠ y → y ∉ chain x →
      (∃ H K, Htree n (chain x) = some H ∧
        Htree n (chain x ∪ chain y) = some K ∧
        ClosedWalk F H (connectingWord n hn x y) ∧
        K ∈ visited F H (connectingWord n hn x y)) ∧
      (∀ z, (∃ e ∈ Wxy n hn x y, z ∈ unst F e) ↔
        z ∈ chain y \ chain x) ∧
      (∃ e ∈ Wxy n hn x y, y ∈ unst F e) ∧
      (∀ e ∈ Wxy n hn x y, ∀ z ∈ acc F e, z = x) ∧
      ((∃ e ∈ Wxy n hn x y, x ∈ acc F e) →
        (chain x ∪ chain y).card = n ∧ PreLt y x) := by
    intro y hy hxy hy_not
    exact connectingWord_props n hn hx_ft (hS hy) hxy (hclique x hx y hy hxy).2 hy_not
  have hpart2 : ∀ e ∈ Wx n hn S x, ∀ z ∈ chain x, z ∉ unst F e := by
    intro e he z hzx hz_unst
    obtain ⟨y, hy_er, hey⟩ := Set.mem_iUnion₂.mp he
    obtain ⟨hyx, hyS⟩ := Finset.mem_erase.mp hy_er
    by_cases hy_in : y ∈ chain x
    · unfold Wxy connectingWord at hey
      rw [if_pos hy_in, wordEdges_nil] at hey
      exact hey
    · have hiff := (hpart1 y hyS hyx.symm hy_in).2.1 z
      have hzD := hiff.mp ⟨e, hey, hz_unst⟩
      exact (Finset.mem_sdiff.mp hzD).2 hzx
  refine ⟨hpart1, hpart2, ?_⟩
  -- Part 3: AcceptingCycle F (Ccycle n hn S x)
  obtain ⟨Hx, hHx_tree, hcw_A, hunst_A, hx_acc_A⟩ := acceptingWord_props n hn hx_ft
  let Ys : List Node := ((S.erase x).filter (fun y => y ∉ chain x)).toList
  let ws : List (List (Letter n)) := acceptingWord n hn x :: Ys.map (connectingWord n hn x)
  let k := ws.length
  have hk_pos : 0 < k := by simp [k, ws]
  have hcw_ws : ∀ idx : Fin k, ClosedWalk F Hx ws[idx] := by
    intro ⟨idx, hidx⟩
    cases idx with
    | zero => exact hcw_A
    | succ m =>
      simp only [Fin.getElem_fin]
      have hm_lt : m < Ys.length := by simp [k, ws] at hidx; omega
      have hws_eq : ws[m + 1] = connectingWord n hn x Ys[m] := by simp [ws]
      rw [hws_eq]
      have hy_mem : Ys[m] ∈ (S.erase x).filter (fun y => y ∉ chain x) :=
        Finset.mem_toList.mp (List.getElem_mem hm_lt)
      obtain ⟨hy_er, hy_not⟩ := Finset.mem_filter.mp hy_mem
      obtain ⟨hyx, hyS⟩ := Finset.mem_erase.mp hy_er
      obtain ⟨H', _, hH'_tree, _, hcw_y, _⟩ := (hpart1 Ys[m] hyS hyx.symm hy_not).1
      have hH'_eq : H' = Hx := Option.some.inj (hH'_tree.symm.trans hHx_tree)
      rwa [← hH'_eq]
  have hconn_ws : ∀ j : Fin k, 0 < j.val → ∃ i : Fin k, i.val < j.val ∧
      (visited F Hx ws[i] ∩ visited F Hx ws[j]).Nonempty := by
    intro j hj
    refine ⟨⟨0, hk_pos⟩, hj, Hx, ?_, ?_⟩
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · exact ⟨0, Nat.zero_le _, rfl⟩
  have hcyc_union : Cycle F (⋃ i : Fin k, wordEdges F (some Hx) ws[i]) :=
    (fact_31 n hn).2 k (fun _ => Hx) (fun i => ws[i]) hk_pos hcw_ws hconn_ws
  have hunion_eq : (⋃ i : Fin k, wordEdges F (some Hx) ws[i]) = Ccycle n hn S x := by
    ext e
    simp only [Set.mem_iUnion, Ccycle, Set.mem_union, Wx]
    constructor
    · rintro ⟨⟨idx, hidx⟩, he⟩
      cases idx with
      | zero =>
        right
        simpa [ws, Acycle, hHx_tree] using he
      | succ m =>
        left
        have hm_lt : m < Ys.length := by simp [k, ws] at hidx; omega
        have hy_mem : Ys[m] ∈ (S.erase x).filter (fun y => y ∉ chain x) :=
          Finset.mem_toList.mp (List.getElem_mem hm_lt)
        obtain ⟨hy_er, _⟩ := Finset.mem_filter.mp hy_mem
        refine ⟨Ys[m], hy_er, ?_⟩
        simpa [ws, Wxy, hHx_tree] using he
    · rintro (⟨y, hy_er, hey⟩ | heA)
      · by_cases hy_in : y ∈ chain x
        · unfold Wxy connectingWord at hey
          rw [if_pos hy_in, wordEdges_nil] at hey
          cases hey
        · have hy_Ys : y ∈ Ys :=
            Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hy_er, hy_in⟩)
          obtain ⟨m, hm_lt, rfl⟩ := List.getElem_of_mem hy_Ys
          refine ⟨⟨m + 1, by simp [k, ws]; omega⟩, ?_⟩
          simpa [ws, Wxy, hHx_tree] using hey
      · refine ⟨⟨0, hk_pos⟩, ?_⟩
        simpa [ws, Acycle, hHx_tree] using heA
  rw [hunion_eq] at hcyc_union
  rw [lemma_32 n hn (Ccycle n hn S x) hcyc_union]
  obtain ⟨hpx, _⟩ := mem_fullTree_props hx_ft
  refine ⟨x, hpx, ?_, ?_⟩
  · intro e he
    rcases he with heWx | heA
    · exact hpart2 e heWx x (fact_30 x x hpx hpx).2.1.1
    · rw [hunst_A e heA]; simp
  · obtain ⟨e, heA, hx_acc⟩ := hx_acc_A
    exact ⟨e, Or.inr heA, hx_acc⟩
