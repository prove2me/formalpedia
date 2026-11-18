-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:50:26.329111+00:00
-- url     : https://prove2.me/submissions/286566cd-5aba-4f75-8e09-9316ef2ce6a2

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator
import Mathlib.Combinatorics.SimpleGraph.Star


open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EdgeCounting

 theorem edgeCount_eq {n : ℕ} (G : SimpleGraph (Fin n)) : edgeCount G = G.edgeSet.ncard := by
  classical
  rw [edgeCount, Set.ncard_eq_toFinset_card']
  change ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)).card = G.edgeFinset.card
  apply Finset.card_bij (fun e he => s(e.1,e.2))
  · intro e he
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (Finset.mem_filter.mp he).2.2
  · intro e he f hf hEq
    have he' := (Finset.mem_filter.mp he).2.1
    have hf' := (Finset.mem_filter.mp hf).2.1
    rcases Sym2.eq_iff.mp hEq with hEq | hEq
    · exact Prod.ext hEq.1 hEq.2
    · have h1 := congrArg Fin.val hEq.1
      have h2 := congrArg Fin.val hEq.2
      have heV := he'
      have hfV := hf'
      simp only [Fin.lt_def] at heV hfV
      omega
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by simpa using he
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
      · exact ⟨(u,v), by simp [h, hadj], rfl⟩
      · exact ⟨(v,u), by simp [h, hadj.symm], Sym2.eq_swap⟩

end EdgeSublinearMWIS.Main.EdgeCounting


open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StructuralHelpers

 theorem blowup_of_projection {n m : ℕ} (C : GraphClass) (G : SimpleGraph (Fin n))
    (hC : Hereditary C) (hG : C n G) (H : SimpleGraph (Fin m)) (p : Fin m → Fin n)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (p u) (p v)) : BlowupClass C m H := by
  classical
  let V := {v : Fin n // v ∈ Set.range p}
  let r := Fintype.card V
  let e : V ≃ Fin r := Fintype.equivFin V
  let inc : Fin r ↪ Fin n :=
    ⟨fun v => (e.symm v).val, Subtype.val_injective.comp e.symm.injective⟩
  let G0 := G.comap inc
  have hG0 : C r G0 := hC G G0 inc hG (fun u v => Iff.rfl)
  let f : Fin m → Fin r := fun u => e ⟨p u, Set.mem_range_self u⟩
  refine ⟨r, G0, hG0, f, ?_, ?_⟩
  · intro v
    obtain ⟨u, hu⟩ := (e.symm v).property
    refine ⟨u, ?_⟩
    have hh : (⟨p u, Set.mem_range_self u⟩ : V) = e.symm v := Subtype.ext hu
    change e _ = v
    rw [hh]
    exact e.apply_symm_apply v
  · intro u v
    change H.Adj u v ↔ G.Adj (inc (f u)) (inc (f v))
    simpa only [inc, f, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply] using hAdj u v

 theorem blowup_hereditary (C : GraphClass) (hC : Hereditary C) : Hereditary (BlowupClass C) := by
  intro n m H H' inc hH hind
  obtain ⟨r, G, hG, p, hp, hAdj⟩ := hH
  exact blowup_of_projection C G hC hG H' (fun v => p (inc v))
    (fun u v => (hind u v).trans (hAdj (inc u) (inc v)))

end EdgeSublinearMWIS.Main.StructuralHelpers


open scoped BigOperators Classical
open EdgeSublinearMWIS.Main
open EdgeSublinearMWIS.Main.EdgeCounting
open RobertsonSeymour1986.GM5
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BlowupDecomposition

/-- Leaf attachment; construction and degree-count proof follow the paper-linked
Lax263307Proofs.TreeExtensions (commit 68b2d26), adapted to this mission's API. -/
def attachLeaves {α β : Type} (T : SimpleGraph α) (root : α) : SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inl b => T.Adj a b
    | .inl a, .inr _ => a = root
    | .inr _, .inl b => b = root
    | .inr _, .inr _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> simp_all [T.adj_comm]⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

 theorem degree_as_sum {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    G.degree v = ∑ u, if G.Adj v u then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, G.neighborFinset_eq_filter]
  simp

 theorem attachLeaves_tree {α β : Type} [Fintype α] [Fintype β]
    (T : SimpleGraph α) (root : α) (hT : T.IsTree) : (attachLeaves (β := β) T root).IsTree := by
  classical
  let H := attachLeaves (β := β) T root
  let inclusion : T →g H := ⟨Sum.inl, fun h => h⟩
  have hroot : ∀ a : α ⊕ β, H.Reachable a (.inl root) := by
    intro a
    cases a with
    | inl a => exact (hT.connected a root).map inclusion
    | inr b => exact SimpleGraph.Adj.reachable (show H.Adj (.inr b) (.inl root) from rfl)
  have : Nonempty (α ⊕ β) := ⟨.inl root⟩
  have hconn : H.Connected := ⟨fun a b => (hroot a).trans (hroot b).symm⟩
  have hleft (a : α) : H.degree (.inl a) = T.degree a + if a = root then Fintype.card β else 0 := by
    rw [degree_as_sum, Fintype.sum_sum_type, degree_as_sum]
    simp only [H, attachLeaves]
    split_ifs <;> simp_all
  have hright (b : β) : H.degree (.inr b) = 1 := by
    rw [degree_as_sum, Fintype.sum_sum_type]
    simp [H, attachLeaves, eq_comm]
  have hsum : (∑ v, H.degree v) = (∑ a, T.degree a) + 2 * Fintype.card β := by
    rw [Fintype.sum_sum_type]
    simp_rw [hleft, hright]
    simp [Finset.sum_add_distrib]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hcount := hT.card_edgeFinset
  have hhand := H.sum_degrees_eq_twice_card_edges
  rw [hsum, T.sum_degrees_eq_twice_card_edges] at hhand
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_sum,
    ← SimpleGraph.edgeFinset_card]
  omega

 theorem degree_eq {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : degree G v = G.degree v := by
  classical
  rw [degree, Set.ncard_eq_toFinset_card']
  rfl

 noncomputable def highDegree {m : ℕ} (H : SimpleGraph (Fin m)) (s : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun v => s < H.degree v)

 theorem highDegree_card {m : ℕ} (H : SimpleGraph (Fin m)) (s : ℕ) :
    s * (highDegree H s).card ≤ 2 * edgeCount H := by
  classical
  calc
    s * (highDegree H s).card = ∑ _v ∈ highDegree H s, s := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highDegree H s, H.degree v := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.le)
    _ ≤ ∑ v, H.degree v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = 2 * edgeCount H := by rw [edgeCount_eq, SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]

 noncomputable def active {m : ℕ} (H : SimpleGraph (Fin m)) (s : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun v => v ∉ highDegree H s ∧ ∃ u, u ∉ highDegree H s ∧ H.Adj v u)

 theorem active_fiber_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) (s : ℕ) (v : Fin n) :
    ((active H s).filter (fun u => f u = v)).card ≤ s := by
  classical
  by_cases hne : ((active H s).filter (fun u => f u = v)).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have huv : f u = v := (Finset.mem_filter.mp hu).2
    obtain ⟨huS, w, hwS, huw⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    have hdeg : H.degree w ≤ s := by simpa [highDegree] using hwS
    apply le_trans ?_ hdeg
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    have hzv : f z = v := (Finset.mem_filter.mp hz).2
    apply (SimpleGraph.mem_neighborFinset H w z).mpr
    apply (hAdj w z).mpr
    simpa only [hzv, ← huv] using (hAdj w u).mp huw.symm
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

 theorem transfer_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))
    {T : Type} [Fintype T] (tree : SimpleGraph T) (bags : T → Finset (Fin n))
    (dec : IsTreeDecomposition G tree bags) (w s : ℕ) (hsize : ∀ t, (bags t).card ≤ w + 1) :
    ∃ (newTree : SimpleGraph (T ⊕ Fin m)) (newBags : T ⊕ Fin m → Finset (Fin m)),
      IsTreeDecomposition H newTree newBags ∧
      ∀ t, (newBags t).card ≤ (highDegree H s).card + max 1 (s * (w + 1)) := by
  classical
  let S := highDegree H s
  let A := active H s
  let root : T := Classical.choice dec.1.connected.nonempty
  let newTree := attachLeaves (β := Fin m) tree root
  have htree : newTree.IsTree := attachLeaves_tree tree root dec.1
  let newBags : T ⊕ Fin m → Finset (Fin m) := fun t =>
    S ∪ match t with
    | .inl t => A.filter (fun v => f v ∈ bags t)
    | .inr v => if v ∈ A then ∅ else {v}
  have mem_old (t : T) (v : Fin m) : v ∈ newBags (.inl t) ↔ v ∈ S ∨ v ∈ A ∧ f v ∈ bags t := by
    simp [newBags]
  have mem_leaf (u v : Fin m) : v ∈ newBags (.inr u) ↔ v ∈ S ∨ v = u ∧ v ∉ A := by
    by_cases hu : u ∈ A <;> simp [newBags, hu] <;> aesop
  have active_notS {v : Fin m} (hv : v ∈ A) : v ∉ S := (Finset.mem_filter.mp hv).2.1
  have hcover (v : Fin m) : ∃ t, v ∈ newBags t := by
    by_cases hvS : v ∈ S
    · exact ⟨.inl root, (mem_old root v).mpr (Or.inl hvS)⟩
    · by_cases hvA : v ∈ A
      · obtain ⟨t, ht⟩ := dec.2.1 (f v)
        exact ⟨.inl t, (mem_old t v).mpr (Or.inr ⟨hvA, ht⟩)⟩
      · exact ⟨.inr v, (mem_leaf v v).mpr (Or.inr ⟨rfl, hvA⟩)⟩
  refine ⟨newTree, newBags, ⟨htree, hcover, ?_, ?_⟩, ?_⟩
  · intro u v huv
    by_cases huS : u ∈ S
    · obtain ⟨t, ht⟩ := hcover v
      exact ⟨t, Finset.mem_union_left _ huS, ht⟩
    · by_cases hvS : v ∈ S
      · obtain ⟨t, ht⟩ := hcover u
        exact ⟨t, ht, Finset.mem_union_left _ hvS⟩
      · have huA : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huS, v, hvS, huv⟩
        have hvA : v ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS, u, huS, huv.symm⟩
        obtain ⟨t, hut, hvt⟩ := dec.2.2.1 (f u) (f v) ((hAdj u v).mp huv)
        exact ⟨.inl t, (mem_old t u).mpr (Or.inr ⟨huA, hut⟩), (mem_old t v).mpr (Or.inr ⟨hvA, hvt⟩)⟩
  · intro a b c p hp hm v hv
    by_cases hvS : v ∈ S
    · exact Finset.mem_union_left _ hvS
    · have hva := (Finset.mem_inter.mp hv).1
      have hvc := (Finset.mem_inter.mp hv).2
      by_cases hvA : v ∈ A
      · have old_node (t : T ⊕ Fin m) (ht : v ∈ newBags t) : ∃ i : T, t = .inl i ∧ f v ∈ bags i := by
          cases t with
          | inl i => exact ⟨i, rfl, ((mem_old i v).mp ht).resolve_left hvS |>.2⟩
          | inr u => have hh := ((mem_leaf u v).mp ht).resolve_left hvS; exact False.elim (hh.2 hvA)
        obtain ⟨a0, rfl, hfa⟩ := old_node a hva
        obtain ⟨c0, rfl, hfc⟩ := old_node c hvc
        obtain ⟨q, hq⟩ := dec.1.connected.exists_isPath a0 c0
        let incl : tree →g newTree := ⟨Sum.inl, fun h => h⟩
        have hqmap : (q.map incl).IsPath := hq.map Sum.inl_injective
        let := htree.isAcyclic.subsingleton_path (.inl a0) (.inl c0)
        have heq : p = q.map incl := congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩ : newTree.Path (.inl a0) (.inl c0)) ⟨q.map incl,hqmap⟩)
        rw [heq, SimpleGraph.Walk.support_map] at hm
        obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hm
        apply (mem_old b0 v).mpr
        exact Or.inr ⟨hvA, dec.2.2.2 a0 b0 c0 q hq hb0 (Finset.mem_inter.mpr ⟨hfa, hfc⟩)⟩
      · have leaf_node (t : T ⊕ Fin m) (ht : v ∈ newBags t) : t = .inr v := by
          cases t with
          | inl i => have hh := ((mem_old i v).mp ht).resolve_left hvS; exact False.elim (hvA hh.1)
          | inr u => have hh := ((mem_leaf u v).mp ht).resolve_left hvS; exact congrArg Sum.inr hh.1.symm
        have ha := leaf_node a hva
        have hc := leaf_node c hvc
        subst a
        subst c
        let := htree.isAcyclic.subsingleton_path (.inr v) (.inr v)
        have heq : p = .nil := congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩ : newTree.Path (.inr v) (.inr v)) ⟨.nil, SimpleGraph.Walk.IsPath.nil⟩)
        rw [heq] at hm
        have hb : b = .inr v := by simpa using hm
        subst b
        exact hva
  · intro t
    cases t with
    | inl i =>
      have hc : (A.filter (fun v => f v ∈ bags i)).card ≤ s * (w + 1) := by
        rw [← Finset.sum_card_fiberwise_eq_card_filter]
        calc
          _ ≤ ∑ _v ∈ bags i, s := Finset.sum_le_sum (fun v hv => active_fiber_bound G H f hAdj s v)
          _ = (bags i).card * s := by simp
          _ ≤ (w + 1) * s := Nat.mul_le_mul_right _ (hsize i)
          _ = s * (w + 1) := Nat.mul_comm _ _
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_right _ _)) _)
    | inr v =>
      have hc : (if v ∈ A then (∅ : Finset (Fin m)) else {v}).card ≤ 1 := by split_ifs <;> simp
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_left _ _)) _)

 theorem treewidth_witness {n : ℕ} (G : SimpleGraph (Fin n)) : TreewidthLE G (PlantedSubgraphLD.tw G) := by
  have hne : {w : ℕ | TreewidthLE G w}.Nonempty := by
    refine ⟨n, PUnit, inferInstance, ⊥, (fun _ => Finset.univ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨SimpleGraph.Connected.of_subsingleton, by simp⟩
      · intro v; exact ⟨PUnit.unit, Finset.mem_univ _⟩
      · intro u v h; exact ⟨PUnit.unit, Finset.mem_univ _, Finset.mem_univ _⟩
      · intro s s' s'' p hp hm; exact Finset.subset_univ _
    · intro s; simp
  exact Nat.sInf_mem hne

 theorem treewidth_zero {m : ℕ} (H : SimpleGraph (Fin m)) (hz : edgeCount H = 0) :
    PlantedSubgraphLD.tw H = 0 := by
  have hH : H = ⊥ := by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    apply Finset.card_eq_zero.mp
    have hh := hz
    rw [edgeCount_eq] at hh
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hh
  have hS : highDegree H 0 = ∅ := by simp [highDegree, hH]
  obtain ⟨T, inst, tree, bags, dec, size⟩ := treewidth_witness H
  let := inst
  obtain ⟨tr, bs, hd, hsize⟩ := transfer_bound H H id (fun _ _ => Iff.rfl) tree bags dec (PlantedSubgraphLD.tw H) 0 size
  have hw : TreewidthLE H 0 := by
    refine ⟨T ⊕ Fin m, inferInstance, tr, bs, hd, ?_⟩
    intro t
    simpa [hS] using hsize t
  have ht : PlantedSubgraphLD.tw H ≤ 0 := Nat.sInf_le hw
  omega

 theorem power_bound {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m → Fin n) (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))
    (w : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hb1 : b < 1) (hc : 0 < c)
    (hm : 1 ≤ edgeCount H) (hw : TreewidthLE G w)
    (hbound : (w + 1 : ℕ) ≤ c * (edgeCount H : ℝ) ^ b) :
    (PlantedSubgraphLD.tw H : ℝ) ≤ (3 + 2 * c) * (edgeCount H : ℝ) ^ ((1 + b) / 2) := by
  let M : ℝ := edgeCount H
  let α := (1 - b) / 2
  let β := (1 + b) / 2
  let q := M ^ α
  let t := M ^ β
  let s := Nat.ceil q
  have hM : 1 ≤ M := by dsimp [M]; exact_mod_cast hm
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hq : 1 ≤ q := Real.one_le_rpow hM hα
  have ht : 1 ≤ t := Real.one_le_rpow hM hβ
  have hqs : q ≤ (s : ℝ) := Nat.le_ceil q
  have hs : (s : ℝ) ≤ 2 * q := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ q by linarith)).le
    change (s : ℝ) ≤ q + 1 at hceil
    linarith
  have hqt : q * t = M := by
    dsimp [q, t]
    rw [← Real.rpow_add hMpos]
    have he : α + β = 1 := by dsimp [α, β]; ring
    rw [he, Real.rpow_one]
  have hqb : q * M ^ b = t := by
    dsimp [q, t]
    rw [← Real.rpow_add hMpos]
    have he : α + b = β := by dsimp [α, β]; ring
    rw [he]
  have hhigh : ((highDegree H s).card : ℝ) ≤ 2 * t := by
    have hdegree : (s : ℝ) * (highDegree H s).card ≤ 2 * M := by
      dsimp [M]
      exact_mod_cast highDegree_card H s
    have hqX : q * (highDegree H s).card ≤ (s : ℝ) * (highDegree H s).card :=
      mul_le_mul_of_nonneg_right hqs (Nat.cast_nonneg _)
    have hmul : q * (highDegree H s).card ≤ q * (2 * t) := by nlinarith [hqt]
    exact (mul_le_mul_iff_right₀ (show 0 < q by linarith)).mp hmul
  have hlift : (s : ℝ) * (w + 1 : ℕ) ≤ 2 * c * t := by
    calc
      (s : ℝ) * (w + 1 : ℕ) ≤ (2 * q) * (c * M ^ b) :=
        mul_le_mul hs hbound (Nat.cast_nonneg _) (by positivity)
      _ = 2 * c * t := by rw [← hqb]; ring
  obtain ⟨T, inst, tree, bags, dec, size⟩ := hw
  let := inst
  obtain ⟨tr, bs, hd, hsize⟩ := transfer_bound G H f hAdj tree bags dec w s size
  let B := (highDegree H s).card + max 1 (s * (w + 1))
  have hwidth : TreewidthLE H B := by
    refine ⟨T ⊕ Fin m, inferInstance, tr, bs, hd, ?_⟩
    intro j
    exact (hsize j).trans (Nat.le_succ _)
  have htw : (PlantedSubgraphLD.tw H : ℝ) ≤ B := by exact_mod_cast (show PlantedSubgraphLD.tw H ≤ B from Nat.sInf_le hwidth)
  have hB : (B : ℝ) = (highDegree H s).card + max 1 ((s : ℝ) * (w + 1 : ℕ)) := by
    simp [B, Nat.cast_max, Nat.cast_mul]
  rw [hB] at htw
  have hmax : max 1 ((s : ℝ) * (w + 1 : ℕ)) ≤ 1 + (s : ℝ) * (w + 1 : ℕ) :=
    max_le (le_add_of_nonneg_right (by positivity)) (by linarith)
  change (PlantedSubgraphLD.tw H : ℝ) ≤ (3 + 2 * c) * t
  nlinarith

end EdgeSublinearMWIS.Main.BlowupDecomposition


open scoped BigOperators Classical
open EdgeSublinearMWIS.Main
open EdgeSublinearMWIS.Main.StructuralHelpers
open EdgeSublinearMWIS.Main.BlowupDecomposition
open EdgeSublinearMWIS.Main.EdgeCounting
set_option autoImplicit false

theorem solution (C : GraphClass) (a : ℕ) (K : ℝ)
    (hereditary : Hereditary C) (ha : 2 ≤ a) (bound : TreewidthBound C a K) :
    Hereditary (BlowupClass C) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ) (H : SimpleGraph (Fin m)), BlowupClass C m H →
        (PlantedSubgraphLD.tw H : ℝ) ≤
          B * (edgeCount H : ℝ) ^ (1 - 1 / (2 * (a : ℝ)))) ∧
      StronglyEdgeSublinear (BlowupClass C) := by
  have hK : 0 < K := bound.1
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  let b : ℝ := 1 - 1 / a
  let β : ℝ := 1 - 1 / (2 * (a : ℝ))
  have hb : 0 ≤ b := by dsimp [b]; have hi := (div_le_one ha0).mpr (by linarith : (1 : ℝ) ≤ a); linarith
  have hb1 : b < 1 := by dsimp [b]; have hi := one_div_pos.mpr ha0; linarith
  have hβ : 0 ≤ β := by
    dsimp [β]
    have hi := (div_le_one (show (0 : ℝ) < 2 * a by positivity)).mpr (by linarith : (1 : ℝ) ≤ 2 * a)
    linarith
  have hβ1 : β < 1 := by
    dsimp [β]
    have hi : (0 : ℝ) < 1 / (2 * a) := by positivity
    linarith
  have hβpos : 0 < β := by
    dsimp [β]
    have hi := (div_lt_one (show (0 : ℝ) < 2 * a by positivity)).mpr (by linarith : (1 : ℝ) < 2 * a)
    linarith
  have hexp : (1 + b) / 2 = β := by dsimp [b, β]; field_simp; ring
  let B : ℝ := 3 + 2 * (K + 1)
  have hB : 0 < B := by dsimp [B]; linarith
  have hher : Hereditary (BlowupClass C) := blowup_hereditary C hereditary
  have htw : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), BlowupClass C m H →
      (PlantedSubgraphLD.tw H : ℝ) ≤ B * (edgeCount H : ℝ) ^ β := by
    intro m H hH
    by_cases hz : edgeCount H = 0
    · simp [treewidth_zero H hz, hz, Real.zero_rpow (ne_of_gt hβpos)]
    · have hm : 1 ≤ edgeCount H := by omega
      obtain ⟨n, G, hG, f, hsurj, hAdj⟩ := hH
      let rep : Fin n → Fin m := fun v => Classical.choose (hsurj v)
      have hrep : Function.LeftInverse f rep := fun v => Classical.choose_spec (hsurj v)
      let emb : G ↪g H :=
        { toFun := rep
          inj' := hrep.injective
          map_rel_iff' := by
            intro u v
            change H.Adj (rep u) (rep v) ↔ G.Adj u v
            rw [hAdj, hrep u, hrep v] }
      have hedge : edgeCount G ≤ edgeCount H := by
        rw [edgeCount_eq, edgeCount_eq]
        have hh := Fintype.card_le_of_injective emb.mapEdgeSet emb.mapEdgeSet.injective
        simpa only [Set.fintypeCard_eq_ncard] using hh
      have hbase := bound.2 n G hG
      change (PlantedSubgraphLD.tw G : ℝ) ≤ K * (edgeCount G : ℝ) ^ b at hbase
      have hmon : (edgeCount G : ℝ) ^ b ≤ (edgeCount H : ℝ) ^ b :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hedge) hb
      have hpow : (1 : ℝ) ≤ (edgeCount H : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hm) hb
      have hbound : (PlantedSubgraphLD.tw G + 1 : ℕ) ≤ (K + 1) * (edgeCount H : ℝ) ^ b := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hmon hK.le]
      have hh := power_bound G H f hAdj (PlantedSubgraphLD.tw G) b (K + 1) hb hb1
        (by linarith) hm (treewidth_witness G) hbound
      simpa only [hexp] using hh
  refine ⟨hher, ⟨B, hB, htw⟩, hher, β, B + 1, hβ, hβ1, by linarith, ?_⟩
  intro m H hH hm
  obtain ⟨S, hbal, hsize⟩ := treewidth_separator H Finset.univ
  refine ⟨S, hbal, ?_⟩
  have hh := htw m H hH
  have hpow : (1 : ℝ) ≤ (edgeCount H : ℝ) ^ β := Real.one_le_rpow (by exact_mod_cast hm) hβ
  have hs : (S.card : ℝ) ≤ (PlantedSubgraphLD.tw H : ℝ) + 1 := by exact_mod_cast hsize
  nlinarith
