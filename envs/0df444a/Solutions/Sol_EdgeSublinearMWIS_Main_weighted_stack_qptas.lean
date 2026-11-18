-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.weighted_stack_qptas
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:21:46.902512+00:00
-- url     : https://prove2.me/submissions/fb881811-5a3e-4648-b306-b3f200a4af7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator
import Mathlib.Combinatorics.SimpleGraph.Star
import Theorems.Thm_TreewidthApprox_Partition_comp_subset_part
import Theorems.Thm_EdgeSublinearMWIS_Main_theorem_5
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Theorems.Thm_EdgeSublinearMWIS_Main_eq_26
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts
import Mathlib
import Theorems.Thm_EdgeSublinearMWIS_Main_weighted_wrapper
import Theorems.Thm_EdgeSublinearMWIS_Main_weight_rounding
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_16

section

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
end

section

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
end

section

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
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.GraphHelpers

 theorem avoid_refl {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u : Fin n} (hu : u ∉ X) : AvoidReach G X u u := by
  exact ⟨.nil, by simpa using hu⟩

 theorem avoid_symm {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (h : AvoidReach G X u v) : AvoidReach G X v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

 theorem avoid_trans {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v w : Fin n} (h1 : AvoidReach G X u v) (h2 : AvoidReach G X v w) : AvoidReach G X u w := by
  obtain ⟨p1, h1⟩ := h1
  obtain ⟨p2, h2⟩ := h2
  refine ⟨p1.append p2, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact h1 z hz
  · exact h2 z hz

 theorem comp_mem {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (u v : Fin n) :
    v ∈ avoidComp G X u ↔ AvoidReach G X u v := by
  classical
  simp [avoidComp]

 theorem comp_self {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u : Fin n} (hu : u ∉ X) : u ∈ avoidComp G X u :=
  (comp_mem G X u u).mpr (avoid_refl G X hu)

 theorem comp_outside {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (hv : v ∈ avoidComp G X u) : v ∉ X := by
  obtain ⟨p, hp⟩ := (comp_mem G X u v).mp hv
  exact hp v p.end_mem_support

 theorem comp_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (hv : v ∈ avoidComp G X u) : avoidComp G X u = avoidComp G X v := by
  classical
  ext z
  simp only [comp_mem]
  have huv := (comp_mem G X u v).mp hv
  exact ⟨fun h => avoid_trans G X (avoid_symm G X huv) h, fun h => avoid_trans G X huv h⟩

 theorem comp_disjoint_or_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (u v : Fin n) : Disjoint (avoidComp G X u) (avoidComp G X v) ∨
      avoidComp G X u = avoidComp G X v := by
  classical
  by_cases h : Disjoint (avoidComp G X u) (avoidComp G X v)
  · exact Or.inl h
  · obtain ⟨z, hzu, hzv⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inr ((comp_eq G X hzu).trans (comp_eq G X hzv).symm)

 theorem comp_adj {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v w : Fin n} (hv : v ∈ avoidComp G X u) (ha : G.Adj v w) (hw : w ∉ X) :
    w ∈ avoidComp G X u := by
  apply (comp_mem G X u w).mpr
  refine avoid_trans G X ((comp_mem G X u v).mp hv) ⟨ha.toWalk, ?_⟩
  intro z hz
  have hvX := comp_outside G X hv
  simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hvX
  · exact hw

 theorem component_subset {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D : Finset (Fin n)} (hD : D ∈ components G W S) : D ⊆ W \ S := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hD
  intro u hu
  have hx := comp_outside G (S ∪ (Finset.univ \ W)) hu
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or,
    not_not] at hx
  exact Finset.mem_sdiff.mpr ⟨hx.2, hx.1⟩

 theorem component_cover {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {v : Fin n} (hv : v ∈ W \ S) :
    ∃ D ∈ components G W S, v ∈ D := by
  classical
  refine ⟨avoidComp G (S ∪ (Finset.univ \ W)) v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
  apply comp_self
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not]
  exact ⟨(Finset.mem_sdiff.mp hv).2, (Finset.mem_sdiff.mp hv).1⟩

 theorem components_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D E : Finset (Fin n)} (hD : D ∈ components G W S) (hE : E ∈ components G W S) :
    Disjoint D E ∨ D = E := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
  exact comp_disjoint_or_eq G _ u v

 theorem component_noEdge {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D : Finset (Fin n)} (hD : D ∈ components G W S) :
    NoEdge G D ((W \ S) \ D) := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
  intro v hv w hw ha
  have hwWS := (Finset.mem_sdiff.mp hw).1
  have hwX : w ∉ S ∪ (Finset.univ \ W) := by
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not]
    exact ⟨(Finset.mem_sdiff.mp hwWS).2, (Finset.mem_sdiff.mp hwWS).1⟩
  exact (Finset.mem_sdiff.mp hw).2 (comp_adj G _ hv ha hwX)

 theorem balanced_split {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    (hbalanced : Balanced G W S) : ∃ L R : Finset (Fin n),
      IsPartition3 W L S R ∧ NoEdge G L R ∧
        3 * L.card ≤ 2 * W.card ∧ 3 * R.card ≤ 2 * W.card := by
  classical
  let P := components G W S
  let unionOf : Finset (Finset (Fin n)) → Finset (Fin n) := fun A => A.biUnion id
  let candidates := P.powerset.filter (fun A => 3 * (unionOf A).card ≤ 2 * W.card)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, unionOf]
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image (fun A => (unionOf A).card) hne
  have hAP : A ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hcap : 3 * (unionOf A).card ≤ 2 * W.card := (Finset.mem_filter.mp hA).2
  let L := unionOf A
  let R := (W \ S) \ L
  have hL : L ⊆ W \ S := by
    intro v hv
    obtain ⟨D, hDA, hvD⟩ := Finset.mem_biUnion.mp hv
    exact component_subset G W S (hAP hDA) hvD
  have hDmax (D : Finset (Fin n)) (hDP : D ∈ P) : D.card ≤ L.card := by
    have hDcand : {D} ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.singleton_subset_iff.mpr hDP, ?_⟩
      simpa [unionOf] using hbalanced.2 D hDP
    simpa [unionOf] using hmax {D} hDcand
  have hRcap : 3 * R.card ≤ 2 * W.card := by
    by_contra hh
    have hsum : R.card + L.card ≤ W.card := by
      rw [show R.card + L.card = (W \ S).card from Finset.card_sdiff_add_card_eq_card hL]
      exact Finset.card_le_card Finset.sdiff_subset
    have hLsmall : 3 * L.card < W.card := by omega
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hvR⟩ := hRne
    obtain ⟨D, hDP, hvD⟩ := component_cover G W S (Finset.mem_sdiff.mp hvR).1
    have hDdis : Disjoint L D := by
      apply (Finset.disjoint_biUnion_left A id D).mpr
      intro E hEA
      rcases components_disjoint G W S (hAP hEA) hDP with hdis | heq
      · exact hdis
      · have hvL : v ∈ L := Finset.mem_biUnion.mpr ⟨E, hEA, heq.symm ▸ hvD⟩
        exact False.elim ((Finset.mem_sdiff.mp hvR).2 hvL)
    have hDsmall := hDmax D hDP
    have hcard : (unionOf (insert D A)).card = D.card + L.card := by
      simp only [unionOf, Finset.biUnion_insert]
      exact Finset.card_union_of_disjoint hDdis.symm
    have hnew : insert D A ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hDP hAP, ?_⟩
      rw [hcard]
      omega
    have hmax' := hmax (insert D A) hnew
    rw [hcard] at hmax'
    have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨v, hvD⟩
    change D.card + L.card ≤ L.card at hmax'
    omega
  have hNo : NoEdge G L R := by
    intro v hv u hu ha
    obtain ⟨D, hDA, hvD⟩ := Finset.mem_biUnion.mp hv
    have huD : u ∉ D := by
      intro huD
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨D, hDA, huD⟩)
    exact component_noEdge G W S (hAP hDA) v hvD u
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, huD⟩) ha
  refine ⟨L, R, ?_, hNo, hcap, hRcap⟩
  have hS := hbalanced.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvL hvS
    exact (Finset.mem_sdiff.mp (hL hvL)).2 hvS
  · apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact (Finset.mem_sdiff.mp hvR).2 hvL
  · apply Finset.disjoint_left.mpr
    intro v hvS hvR
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvR).1).2 hvS
  · ext v
    have hLv : v ∈ L → v ∈ W := fun h => (Finset.mem_sdiff.mp (hL h)).1
    have hSv : v ∈ S → v ∈ W := fun h => hS h
    simp only [Finset.mem_union, R, Finset.mem_sdiff]
    tauto

end EdgeSublinearMWIS.Main.GraphHelpers
end

section

open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.GraphHelpers TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartitionBridge

 theorem balanced_from_partition {n : ℕ} (G : SimpleGraph (Fin n)) (W L S R : Finset (Fin n))
    (hpart : IsPartition3 W L S R) (hNo : NoEdge G L R)
    (hL : 3 * L.card ≤ 2 * W.card) (hR : 3 * R.card ≤ 2 * W.card) : Balanced G W S := by
  classical
  have hunion := hpart.2.2.2
  have hS : S ⊆ W := by intro x hx; rw [← hunion]; simp [hx]
  have hWS : W \ S = L ∪ R := by
    ext v
    have hLS := Finset.disjoint_left.mp hpart.1
    have hSR := Finset.disjoint_left.mp hpart.2.2.1
    rw [← hunion]
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hX : Finset.univ \ (S ∪ (Finset.univ \ W)) = L ∪ R := by
    rw [← hWS]
    ext v
    simp
    tauto
  have hparts : Disjoint L R ∧ Disjoint L ∅ ∧ Disjoint R ∅ ∧
      L ∪ R ∪ ∅ = Finset.univ \ (S ∪ (Finset.univ \ W)) := by
    refine ⟨hpart.2.1, by simp, by simp, ?_⟩
    simpa only [Finset.union_empty] using hX.symm
  have hno3 : NoEdge G L R ∧ NoEdge G L ∅ ∧ NoEdge G R ∅ := by
    exact ⟨hNo, by simp [NoEdge], by simp [NoEdge]⟩
  obtain ⟨hcompL, hcompR, hcomp0⟩ := TreewidthApprox.Partition.comp_subset_part G _ L R ∅ hparts hno3
  refine ⟨hS, ?_⟩
  intro D hD
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hD
  rw [hWS, Finset.mem_union] at hv
  rcases hv with hv | hv
  · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card (hcompL v hv))).trans hL
  · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card (hcompR v hv))).trans hR

 theorem lift_balanced {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m ↪ Fin n) (W : Finset (Fin n)) (S0 : Finset (Fin m))
    (hW : (Finset.univ.image f) = W)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) (hbal : Balanced H Finset.univ S0) :
    Balanced G W (S0.image f) ∧ (S0.image f).card = S0.card := by
  classical
  obtain ⟨L0, R0, hpart, hNo, hL, hR⟩ := balanced_split H Finset.univ S0 hbal
  have hd {U V : Finset (Fin m)} (hUV : Disjoint U V) : Disjoint (U.image f) (V.image f) := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvV
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hvU
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hvV
    have hwu := f.injective he
    exact Finset.disjoint_left.mp hUV hu (hwu ▸ hw)
  have hpart' : IsPartition3 W (L0.image f) (S0.image f) (R0.image f) := by
    refine ⟨hd hpart.1, hd hpart.2.1, hd hpart.2.2.1, ?_⟩
    rw [← Finset.image_union, ← Finset.image_union, hpart.2.2.2, hW]
  have hNo' : NoEdge G (L0.image f) (R0.image f) := by
    intro u hu v hv hadj
    obtain ⟨u0, hu0, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.mp hv
    exact hNo u0 hu0 v0 hv0 ((hAdj u0 v0).mpr hadj)
  have hcard (U : Finset (Fin m)) : (U.image f).card = U.card := Finset.card_image_of_injective U f.injective
  have hWcard : W.card = (Finset.univ : Finset (Fin m)).card := by rw [← hW, hcard]
  refine ⟨balanced_from_partition G W _ _ _ hpart' hNo' ?_ ?_, hcard S0⟩
  · simpa only [hcard, hWcard] using hL
  · simpa only [hcard, hWcard] using hR

end EdgeSublinearMWIS.Main.PartitionBridge
end

section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.PartitionBridge
open EdgeSublinearMWIS.Main.BlowupDecomposition EdgeSublinearMWIS.Main.EdgeCounting
set_option autoImplicit false

theorem EdgeSublinearMWIS.Main.class_treewidth_bound (C : GraphClass) (hC : StronglyEdgeSublinear C) :
    ∃ (a : ℕ) (K : ℝ), 2 ≤ a ∧ TreewidthBound C a K := by
  obtain ⟨hher, b, c, hb, hb1, hc, hsep⟩ := hC
  obtain ⟨c0, K0, hc0, hK0, htw⟩ := theorem_5
  have hgap : 0 < 1 - b := by linarith
  obtain ⟨a, ha⟩ := exists_nat_gt (max (2 : ℝ) (1 / (1 - b)))
  have haR : (2 : ℝ) ≤ a := (le_max_left _ _).trans ha.le
  have haN : 2 ≤ a := by exact_mod_cast haR
  have ha0 : (0 : ℝ) < a := by linarith
  have hprod : 1 < (a : ℝ) * (1 - b) :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt ha)
  have he : b ≤ 1 - 1 / (a : ℝ) := by
    have hi : 1 / (a : ℝ) ≤ 1 - b := (div_le_iff₀ ha0).mpr (by nlinarith)
    linarith
  have hexppos : (0 : ℝ) < 1 - 1 / (a : ℝ) := by
    have hi : 1 / (a : ℝ) < 1 := (div_lt_one ha0).mpr (by linarith : (1 : ℝ) < a)
    linarith
  refine ⟨a, K0 * (c + 2), haN, mul_pos hK0 (by linarith), ?_⟩
  intro n G hG
  by_cases hz : edgeCount G = 0
  · rw [treewidth_zero G hz]
    simp only [Nat.cast_zero]
    positivity
  · have hm : 1 ≤ edgeCount G := by omega
    let M : ℝ := edgeCount G
    let Q := (c + 1) * M ^ b
    have hM : (1 : ℝ) ≤ M := by dsimp [M]; exact_mod_cast hm
    have hpow : (1 : ℝ) ≤ M ^ b := Real.one_le_rpow hM hb
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hboundW : ∀ W : Finset (Fin n), ∃ S, Balanced G W S ∧ S.card ≤ Nat.ceil Q := by
      intro W
      let V := {v : Fin n // v ∈ W}
      let r := Fintype.card V
      let e : V ≃ Fin r := Fintype.equivFin V
      let inc : Fin r ↪ Fin n := ⟨fun v => (e.symm v).val, Subtype.val_injective.comp e.symm.injective⟩
      let H := G.comap inc
      have hH : C r H := hher G H inc hG (fun _ _ => Iff.rfl)
      have hAdj : ∀ u v, H.Adj u v ↔ G.Adj (inc u) (inc v) := fun _ _ => Iff.rfl
      have himg : Finset.univ.image inc = W := by
        ext v
        constructor
        · intro hv
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
          exact (e.symm u).property
        · intro hv
          refine Finset.mem_image.mpr ⟨e ⟨v,hv⟩, Finset.mem_univ _, ?_⟩
          simp [inc]
      let emb : H ↪g G := { toFun := inc, inj' := inc.injective, map_rel_iff' := Iff.rfl }
      have hedge : edgeCount H ≤ edgeCount G := by
        rw [edgeCount_eq, edgeCount_eq]
        have hh := Fintype.card_le_of_injective emb.mapEdgeSet emb.mapEdgeSet.injective
        simpa only [Set.fintypeCard_eq_ncard] using hh
      have hsmall : ∃ S0, Balanced H Finset.univ S0 ∧ (S0.card : ℝ) ≤ Q := by
        by_cases hzH : edgeCount H = 0
        · obtain ⟨S0, hb0, hcard⟩ := treewidth_separator H Finset.univ
          refine ⟨S0, hb0, ?_⟩
          have hs : (S0.card : ℝ) ≤ 1 := by simpa only [treewidth_zero H hzH, zero_add, Nat.cast_one] using (show (S0.card : ℝ) ≤ (PlantedSubgraphLD.tw H + 1 : ℕ) by exact_mod_cast hcard)
          dsimp [Q]
          nlinarith
        · obtain ⟨S0, hb0, hcard⟩ := hsep r H hH (by omega)
          have hmon : (edgeCount H : ℝ) ^ b ≤ M ^ b :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by dsimp [M]; exact_mod_cast hedge) hb
          refine ⟨S0, hb0, ?_⟩
          dsimp [Q]
          nlinarith [mul_le_mul_of_nonneg_left hmon hc.le]
      obtain ⟨S0, hb0, hcard⟩ := hsmall
      obtain ⟨hbal, hcardeq⟩ := lift_balanced G H inc W S0 himg hAdj hb0
      refine ⟨S0.image inc, hbal, ?_⟩
      rw [hcardeq]
      exact_mod_cast (hcard.trans (Nat.le_ceil Q))
    have hsn : separationNumber G ≤ Nat.ceil Q := Nat.sInf_le hboundW
    have hsnR : (separationNumber G : ℝ) ≤ Nat.ceil Q := by exact_mod_cast hsn
    have hceil : (Nat.ceil Q : ℝ) ≤ (c + 2) * M ^ b := by
      have hh := (Nat.ceil_lt_add_one hQ).le
      dsimp [Q] at hh
      nlinarith
    have htwG := (htw n G hm).2
    have htwM : (PlantedSubgraphLD.tw G : ℝ) ≤ K0 * (c + 2) * M ^ b := by
      nlinarith [mul_le_mul_of_nonneg_left (hsnR.trans hceil) hK0.le]
    have hp : M ^ b ≤ M ^ (1 - 1 / (a : ℝ)) := Real.rpow_le_rpow_of_exponent_le hM he
    exact htwM.trans (mul_le_mul_of_nonneg_left hp (by positivity))
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedHelpers

 def beforeCount {n : ℕ} (t : Fin n → ℕ) (v : Fin n) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => u < v), t u

 theorem beforeCount_add {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    beforeCount t v + t v = ∑ u ∈ Finset.univ.filter (fun u => u ≤ v), t u := by
  classical
  have hset : Finset.univ.filter (fun u : Fin n => u ≤ v) =
      insert v (Finset.univ.filter (fun u : Fin n => u < v)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    exact le_iff_lt_or_eq.trans or_comm
  rw [hset, Finset.sum_insert (by simp)]
  exact Nat.add_comm _ _

 theorem beforeCount_le_total {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    beforeCount t v + t v ≤ totalCopies t := by
  classical
  rw [beforeCount_add]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

 theorem cumulative_le_beforeCount {n : ℕ} (t : Fin n → ℕ) {u v : Fin n} (huv : u < v) :
    (∑ x ∈ Finset.univ.filter (fun x => x ≤ u), t x) ≤ beforeCount t v := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_le_of_lt hx huv

 theorem owner_of_interval {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t))
    (v : Fin n) (lo : beforeCount t v ≤ j.val) (hi : j.val < beforeCount t v + t v) :
    copyOwner t j = some v := by
  classical
  unfold copyOwner
  rw [show List.finRange n = List.ofFn (fun v : Fin n => v) from rfl]
  apply (List.find?_ofFn_eq_some_of_injective (Function.injective_id)).mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, decide_eq_true_eq, ← beforeCount_add] using hi
  · intro u huv
    simp only [decide_eq_true_eq, not_lt]
    exact (cumulative_le_beforeCount t huv).trans lo

 theorem owner_interval {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t))
    (v : Fin n) (h : copyOwner t j = some v) :
    beforeCount t v ≤ j.val ∧ j.val < beforeCount t v + t v := by
  classical
  unfold copyOwner at h
  rw [show List.finRange n = List.ofFn (fun v : Fin n => v) from rfl] at h
  have hh := (List.find?_ofFn_eq_some_of_injective (Function.injective_id)).mp h
  simp only [id_eq] at hh
  have hi : j.val < beforeCount t v + t v := by
    simpa only [decide_eq_true_eq, ← beforeCount_add] using hh.1
  refine ⟨?_, hi⟩
  by_cases hz : v.val = 0
  · have hv : ∀ u : Fin n, ¬ u < v := by intro u; simp only [Fin.lt_def]; omega
    simp [beforeCount, hv]
  · let u : Fin n := ⟨v.val - 1, by omega⟩
    have huv : u < v := by simp only [Fin.lt_def]; dsimp [u]; omega
    have hu := hh.2 u huv
    simp only [decide_eq_true_eq, not_lt] at hu
    have hset : Finset.univ.filter (fun x : Fin n => x ≤ u) =
        Finset.univ.filter (fun x : Fin n => x < v) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val,
        Fin.lt_def]
      dsimp [u]
      omega
    simpa [hset, beforeCount] using hu

 def copyIndex {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (i : Fin (t v)) :
    Fin (totalCopies t) :=
  ⟨beforeCount t v + i.val, (Nat.add_lt_add_left i.isLt _).trans_le (beforeCount_le_total t v)⟩

 theorem owner_copyIndex {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (i : Fin (t v)) :
    copyOwner t (copyIndex t v i) = some v := by
  apply owner_of_interval
  · exact Nat.le_add_right _ _
  · exact Nat.add_lt_add_left i.isLt _

 theorem owner_exists {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    ∃ v, copyOwner t j = some v := by
  classical
  by_contra h
  have hnone : copyOwner t j = none := by
    cases he : copyOwner t j with
    | none => rfl
    | some v => exact False.elim (h ⟨v, he⟩)
  unfold copyOwner at hnone
  have hf := List.find?_eq_none.mp hnone
  by_cases hn : n = 0
  · subst n
    have hz : totalCopies t = 0 := by simp [totalCopies]
    have := j.isLt
    omega
  · let v : Fin n := ⟨n-1, by omega⟩
    have hp := hf v (by simp)
    simp only [decide_eq_true_eq, not_lt] at hp
    have heq : Finset.univ.filter (fun u : Fin n => u ≤ v) = Finset.univ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
      dsimp [v]
      have hu := u.isLt
      exact iff_true_intro (Nat.le_pred_of_lt u.isLt)
    rw [heq] at hp
    exact Nat.not_le_of_lt j.isLt hp

noncomputable def fiberEquiv {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    {j : Fin (totalCopies t) // copyOwner t j = some v} ≃ Fin (t v) where
  toFun j := ⟨j.val.val - beforeCount t v, by
    have h := owner_interval t j.val v j.property
    omega⟩
  invFun i := ⟨copyIndex t v i, owner_copyIndex t v i⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp [copyIndex]
    have h := (owner_interval t j.val v j.property).1
    omega
  right_inv i := by
    apply Fin.ext
    simp [copyIndex]

 theorem fiber_card {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    (Finset.univ.filter (fun j => copyOwner t j = some v)).card = t v := by
  classical
  simpa only [Fintype.card_coe, Fintype.card_fin, Finset.card_univ, Fintype.card_subtype]
    using Fintype.card_congr (fiberEquiv t v)

 theorem max_weight_le {n : ℕ} (w : Fin n → ℚ) (v : Fin n) :
    w v ≤ maximumWeight w := by
  have hne : List.ofFn w ≠ [] := List.ne_nil_of_mem (List.mem_ofFn.mpr ⟨v, rfl⟩)
  unfold maximumWeight
  rw [List.foldl_max_eq_max hne]
  exact (List.le_max_of_mem (List.mem_ofFn.mpr ⟨v, rfl⟩)).trans (le_max_right _ _)

 theorem max_weight_attained {n : ℕ} (w : Fin n → ℚ) (hpos : 0 < maximumWeight w) :
    ∃ v, maximumWeight w = w v := by
  have hne : List.ofFn w ≠ [] := by
    intro h
    have : maximumWeight w = 0 := by simp [maximumWeight, h]
    linarith
  have hEq : maximumWeight w = (List.ofFn w).max hne := by
    unfold maximumWeight at *
    rw [List.foldl_max_eq_max hne] at *
    exact max_eq_right (by by_contra h; rw [max_eq_left (le_of_not_ge h)] at hpos; linarith)
  have hmem := List.max_mem hne
  obtain ⟨v, hv⟩ := List.mem_ofFn.mp hmem
  exact ⟨v, hEq.trans hv.symm⟩

 theorem weightedAlpha_bdd {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) : BddAbove {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
      z = ∑ v ∈ I, (w v : ℝ)} := by
  classical
  apply (Set.finite_range (fun I : Finset (Fin n) => ∑ v ∈ I, (w v : ℝ))).bddAbove.mono
  rintro z ⟨I, hI, hi, rfl⟩
  exact Set.mem_range_self _

 theorem weightedAlpha_member {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) (I : Finset (Fin n)) (hI : I ⊆ W) (hind : G.IsIndepSet (I : Set (Fin n))) :
    (∑ v ∈ I, (w v : ℝ)) ≤ weightedAlphaOn G W w := by
  exact le_csSup (weightedAlpha_bdd G W w) ⟨I, hI, hind, rfl⟩

 theorem weightedAlpha_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) : ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
      weightedAlphaOn G W w = ∑ v ∈ I, (w v : ℝ) := by
  classical
  let S := {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧ z = ∑ v ∈ I, (w v : ℝ)}
  have hne : S.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, by simp⟩
    simp
  have hfin : S.Finite := by
    apply (Set.finite_range (fun I : Finset (Fin n) => ∑ v ∈ I, (w v : ℝ))).subset
    rintro z ⟨I, hI, hi, rfl⟩
    exact Set.mem_range_self _
  exact hne.csSup_mem hfin

noncomputable def owner {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) : Fin n :=
  Classical.choose (owner_exists t j)

 theorem owner_spec {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    copyOwner t j = some (owner t j) := Classical.choose_spec (owner_exists t j)

 theorem owner_eq_iff {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) (v : Fin n) :
    owner t j = v ↔ copyOwner t j = some v := by
  rw [owner_spec, Option.some.injEq]

 theorem owner_fiber_card {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    (Finset.univ.filter (fun j => owner t j = v)).card = t v := by
  classical
  simp only [owner_eq_iff]
  exact fiber_card t v

 theorem rounded_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (i j : Fin (totalCopies t)) :
    (roundedGraph G t).Adj i j ↔ G.Adj (owner t i) (owner t j) := by
  constructor
  · rintro ⟨u, v, hu, hv, hadj⟩
    rw [← (owner_eq_iff t i u).mpr hu, ← (owner_eq_iff t j v).mpr hv] at hadj
    exact hadj
  · intro h
    exact ⟨owner t i, owner t j, owner_spec t i, owner_spec t j, h⟩

 theorem lift_card {n : ℕ} (t : Fin n → ℕ) (I : Finset (Fin n)) :
    (Finset.univ.filter (fun j => owner t j ∈ I)).card = ∑ v ∈ I, t v := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.sum_congr rfl (fun v hv => owner_fiber_card t v)

 theorem lift_independent {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin n)) (hind : G.IsIndepSet (I : Set (Fin n))) :
    (roundedGraph G t).IsIndepSet (Finset.univ.filter (fun j => owner t j ∈ I) : Set (Fin (totalCopies t))) := by
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro i hi j hj hij hadj
  have h := (rounded_adj_iff G t i j).mp hadj
  exact hind (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (G.ne_of_adj h) h

 theorem alpha_lift_bound {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin n)) (hind : G.IsIndepSet (I : Set (Fin n))) :
    ∑ v ∈ I, t v ≤ alpha (roundedGraph G t) Finset.univ := by
  classical
  rw [← lift_card]
  unfold alpha
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, lift_independent G t I hind⟩

 theorem originalVertices_eq {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : originalVertices t I = I.image (owner t) := by
  classical
  ext v
  simp only [originalVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, owner_eq_iff]

 theorem projection_independent {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t)))
    (hind : (roundedGraph G t).IsIndepSet (I : Set (Fin (totalCopies t)))) :
    G.IsIndepSet (originalVertices t I : Set (Fin n)) := by
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro u hu v hv huv hadj
  rw [originalVertices_eq] at hu hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have h := (rounded_adj_iff G t i j).mpr hadj
  exact hind hi hj ((roundedGraph G t).ne_of_adj h) h

 theorem projection_card_bound {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : I.card ≤ ∑ v ∈ originalVertices t I, t v := by
  classical
  rw [originalVertices_eq, Finset.card_eq_sum_card_image (owner t) I]
  apply Finset.sum_le_sum
  intro v hv
  rw [← owner_fiber_card t v]
  exact Finset.card_le_card (by intro j hj; simp_all only [Finset.mem_filter, Finset.mem_univ, true_and])

 theorem maximumWeight_le_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (hpos : 0 < maximumWeight w) : (maximumWeight w : ℝ) ≤ weightedAlpha G w := by
  classical
  obtain ⟨v, hv⟩ := max_weight_attained w hpos
  rw [hv]
  have h := weightedAlpha_member G Finset.univ w {v} (Finset.subset_univ _) (by simp)
  simpa [weightedAlpha] using h

 theorem owner_positive {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    0 < t (owner t j) := by
  have h := owner_interval t j (owner t j) (owner_spec t j)
  omega

 theorem rounded_mem_blowup {n : ℕ} (C : GraphClass) (G : SimpleGraph (Fin n))
    (hC : Hereditary C) (hG : C n G) (t : Fin n → ℕ) :
    BlowupClass C (totalCopies t) (roundedGraph G t) := by
  classical
  let V := {v : Fin n // 0 < t v}
  let m := Fintype.card V
  let e : V ≃ Fin m := Fintype.equivFin V
  let inc : Fin m ↪ Fin n :=
    ⟨fun v => (e.symm v).val, (Subtype.val_injective.comp e.symm.injective)⟩
  let H : SimpleGraph (Fin m) := G.comap inc
  have hH : C m H := hC G H inc hG (fun u v => Iff.rfl)
  let f : Fin (totalCopies t) → Fin m := fun j => e ⟨owner t j, owner_positive t j⟩
  refine ⟨m, H, hH, f, ?_, ?_⟩
  · intro v
    let u : V := e.symm v
    let j := copyIndex t u.val ⟨0, u.property⟩
    have hj : owner t j = u.val := (owner_eq_iff t j u.val).mpr (owner_copyIndex t u.val ⟨0, u.property⟩)
    refine ⟨j, ?_⟩
    dsimp [f]
    have hh : (⟨owner t j, owner_positive t j⟩ : V) = u := Subtype.ext hj
    rw [hh]
    exact e.apply_symm_apply v
  · intro i j
    change (roundedGraph G t).Adj i j ↔ G.Adj (inc (f i)) (inc (f j))
    simp only [inc, f, Equiv.symm_apply_apply, Function.Embedding.coeFn_mk]
    exact rounded_adj_iff G t i j

end EdgeSublinearMWIS.Main.WeightedHelpers
end

section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.WeightedHelpers
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedExecutionMath

 theorem clipped_value (w : RationalCode) : (clippedCode w).value = max w.value 0 := by
  have hd : (0 : ℚ) < w.denominator := by exact_mod_cast w.positive
  unfold clippedCode RationalCode.value
  push_cast
  rw [← max_div_div_right (le_of_lt hd)]
  simp

 theorem clipped_nonneg {n : ℕ} (w : Fin n → RationalCode) (v : Fin n) : 0 ≤ clippedValues w v := by
  simp only [clippedValues, clipped_value]
  exact le_max_right _ _

 theorem half_value (ε : RationalCode) : (halfAccuracy ε).value = ε.value / 2 := by
  unfold halfAccuracy RationalCode.value
  push_cast
  ring

 theorem clipped_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) :
    weightedAlpha G (clippedValues w) = weightedAlpha G (fun v => (w v).value) := by
  unfold weightedAlpha weightedAlphaOn
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨I, hI, hi, rfl⟩
    let J := I.filter (fun v => 0 ≤ (w v).value)
    refine ⟨∑ v ∈ J, ((w v).value : ℝ), ⟨J, Finset.subset_univ _, hi.mono (by intro v hv; exact (Finset.mem_filter.mp hv).1), rfl⟩, ?_⟩
    have heq : (∑ v ∈ I, (clippedValues w v : ℝ)) = ∑ v ∈ J, ((w v).value : ℝ) := by
      dsimp [J]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [clippedValues, clipped_value]
      split_ifs with h
      · rw [max_eq_left h]
      · rw [max_eq_right (le_of_not_ge h)]
        simp
    exact heq.le
  · rintro x ⟨I, hI, hi, rfl⟩
    refine ⟨∑ v ∈ I, (clippedValues w v : ℝ), ⟨I, hI, hi, rfl⟩, ?_⟩
    apply Finset.sum_le_sum
    intro v hv
    simp only [clippedValues, clipped_value]
    exact_mod_cast (le_max_left (w v).value 0)

 theorem nonpositive_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (hw : ∀ v, w v ≤ 0) : weightedAlpha G w = 0 := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ∅, Finset.empty_subset _, by simp, by simp⟩
    · rintro x ⟨I, hI, hi, rfl⟩
      exact Finset.sum_nonpos (fun v hv => by exact_mod_cast hw v)
  · have h := weightedAlpha_member G Finset.univ w ∅ (Finset.empty_subset _) (by simp)
    simpa [weightedAlpha] using h

 theorem alpha_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) : 0 ≤ weightedAlpha G w := by
  have h := weightedAlpha_member G Finset.univ w ∅ (Finset.empty_subset _) (by simp)
  simpa [weightedAlpha] using h

 theorem direct_correct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode)
    (hn : n ≤ 1) : G.IsIndepSet (directVertices w : Set (Fin n)) ∧
      weightedAlpha G (fun v => (w v).value) = ∑ v ∈ directVertices w, ((w v).value : ℝ) := by
  have hind : G.IsIndepSet (directVertices w : Set (Fin n)) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv hne
    have hu' := u.isLt
    have hv' := v.isLt
    have heq : u = v := Fin.ext (by omega)
    exact False.elim (hne heq)
  refine ⟨hind, le_antisymm ?_ ?_⟩
  · apply csSup_le
    · exact ⟨0, ∅, Finset.empty_subset _, by simp, by simp⟩
    · rintro x ⟨I, hI, hi, rfl⟩
      have hsum1 : (∑ v ∈ I, ((w v).value : ℝ)) ≤ ∑ v ∈ I, (clippedValues w v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        simp only [clippedValues, clipped_value]
        exact_mod_cast (le_max_left (w v).value 0)
      have hsum2 : (∑ v ∈ I, (clippedValues w v : ℝ)) ≤ ∑ v : Fin n, (clippedValues w v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v hv hnot => by exact_mod_cast clipped_nonneg w v)
      have heq : (∑ v : Fin n, (clippedValues w v : ℝ)) = ∑ v ∈ directVertices w, ((w v).value : ℝ) := by
        unfold directVertices
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v hv
        simp only [clippedValues, clipped_value]
        split_ifs with h
        · rw [max_eq_left h]
        · rw [max_eq_right (le_of_not_ge h)]
          simp
      exact hsum1.trans (hsum2.trans heq.le)
  · exact weightedAlpha_member G Finset.univ _ (directVertices w) (Finset.subset_univ _) hind

 theorem projection_original_weights {n : ℕ} (w : Fin n → RationalCode) (τ : ℚ) (t : Fin n → ℕ)
    (ht : ∀ v, t v = ⌊clippedValues w v / τ⌋₊) (J : Finset (Fin (totalCopies t))) :
    (∑ v ∈ originalVertices t J, (clippedValues w v : ℝ)) =
      ∑ v ∈ originalVertices t J, ((w v).value : ℝ) := by
  apply Finset.sum_congr rfl
  intro v hv
  have hnon : 0 ≤ (w v).value := by
    by_contra hh
    have hneg : (w v).value ≤ 0 := le_of_lt (lt_of_not_ge hh)
    have hz : clippedValues w v = 0 := by simp [clippedValues, clipped_value, max_eq_right hneg]
    have htv : t v = 0 := by rw [ht v, hz]; simp
    obtain ⟨j, hj, howner⟩ := (Finset.mem_filter.mp hv).2
    have hown := (owner_eq_iff t j v).mpr howner
    have hp := owner_positive t j
    rw [hown, htv] at hp
    omega
  simp only [clippedValues, clipped_value, max_eq_left hnon]

 theorem rounding_large {n : ℕ} (w : Fin n → ℚ) (ε τ : ℚ) (t : Fin n → ℕ)
    (hn : 2 ≤ n) (hmax : 0 < maximumWeight w) (he : 0 < ε) (he1 : ε < 1)
    (hτ : 0 < τ) (hscale : τ = ε * maximumWeight w / (2 * (n : ℚ)))
    (ht : ∀ v, t v = ⌊w v / τ⌋₊) : 2 ≤ totalCopies t := by
  obtain ⟨v, hv⟩ := max_weight_attained w hmax
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hnq)
  have hscaled : τ * (2 * (n : ℚ)) = ε * maximumWeight w := by rw [hscale]; field_simp
  have hmul : ε * maximumWeight w < maximumWeight w := by nlinarith
  have h2τ : 2 * τ ≤ w v := by rw [← hv]; nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hnq)]
  have htwo : 2 ≤ t v := by
    rw [ht]
    apply Nat.le_floor
    exact (le_div_iff₀ hτ).mpr (by simpa [mul_comm] using h2τ)
  apply htwo.trans
  exact Finset.single_le_sum (fun v hv => Nat.zero_le _) (Finset.mem_univ _)

end EdgeSublinearMWIS.Main.WeightedExecutionMath
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.UnweightedStack

lemma height_pos {n : ℕ} (hn : 2 ≤ n) : 0 < height n := by
  unfold height
  generalize he : (List.range (2 * n + 1)).find? (fun j => decide (2 ^ j * n ≤ 3 ^ j)) = o
  cases o with
  | none => simp; omega
  | some j =>
    simp only [Option.getD_some]
    have hj := List.find?_some he
    simp only [decide_eq_true_eq] at hj
    by_contra h
    have : j = 0 := by omega
    subst j
    norm_num at hj
    omega

lemma accuracy_factor (B a n : ℕ) (ε : ℚ) (he : 0 < ε) (he1 : ε < 1) :
    1 - (ε : ℝ) ≤ (1 - ((parameters B a n ε).delta : ℝ)) ^ height n := by
  by_cases hn : n ≤ 1
  · simp [parameters, hn]
    exact_mod_cast le_of_lt he
  · have hh := height_pos (n := n) (by omega)
    have hhr : (0 : ℝ) < height n := by exact_mod_cast hh
    have heR : (0 : ℝ) < ε := by exact_mod_cast he
    have he1R : (ε : ℝ) < 1 := by exact_mod_cast he1
    have hdiv : (ε : ℝ) / height n ≤ 1 := by
      apply (div_le_iff₀ hhr).mpr
      have : (1 : ℝ) ≤ height n := by exact_mod_cast hh
      linarith
    have hb := one_add_mul_le_pow (a := -((ε : ℝ) / height n)) (by linarith : (-2 : ℝ) ≤ -((ε : ℝ) / height n)) (height n)
    have heq : (height n : ℝ) * -((ε : ℝ) / height n) = -(ε : ℝ) := by field_simp
    rw [heq] at hb
    simpa [parameters, hn, Rat.cast_div, Rat.cast_natCast, sub_eq_add_neg] using hb


 theorem unweighted_scheme :
    ∃ q : ℕ, 0 < q ∧ ∀ (C : GraphClass) (a : ℕ) (K : ℝ),
      StronglyEdgeSublinear C → 2 ≤ a → TreewidthBound C a K →
      ∃ (U : Program) (D : ℝ), 0 < D ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : RationalCode),
          2 ≤ n → C n G → 0 < ε.value → ε.value < 1 →
          ∃ (I : Finset (Fin n)) (u t : ℕ),
            Runs U (unweightedInput G ε) (mask I ++ encodeNat u) t ∧
            G.IsIndepSet (I : Set (Fin n)) ∧
            (1 - (ε.value : ℝ)) * alpha G Finset.univ ≤ (I.card : ℝ) ∧
            (t : ℝ) ≤ D * (ε.bits.length + 1 : ℝ) ^ q +
              D * (2 : ℝ) ^ (D * (ε.value : ℝ)⁻¹ ^ (4 * a - 2) *
                logTwo n ^ (8 * a - 1)) := by
  obtain ⟨q, hq, hsource⟩ := eq_26
  refine ⟨q, hq, ?_⟩
  intro C a K hC ha hbound
  obtain ⟨B, M, U, D, hB, hD, hprimitive, hinv, hex⟩ := hsource C a K hC ha hbound
  refine ⟨U, D, hD, ?_⟩
  intro n G ε hn hG he he1
  have hcall := hex n G ε hn hG he he1
  dsimp only at hcall
  obtain ⟨helower, heupper, I, u, t, hExec, hRun, htime1, htime2, htime3, htime4⟩ := hcall
  let e := roundedAccuracy ε.value
  have he0 : 0 < e := by dsimp [e]; linarith
  have he1' : e < 1 := lt_of_le_of_lt heupper he1
  obtain ⟨hsub, hind, halpha, hu, hsize⟩ := (hinv n G e Finset.univ hG he0 he1').2 I u hExec
  refine ⟨I, u, t, hRun, hind, ?_, htime4⟩
  have hfac := accuracy_factor B a n e he0 he1'
  have hnon : (0 : ℝ) ≤ 1 - e := by exact_mod_cast sub_nonneg.mpr he1'.le
  have heR : (e : ℝ) ≤ ε.value := by exact_mod_cast heupper
  have haR : (alpha G Finset.univ : ℝ) ≤ u := by exact_mod_cast halpha
  have hsum := mul_le_mul_of_nonneg_left haR hnon
  have hsize' := mul_le_mul_of_nonneg_right hfac (Nat.cast_nonneg u (α := ℝ))
  have hsizeR : (1 - ((parameters B a n e).delta : ℝ)) ^ height n * u ≤ (I.card : ℝ) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hsize
  have halpha0 := Nat.cast_nonneg (α := ℝ) (alpha G Finset.univ)
  nlinarith

end EdgeSublinearMWIS.Main.UnweightedStack
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EncodingBounds

 theorem natBits_length (n : ℕ) : (natBits n).length ≤ n := by
  simpa only [natBits, List.length_map] using
    (Nat.digits_length_le_iff (by decide : 1 < 2) n).mpr (show n < 2 ^ n from Nat.lt_two_pow_self)

 theorem encodeNat_length (n : ℕ) : (encodeNat n).length ≤ 2 * n + 1 := by
  have h := natBits_length n
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  omega

 theorem rationalBits_length (r : RationalCode) : 1 ≤ r.bits.length := by
  simp only [RationalCode.bits, encodeInt, List.length_append, List.length_singleton]
  omega

 theorem order_le_data {n : ℕ} (w : Fin n → RationalCode) (ε : RationalCode) :
    n ≤ (rationalData w ε).length := by
  have hsum : (∑ _v : Fin n, 1) ≤ ∑ v : Fin n, (w v).bits.length :=
    Finset.sum_le_sum (fun v hv => rationalBits_length (w v))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  have heq : (rationalData w ε).length = (∑ v, (w v).bits.length) + ε.bits.length := by
    simp [rationalData, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  omega

 theorem graphBits_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphBits G).length ≤ (n + 1) ^ 2 := by
  classical
  have hpart (u : Fin n) : ((List.finRange n).filter (fun v => u < v)).length ≤ n := by
    simpa using (List.length_filter_le (fun v : Fin n => decide (u < v)) (List.finRange n))
  have hsum : (∑ u : Fin n, ((List.finRange n).filter (fun v => u < v)).length) ≤ n * n := by
    calc
      _ ≤ ∑ _u : Fin n, n := Finset.sum_le_sum (fun v hv => hpart v)
      _ = n * n := by simp
  have heq : (graphBits G).length = (encodeNat n).length +
      ∑ u : Fin n, ((List.finRange n).filter (fun v => u < v)).length := by
    simp [graphBits, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]
  have henc := encodeNat_length n
  nlinarith

 theorem input_length {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
    (weightedInput G w ε).length + 1 ≤ 3 * ((rationalData w ε).length + 1) ^ 2 := by
  have hn := order_le_data w ε
  have hg := graphBits_length G
  simp only [weightedInput, List.length_append]
  nlinarith

end EdgeSublinearMWIS.Main.EncodingBounds
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedRuntime

 theorem half_bits (ε : RationalCode) : (halfAccuracy ε).bits.length = ε.bits.length + 2 := by
  unfold RationalCode.bits halfAccuracy encodeNat natBits
  rw [Nat.digits_base_mul (by decide : 1 < 2) ε.positive]
  simp [List.length_append, List.length_replicate]
  omega

 theorem log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have hlo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  have hhi := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_inv] at hlo
  constructor <;> linarith

 theorem blowup_log (n N : ℕ) (ε : ℝ) (hn : 2 ≤ n) (hN : 2 ≤ N)
    (he : 0 < ε) (he1 : ε < 1) (hsize : (N : ℝ) ≤ 2 * (n : ℝ) ^ 2 / ε) :
    let X := ε⁻¹ * logTwo n
    1 ≤ X ∧ ε⁻¹ ≤ X ∧ logTwo n ≤ X ∧ logTwo N ≤ 5 * X := by
  let L := logTwo n
  let E := ε⁻¹
  let X := E * L
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 1 ≤ L := by
    dsimp [L, logTwo]
    apply (le_div_iff₀ hlog).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
  have hE : 1 ≤ E := by
    dsimp [E]
    rw [inv_eq_one_div]
    exact (le_div_iff₀ he).mpr (by linarith)
  have hE0 : 0 < E := by dsimp [E]; positivity
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hE hL
  have hEL : E ≤ X := by dsimp [X]; nlinarith
  have hLX : L ≤ X := by dsimp [X]; nlinarith
  have hlogE : Real.log E / Real.log 2 ≤ 2 * E := by
    apply (div_le_iff₀ hlog).mpr
    have hb := log_two_bounds.1
    have hh := Real.log_le_sub_one_of_pos hE0
    nlinarith
  have hprod : (0 : ℝ) < 2 * (n : ℝ) ^ 2 * E := by positivity
  have hlogN : Real.log N ≤ Real.log 2 + 2 * Real.log n + Real.log E := by
    have hh := Real.log_le_log (show (0 : ℝ) < N by linarith) (show (N : ℝ) ≤ 2 * (n : ℝ) ^ 2 * E by simpa [E, div_eq_mul_inv] using hsize)
    rw [Real.log_mul (by positivity) (ne_of_gt hE0), Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    exact hh
  have hLN : logTwo N ≤ 1 + 2 * L + 2 * E := by
    dsimp [logTwo]
    apply (div_le_iff₀ hlog).mpr
    have hLeq : L * Real.log 2 = Real.log n := by dsimp [L, logTwo]; field_simp
    have hEE : Real.log E ≤ 2 * E * Real.log 2 := (div_le_iff₀ hlog).mp hlogE
    nlinarith
  exact ⟨hX, hEL, hLX, by nlinarith⟩

 theorem runtime_envelope (q a : ℕ) (D : ℝ) (ha : 2 ≤ a) (hD : 0 < D) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ 0 < d ∧
      ∀ (n N ell T : ℕ) (ε : ℝ), 2 ≤ n → 2 ≤ N → 0 < ε → ε < 1 →
        (N : ℝ) ≤ 2 * (n : ℝ) ^ 2 / ε →
        (T : ℝ) ≤ D * (ell + 3 : ℝ) ^ q +
          D * (2 : ℝ) ^ (D * (ε / 2)⁻¹ ^ (4 * a - 2) * logTwo N ^ (8 * a - 1)) →
        (T + N : ℝ) ≤ K * Real.exp (K * (ε⁻¹ * logTwo n) ^ d) + K * (ell + 1 : ℝ) ^ q := by
  let p := 4 * a - 2
  let r := 8 * a - 1
  let d := p + r
  let B := D * (2 : ℝ) ^ p * (5 : ℝ) ^ r
  let C := D * (3 : ℝ) ^ q
  let K := B + C + D + 10
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have hBK : B ≤ K := by dsimp [K]; linarith
  have hCK : C ≤ K := by dsimp [K]; linarith
  have hDK : D + 1 ≤ K := by dsimp [K]; linarith
  have h5K : (5 : ℝ) ≤ K := by dsimp [K]; linarith
  have hd : 0 < d := by dsimp [d,p,r]; omega
  refine ⟨K, d, hK, hd, ?_⟩
  intro n N ell T ε hn hN he he1 hsize htime
  let X := ε⁻¹ * logTwo n
  obtain ⟨hX, hEX, hLX, hNX⟩ := blowup_log n N ε hn hN he he1 hsize
  change 1 ≤ X at hX
  change ε⁻¹ ≤ X at hEX
  change logTwo n ≤ X at hLX
  change logTwo N ≤ 5 * X at hNX
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hNX0 : 0 ≤ logTwo N := div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) (Real.log_nonneg (by norm_num))
  have hlog2 := log_two_bounds
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hXpow : X ≤ X ^ d := le_self_pow₀ hX (Nat.ne_of_gt hd)
  have hhalf : (ε / 2)⁻¹ ≤ 2 * X := by
    have hi : (ε / 2)⁻¹ = 2 * ε⁻¹ := by field_simp
    rw [hi]
    linarith
  have hcore : (ε / 2)⁻¹ ^ p * logTwo N ^ r ≤ (2 : ℝ) ^ p * (5 : ℝ) ^ r * X ^ d := by
    calc
      _ ≤ (2 * X) ^ p * (5 * X) ^ r :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hhalf p) (pow_le_pow_left₀ hNX0 hNX r)
          (pow_nonneg hNX0 _) (by positivity)
      _ = _ := by dsimp [d]; rw [mul_pow, mul_pow, pow_add]; ring
  have hExp : (2 : ℝ) ^ (D * (ε / 2)⁻¹ ^ p * logTwo N ^ r) ≤ Real.exp (K * X ^ d) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hc0 : 0 ≤ (ε / 2)⁻¹ ^ p * logTwo N ^ r := mul_nonneg (by positivity) (pow_nonneg hNX0 _)
    have hc1 := mul_le_mul_of_nonneg_left hcore hD.le
    have hc2 := mul_le_mul_of_nonneg_right hlog2.2 (mul_nonneg hD.le hc0)
    have hc3 := mul_le_mul_of_nonneg_right hBK (pow_nonneg hX0 d)
    dsimp [B] at hc3
    nlinarith
  have hNExp : (N : ℝ) ≤ Real.exp (K * X ^ d) := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogeq : Real.log N = logTwo N * Real.log 2 := by unfold logTwo; field_simp
    have hlogN : Real.log N ≤ 5 * X := by
      rw [hlogeq]
      nlinarith [mul_le_mul_of_nonneg_right hlog2.2 hNX0]
    rw [← Real.exp_log hNR]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right h5K (pow_nonneg hX0 d)]
  have hpoly : D * (ell + 3 : ℝ) ^ q ≤ C * (ell + 1 : ℝ) ^ q := by
    calc
      _ ≤ D * (3 * (ell + 1 : ℝ)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by have hh := Nat.cast_nonneg (α := ℝ) ell; linarith) q) hD.le
      _ = _ := by dsimp [C]; rw [mul_pow]; ring
  change (T : ℝ) ≤ D * (ell + 3 : ℝ) ^ q + D * (2 : ℝ) ^ (D * (ε / 2)⁻¹ ^ p * logTwo N ^ r) at htime
  have hE0 : 0 ≤ Real.exp (K * X ^ d) := (Real.exp_pos _).le
  have hP0 : (0 : ℝ) ≤ (ell + 1 : ℝ) ^ q := by positivity
  have hh1 := mul_le_mul_of_nonneg_left hExp hD.le
  have hh2 := mul_le_mul_of_nonneg_right hDK hE0
  have hh3 := mul_le_mul_of_nonneg_right hCK hP0
  nlinarith

end EdgeSublinearMWIS.Main.WeightedRuntime
end

section

open scoped BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.SimulationEnvelope

 theorem polynomial_simulation (q r d : ℕ) (K k : ℝ) (hK : 0 < K) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (ell t i s : ℕ), 0 ≤ x →
      (t : ℝ) ≤ K * Real.exp (K * x ^ d) + K * (ell + 1 : ℝ) ^ q →
      i + 1 ≤ 3 * (ell + 1) ^ 2 →
      (s : ℝ) ≤ k * (t + i + 1 : ℝ) ^ r →
      (s : ℝ) ≤ C * Real.exp (C * x ^ d) + C * (ell + 1 : ℝ) ^ (max q 2 * r) := by
  let A := K + 4
  let D := k * A ^ r * (2 : ℝ) ^ (r - 1)
  let C := D + (r : ℝ) * K + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    dsimp [C]
    have hh := mul_nonneg (Nat.cast_nonneg r) hK.le
    linarith
  have hrK : (r : ℝ) * K ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro x ell t i s hx ht hi hs
  let L : ℝ := ell + 1
  let E := Real.exp (K * x ^ d)
  have hL : 1 ≤ L := by dsimp [L]; have hh := Nat.cast_nonneg (α := ℝ) ell; linarith
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hK.le (pow_nonneg hx _))
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  have hpow : L ^ q ≤ L ^ max q 2 := pow_le_pow_right₀ hL (le_max_left _ _)
  have hpow2 : L ^ 2 ≤ L ^ max q 2 := pow_le_pow_right₀ hL (le_max_right _ _)
  have hiR : (i : ℝ) + 1 ≤ 3 * L ^ 2 := by dsimp [L]; exact_mod_cast hi
  have hsum : (t + i + 1 : ℝ) ≤ A * (E + L ^ max q 2) := by
    change (t : ℝ) ≤ K * E + K * L ^ q at ht
    dsimp [A]
    have hP : (0 : ℝ) ≤ L ^ max q 2 := pow_nonneg hL0 _
    nlinarith [mul_le_mul_of_nonneg_left hpow hK.le]
  have hpowSum : (t + i + 1 : ℝ) ^ r ≤ (A * (E + L ^ max q 2)) ^ r :=
    pow_le_pow_left₀ (by positivity) hsum _
  have hadd := add_pow_le hE0 (pow_nonneg hL0 (max q 2)) r
  have hmain : (s : ℝ) ≤ D * (E ^ r + L ^ (max q 2 * r)) := by
    calc
      (s : ℝ) ≤ k * (A * (E + L ^ max q 2)) ^ r := hs.trans (mul_le_mul_of_nonneg_left hpowSum hk.le)
      _ = k * A ^ r * (E + L ^ max q 2) ^ r := by rw [mul_pow]; ring
      _ ≤ k * A ^ r * ((2 : ℝ) ^ (r - 1) * (E ^ r + (L ^ max q 2) ^ r)) :=
        mul_le_mul_of_nonneg_left hadd (by positivity)
      _ = D * (E ^ r + L ^ (max q 2 * r)) := by dsimp [D]; rw [pow_mul]; ring
  have hEr : E ^ r ≤ Real.exp (C * x ^ d) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hrK (pow_nonneg hx d)]
  calc
    (s : ℝ) ≤ D * (E ^ r + L ^ (max q 2 * r)) := hmain
    _ ≤ C * Real.exp (C * x ^ d) + C * L ^ (max q 2 * r) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul hDC hEr (pow_nonneg hE0 _) hC.le)
        (mul_le_mul_of_nonneg_right hDC (pow_nonneg hL0 _))
    _ = _ := rfl

end EdgeSublinearMWIS.Main.SimulationEnvelope
end

section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.WeightedHelpers
open EdgeSublinearMWIS.Main.WeightedExecutionMath EdgeSublinearMWIS.Main.UnweightedStack
open EdgeSublinearMWIS.Main.WeightedRuntime EdgeSublinearMWIS.Main.SimulationEnvelope
open EdgeSublinearMWIS.Main.EncodingBounds
set_option autoImplicit false

theorem solution :
    ∃ q : ℕ, 0 < q ∧ ∀ C : GraphClass, StronglyEdgeSublinear C →
      ∃ (P : Program) (K : ℝ) (d : ℕ), 0 < K ∧ 0 < d ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode)
          (ε : RationalCode), C n G → 0 < ε.value → ε.value < 1 →
          ∃ (I : Finset (Fin n)) (s : ℕ),
            Runs P (weightedInput G w ε) (mask I) s ∧
            G.IsIndepSet (I : Set (Fin n)) ∧
            (1 - (ε.value : ℝ)) * weightedAlpha G (fun v => (w v).value) ≤
              ∑ v ∈ I, ((w v).value : ℝ) ∧
            (s : ℝ) ≤ K * Real.exp
              (K * (((ε.value : ℝ))⁻¹ * logTwo (max 2 n)) ^ d) +
                K * ((rationalData w ε).length + 1 : ℝ) ^ q  := by
  obtain ⟨q, hq, hUnweighted⟩ := unweighted_scheme
  obtain ⟨r, hr, hWrapper⟩ := weighted_wrapper
  refine ⟨max q 2 * r, Nat.mul_pos (by omega) hr, ?_⟩
  intro C hC
  obtain ⟨a, K, ha, hbound⟩ := class_treewidth_bound C hC
  obtain ⟨hherbl, ⟨B, hB, htwbl⟩, hsepbl⟩ := lemma_16 C a K hC.1 ha hbound
  have ha2 : 2 ≤ 2 * a := by omega
  have hboundbl : TreewidthBound (BlowupClass C) (2 * a) B := by
    refine ⟨hB, ?_⟩
    intro n G hG
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using htwbl n G hG
  obtain ⟨U, D, hD, hU⟩ := hUnweighted (BlowupClass C) (2 * a) B hsepbl ha2 hboundbl
  obtain ⟨P, k, hk, hP⟩ := hWrapper U
  obtain ⟨K1, d, hK1, hd, hEnv⟩ := runtime_envelope q (2 * a) D ha2 hD
  obtain ⟨K2, hK2, hClose⟩ := polynomial_simulation q r d K1 k hK1 (by exact_mod_cast hk)
  refine ⟨P, K2, d, hK2, hd, ?_⟩
  intro n G w ε hG he he1
  let ell := (rationalData w ε).length
  let X := (ε.value : ℝ)⁻¹ * logTwo (max 2 n)
  have heR : (0 : ℝ) < ε.value := by exact_mod_cast he
  have he1R : (ε.value : ℝ) < 1 := by exact_mod_cast he1
  have hX : 0 ≤ X := by
    apply mul_nonneg (inv_nonneg.mpr heR.le)
    unfold logTwo
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ max 2 n by omega))
    · exact Real.log_nonneg (by norm_num)
  obtain ⟨hsmall, hzero, hnormal⟩ := hP n G w ε he he1
  have direct_time {s : ℕ} (hs : s ≤ k * ((weightedInput G w ε).length + 1) ^ r) :
      (s : ℝ) ≤ K2 * Real.exp (K2 * X ^ d) + K2 * (ell + 1 : ℝ) ^ (max q 2 * r) := by
    apply hClose X ell 0 (weightedInput G w ε).length s hX (by simp only [Nat.cast_zero]; positivity) (input_length G w ε)
    simpa only [Nat.cast_zero, zero_add] using (show (s : ℝ) ≤ (k : ℝ) * ((weightedInput G w ε).length + 1 : ℝ) ^ r by exact_mod_cast hs)
  by_cases hn : n ≤ 1
  · obtain ⟨s, hs, htime⟩ := hsmall hn
    obtain ⟨hind, hopt⟩ := direct_correct G w hn
    refine ⟨directVertices w, s, hs, hind, ?_, direct_time htime⟩
    have hnon := alpha_nonneg G (fun v => (w v).value)
    rw [← hopt]
    nlinarith
  · have hn2 : 2 ≤ n := by omega
    by_cases hmax : maximumWeight (clippedValues w) ≤ 0
    · obtain ⟨s, hs, htime⟩ := hzero hn2 hmax
      have hall (v : Fin n) : (w v).value ≤ 0 := by
        have h1 : (w v).value ≤ clippedValues w v := by
          simp only [clippedValues, clipped_value]
          exact le_max_left _ _
        exact h1.trans ((max_weight_le (clippedValues w) v).trans hmax)
      have hopt := nonpositive_alpha G (fun v => (w v).value) hall
      refine ⟨∅, s, hs, by simp, ?_, direct_time htime⟩
      simp [hopt]
    · have hmaxpos : 0 < maximumWeight (clippedValues w) := lt_of_not_ge hmax
      obtain ⟨τ, t, hrounding, hτ, hscale, htfloor, htotal, hround, hproject⟩ :=
        weight_rounding G (clippedValues w) ε.value hn2 (clipped_nonneg w) hmaxpos he he1
      have hN : 2 ≤ totalCopies t := rounding_large (clippedValues w) ε.value τ t hn2 hmaxpos he he1 hτ hscale htfloor
      have hclass : BlowupClass C (totalCopies t) (roundedGraph G t) := rounded_mem_blowup C G hC.1 hG t
      have hehalf : 0 < (halfAccuracy ε).value := by rw [half_value]; linarith
      have hehalf1 : (halfAccuracy ε).value < 1 := by rw [half_value]; linarith
      obtain ⟨J, u, T, hRun, hInd, hAcc, hTime⟩ := hU (totalCopies t) (roundedGraph G t) (halfAccuracy ε) hN hclass hehalf hehalf1
      obtain ⟨s, hs, hsteps⟩ := hnormal τ t hn2 hrounding J u T hRun
      obtain ⟨hind, hweight⟩ := hproject J hInd
      refine ⟨originalVertices t J, s, hs, hind, ?_, ?_⟩
      · have hhalfR : ((halfAccuracy ε).value : ℝ) = (ε.value : ℝ) / 2 := by rw [half_value]; push_cast; rfl
        rw [hhalfR] at hAcc
        have hα := clipped_alpha G w
        have hα0 := alpha_nonneg G (clippedValues w)
        have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
        have hc : (0 : ℝ) ≤ 1 - (ε.value : ℝ) / 2 := by linarith
        have hcoef : (1 - (ε.value : ℝ)) ≤ (1 - (ε.value : ℝ) / 2) * (1 - (ε.value : ℝ) / 2) := by nlinarith [sq_nonneg (ε.value : ℝ)]
        rw [projection_original_weights w τ t htfloor J] at hweight
        calc
          (1 - (ε.value : ℝ)) * weightedAlpha G (fun v => (w v).value)
              ≤ (1 - (ε.value : ℝ) / 2) * (1 - (ε.value : ℝ) / 2) * weightedAlpha G (clippedValues w) := by rw [← hα]; exact mul_le_mul_of_nonneg_right hcoef hα0
          _ ≤ (1 - (ε.value : ℝ) / 2) * ((τ : ℝ) * alpha (roundedGraph G t) Finset.univ) := by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hround hc
          _ = (τ : ℝ) * ((1 - (ε.value : ℝ) / 2) * alpha (roundedGraph G t) Finset.univ) := by ring
          _ ≤ (τ : ℝ) * J.card := mul_le_mul_of_nonneg_left hAcc hτR.le
          _ ≤ ∑ v ∈ originalVertices t J, ((w v).value : ℝ) := hweight
      · have hhalfR : ((halfAccuracy ε).value : ℝ) = (ε.value : ℝ) / 2 := by rw [half_value]; push_cast; rfl
        have hEL : (halfAccuracy ε).bits.length + 1 ≤ ell + 3 := by
          have heL : ε.bits.length ≤ ell := by dsimp [ell]; simp only [rationalData, List.length_append]; omega
          rw [half_bits]
          omega
        have hpoly : D * ((halfAccuracy ε).bits.length + 1 : ℝ) ^ q ≤ D * (ell + 3 : ℝ) ^ q :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hEL) q) hD.le
        rw [hhalfR] at hTime
        have hTime' := hTime.trans (add_le_add hpoly le_rfl)
        have hsize : (totalCopies t : ℝ) ≤ 2 * (n : ℝ) ^ 2 / (ε.value : ℝ) := by exact_mod_cast htotal
        have hcombined := hEnv n (totalCopies t) ell T (ε.value : ℝ) hn2 hN heR he1R hsize hTime'
        have hcombined' : (T + totalCopies t : ℝ) ≤ K1 * Real.exp (K1 * X ^ d) + K1 * (ell + 1 : ℝ) ^ q := by
          have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
          simpa only [X, max_eq_right hn2R] using hcombined
        apply hClose X ell (T + totalCopies t) (weightedInput G w ε).length s hX (by exact_mod_cast hcombined') (input_length G w ε)
        exact_mod_cast (show s ≤ k * ((T + totalCopies t) + (weightedInput G w ε).length + 1) ^ r by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsteps)
end
