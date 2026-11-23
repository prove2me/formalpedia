-- Prove2me | solution 1 for ChenCapacityTerminals.Exact.exists_lawfulExactOracle
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T07:48:58.279801+00:00
-- url     : https://prove2.me/submissions/bc470526-1578-4959-b469-40a4541d1d61

import Theorems.Thm_FlowsNetworks_MaxFlow_max_flow_min_cut
import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false
open scoped BigOperators
open ChenCapacityTerminals.Exact
namespace ChenCapacityTerminals.Exact

private lemma list_sum_get {α : Type} [AddCommMonoid α] (l : List Arc) (q : Arc → α) :
    (l.map q).sum = ∑ i : Fin l.length, q (l.get i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.get_eq_getElem, List.length_cons]
      rw [Fin.sum_univ_succ, ih, add_comm]
      simp
      exact add_comm _ _

private lemma weight_eq_sum (G : Network) (A C : Finset ℕ) :
    weight G A C = ∑ i : Fin G.arcs.length,
      if (G.arcs.get i).tail ∈ A ∧ (G.arcs.get i).head ∈ C then (G.arcs.get i).capacity else 0 := by
  exact list_sum_get G.arcs _

private lemma weight_nonneg (G : Network) (hG : G.Valid) (A C : Finset ℕ) : 0 ≤ weight G A C := by
  rw [weight_eq_sum]
  apply Finset.sum_nonneg
  intro i hi
  by_cases h : (G.arcs.get i).tail ∈ A ∧ (G.arcs.get i).head ∈ C
  · simp only [List.get_eq_getElem] at h ⊢
    rw [if_pos h]
    exact (hG _ (List.get_mem _ _)).2.2
  · simp only [List.get_eq_getElem] at h ⊢
    rw [if_neg h]

private lemma arc_capacity_le_weight (G : Network) (hG : G.Valid) (e : Arc)
    (he : e ∈ G.arcs) : e.capacity ≤ weight G {e.tail} {e.head} := by
  unfold weight
  have hnonneg : ∀ x ∈ G.arcs.map (fun a =>
      if a.tail ∈ ({e.tail} : Finset ℕ) ∧ a.head ∈ ({e.head} : Finset ℕ) then a.capacity else 0), 0 ≤ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    by_cases h : a.tail ∈ ({e.tail} : Finset ℕ) ∧ a.head ∈ ({e.head} : Finset ℕ)
    · simp only [if_pos h]
      exact (hG _ ha).2.2
    · simp only [Finset.mem_singleton] at h ⊢
      rw [if_neg h]
  have hmem : (if e.tail ∈ ({e.tail} : Finset ℕ) ∧ e.head ∈ ({e.head} : Finset ℕ)
      then e.capacity else 0) ∈ G.arcs.map (fun a =>
      if a.tail ∈ ({e.tail} : Finset ℕ) ∧ a.head ∈ ({e.head} : Finset ℕ) then a.capacity else 0) :=
    List.mem_map_of_mem he
  simpa using List.single_le_sum hnonneg _ hmem

private lemma pair_capacity_sum (G : Network) (u v : ℕ) :
    (∑ i : Fin G.arcs.length, if (G.arcs.get i).tail = u ∧ (G.arcs.get i).head = v then
      (G.arcs.get i).capacity else 0) = weight G {u} {v} := by
  rw [weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : (G.arcs.get i).tail = u ∧ (G.arcs.get i).head = v
  · simp only [List.get_eq_getElem] at h ⊢
    simp [h]
  · simp only [List.get_eq_getElem] at h ⊢
    simp [h]

private abbrev Vertex (G : Network) := {v // v ∈ G.vertices}

private noncomputable def simpleNetwork (G : Network) (hG : G.Valid) : FlowsNetworks.MaxFlow.Network (Vertex G) where
  arcs := Finset.univ.filter (fun p : Vertex G × Vertex G => p.1 ≠ p.2)
  loopless := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  cap u v := weight G {u.1} {v.1}
  cap_nonneg := by
    intro p hp
    exact weight_nonneg G hG _ _

private lemma mem_simple_arcs (G : Network) (hG : G.Valid) (u v : Vertex G) :
    (u, v) ∈ (simpleNetwork G hG).arcs ↔ u ≠ v := by simp [simpleNetwork]

private lemma simple_arc_sum (G : Network) (hG : G.Valid)
    (P : Vertex G × Vertex G → Prop) [DecidablePred P] (g : Vertex G → Vertex G → ℝ) :
    (∑ p ∈ (simpleNetwork G hG).arcs.filter P, g p.1 p.2) =
      ∑ u : Vertex G, ∑ v : Vertex G, if u ≠ v ∧ P (u, v) then g u v else 0 := by
  classical
  simp only [simpleNetwork, Finset.filter_filter, Finset.sum_filter]
  rw [show (Finset.univ : Finset (Vertex G × Vertex G)) = Finset.univ ×ˢ Finset.univ by ext <;> simp]
  rw [Finset.sum_product]

private noncomputable def splitFlow (G : Network) (hG : G.Valid)
    (f : Vertex G → Vertex G → ℝ) (i : Fin G.arcs.length) : ℝ :=
  let e := G.arcs.get i
  if e.tail = e.head then 0 else
    e.capacity / weight G {e.tail} {e.head} *
      f ⟨e.tail, (hG e (List.get_mem _ _)).1⟩ ⟨e.head, (hG e (List.get_mem _ _)).2.1⟩

private lemma splitFlow_nonneg (G : Network) (hG : G.Valid) (f : Vertex G → Vertex G → ℝ)
    (hf : ∀ p ∈ (simpleNetwork G hG).arcs, 0 ≤ f p.1 p.2) (i : Fin G.arcs.length) :
    0 ≤ splitFlow G hG f i := by
  classical
  unfold splitFlow
  dsimp only
  by_cases hloop : (G.arcs.get i).tail = (G.arcs.get i).head
  · simp only [List.get_eq_getElem] at hloop ⊢
    rw [if_pos hloop]
  · simp only [List.get_eq_getElem] at hloop ⊢
    rw [if_neg hloop]
    apply mul_nonneg
    · apply div_nonneg (hG _ (List.get_mem _ _)).2.2
      exact weight_nonneg G hG _ _
    · exact hf _ ((mem_simple_arcs G hG _ _).2 (by
        intro h
        exact hloop (congrArg Subtype.val h)))

private lemma splitFlow_le_capacity (G : Network) (hG : G.Valid) (f : Vertex G → Vertex G → ℝ)
    (hfc : ∀ p ∈ (simpleNetwork G hG).arcs, f p.1 p.2 ≤ (simpleNetwork G hG).cap p.1 p.2)
    (i : Fin G.arcs.length) : splitFlow G hG f i ≤ (G.arcs.get i).capacity := by
  classical
  unfold splitFlow
  dsimp only
  by_cases hloop : (G.arcs.get i).tail = (G.arcs.get i).head
  · simp only [List.get_eq_getElem] at hloop ⊢
    rw [if_pos hloop]
    exact (hG _ (List.get_mem _ _)).2.2
  · simp only [List.get_eq_getElem] at hloop ⊢
    rw [if_neg hloop]
    let e := G.arcs.get i
    let u : Vertex G := ⟨e.tail, (hG e (List.get_mem _ _)).1⟩
    let v : Vertex G := ⟨e.head, (hG e (List.get_mem _ _)).2.1⟩
    have huv : (u, v) ∈ (simpleNetwork G hG).arcs := by
      rw [mem_simple_arcs]
      intro h
      exact hloop (congrArg Subtype.val h)
    have hfuCap := hfc (u, v) huv
    have he0 := (hG e (List.get_mem _ _)).2.2
    have hew := arc_capacity_le_weight G hG e (List.get_mem _ _)
    have hw0 := weight_nonneg G hG {e.tail} {e.head}
    by_cases hw : weight G {e.tail} {e.head} = 0
    · have hezero : e.capacity = 0 := le_antisymm (by simpa [hw] using hew) he0
      change e.capacity / weight G {e.tail} {e.head} * f u v ≤ e.capacity
      rw [hezero]
      simp
    · change e.capacity / weight G {e.tail} {e.head} * f u v ≤ e.capacity
      have hfuCap' : f u v ≤ weight G {e.tail} {e.head} := by simpa [simpleNetwork, u, v] using hfuCap
      calc
        e.capacity / weight G {e.tail} {e.head} * f u v ≤
            e.capacity / weight G {e.tail} {e.head} * weight G {e.tail} {e.head} :=
          mul_le_mul_of_nonneg_left hfuCap' (div_nonneg he0 hw0)
        _ = e.capacity := div_mul_cancel₀ _ hw

private lemma pair_splitFlow_sum (G : Network) (hG : G.Valid) (f : Vertex G → Vertex G → ℝ)
    (hsupp : FlowsNetworks.MaxFlow.SupportedOnArcs (simpleNetwork G hG) f)
    (hf0 : ∀ p ∈ (simpleNetwork G hG).arcs, 0 ≤ f p.1 p.2)
    (hfc : ∀ p ∈ (simpleNetwork G hG).arcs, f p.1 p.2 ≤ (simpleNetwork G hG).cap p.1 p.2)
    (u v : Vertex G) :
    (∑ i : Fin G.arcs.length, if (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1 then
      splitFlow G hG f i else 0) = f u v := by
  classical
  by_cases huv : u = v
  · subst v
    have hfu : f u u = 0 := by apply hsupp; simp [mem_simple_arcs]
    calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        by_cases h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = u.1
        · simp only [List.get_eq_getElem] at h ⊢
          rw [if_pos h]
          unfold splitFlow
          dsimp only
          simp only [List.get_eq_getElem]
          rw [if_pos (h.1.trans h.2.symm)]
        · simp only [List.get_eq_getElem] at h ⊢
          rw [if_neg h]
      _ = f u u := hfu.symm
  · have hmem : (u, v) ∈ (simpleNetwork G hG).arcs := (mem_simple_arcs G hG u v).2 huv
    by_cases hw : weight G {u.1} {v.1} = 0
    · have hfu : f u v = 0 := by
        have hlo := hf0 (u, v) hmem
        have hhi := hfc (u, v) hmem
        change f u v ≤ weight G {u.1} {v.1} at hhi
        linarith
      calc
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          by_cases h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1
          · simp only [List.get_eq_getElem] at h ⊢
            rw [if_pos h]
            have he : G.arcs[i.1] ∈ G.arcs := List.getElem_mem i.isLt
            have hew := arc_capacity_le_weight G hG _ he
            have he0 := (hG _ he).2.2
            have heq : G.arcs[i.1].capacity = 0 := by
              apply le_antisymm _ he0
              simpa [h.1, h.2, hw] using hew
            have hne : G.arcs[i.1].tail ≠ G.arcs[i.1].head := by
              rw [h.1, h.2]
              exact fun h => huv (Subtype.ext h)
            unfold splitFlow
            dsimp only
            simp only [List.get_eq_getElem]
            rw [if_neg hne, heq]
            simp
          · simp only [List.get_eq_getElem] at h ⊢
            rw [if_neg h]
        _ = f u v := hfu.symm
    · calc
        _ = ∑ i : Fin G.arcs.length,
              (if (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1 then
                (G.arcs.get i).capacity else 0) / weight G {u.1} {v.1} * f u v := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1
          · simp only [List.get_eq_getElem] at h ⊢
            rw [if_pos h]
            have hne : G.arcs[i.1].tail ≠ G.arcs[i.1].head := by
              rw [h.1, h.2]
              exact fun h => huv (Subtype.ext h)
            unfold splitFlow
            dsimp only
            simp only [List.get_eq_getElem]
            rw [if_neg hne]
            simp [h.1, h.2]
          · simp only [List.get_eq_getElem] at h ⊢
            simp [h]
        _ = (∑ i : Fin G.arcs.length,
              (if (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1 then
                (G.arcs.get i).capacity else 0) / weight G {u.1} {v.1}) * f u v :=
          (Finset.sum_mul Finset.univ _ _).symm
        _ = ((∑ i : Fin G.arcs.length, if (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1 then
                (G.arcs.get i).capacity else 0) / weight G {u.1} {v.1}) * f u v := by
          rw [Finset.sum_div]
        _ = f u v := by rw [pair_capacity_sum, div_self hw, one_mul]

private lemma cutCapacity_eq (G : Network) (hG : G.Valid) (C : Finset (Vertex G)) :
    FlowsNetworks.MaxFlow.cutCapacity (simpleNetwork G hG) C =
      ∑ u ∈ C, ∑ v ∈ Cᶜ, weight G {u.1} {v.1} := by
  classical
  unfold FlowsNetworks.MaxFlow.cutCapacity FlowsNetworks.MaxFlow.arcSum FlowsNetworks.MaxFlow.arcsBetween
  rw [simple_arc_sum]
  simp only [Prod.fst, Prod.snd, Finset.mem_compl]
  calc
    _ = ∑ u : Vertex G, if u ∈ C then (∑ v ∈ Cᶜ, weight G {u.1} {v.1}) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases huC : u ∈ C
      · rw [if_pos huC]
        calc
          _ = ∑ v ∈ Cᶜ, if u ≠ v ∧ u ∈ C ∧ v ∉ C then (simpleNetwork G hG).cap u v else 0 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro v hv hvcomp
            have hvC : v ∈ C := by simpa using hvcomp
            simp [hvC]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro v hv
            have hvC : v ∉ C := by simpa using hv
            have huv : u ≠ v := by intro h; subst v; exact hvC huC
            simp [huC, hvC, huv, simpleNetwork]
      · simp [huC]
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

private noncomputable def arcPair (G : Network) (hG : G.Valid) (i : Fin G.arcs.length) : Vertex G × Vertex G :=
  (⟨(G.arcs.get i).tail, (hG _ (List.get_mem _ _)).1⟩,
   ⟨(G.arcs.get i).head, (hG _ (List.get_mem _ _)).2.1⟩)
private noncomputable def pairRawSum (G : Network) (q : Fin G.arcs.length → ℝ) (u v : Vertex G) : ℝ :=
  ∑ i : Fin G.arcs.length, if (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1 then q i else 0
private lemma arcPair_eq (G : Network) (hG : G.Valid) (i : Fin G.arcs.length) (u v : Vertex G)
    (h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1) : arcPair G hG i = (u, v) := by
  simp only [List.get_eq_getElem] at h ⊢
  simp [arcPair, h]

private lemma raw_sum_partition (G : Network) (hG : G.Valid) (q : Fin G.arcs.length → ℝ) :
    (∑ i : Fin G.arcs.length, q i) = ∑ u : Vertex G, ∑ v : Vertex G, pairRawSum G q u v := by
  classical
  symm
  calc
    _ = ∑ p : Vertex G × Vertex G, ∑ i : Fin G.arcs.length, if arcPair G hG i = p then q i else 0 := by
      rw [show (Finset.univ : Finset (Vertex G × Vertex G)) = Finset.univ ×ˢ Finset.univ by ext <;> simp]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl; intro u hu
      apply Finset.sum_congr rfl; intro v hv
      unfold pairRawSum
      apply Finset.sum_congr rfl; intro i hi
      by_cases h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1
      · have hp := arcPair_eq G hG i u v h
        simp only [List.get_eq_getElem] at h ⊢
        simp [h, hp]
      · have hp : arcPair G hG i ≠ (u, v) := by
          intro hp
          apply h
          constructor
          · have he := congrArg (fun p : Vertex G × Vertex G => p.1.1) hp
            simpa [arcPair] using he
          · have he := congrArg (fun p : Vertex G × Vertex G => p.2.1) hp
            simpa [arcPair] using he
        simp only [List.get_eq_getElem] at h ⊢
        simp [h, hp]
    _ = ∑ p : Vertex G × Vertex G,
          ∑ i ∈ Finset.univ.filter (fun i : Fin G.arcs.length => arcPair G hG i = p), q i := by
      apply Finset.sum_congr rfl; intro p hp
      rw [Finset.sum_filter]
    _ = _ := Finset.sum_fiberwise Finset.univ (arcPair G hG) q

private lemma sum_pair_restrict (G : Network) (A B : Finset (Vertex G)) (g : Vertex G → Vertex G → ℝ) :
    (∑ u : Vertex G, ∑ v : Vertex G, if u ∈ A ∧ v ∈ B then g u v else 0) = ∑ u ∈ A, ∑ v ∈ B, g u v := by
  classical
  calc
    _ = ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Vertex G × Vertex G => p.1 ∈ A ∧ p.2 ∈ B), g p.1 p.2 := by
      rw [Finset.sum_filter, Finset.sum_product]
    _ = ∑ p ∈ A ×ˢ B, g p.1 p.2 := by congr 1; ext p; simp
    _ = _ := Finset.sum_product ..

private lemma raw_sum_restrict (G : Network) (hG : G.Valid) (A B : Finset (Vertex G))
    (q : Fin G.arcs.length → ℝ) :
    (∑ i : Fin G.arcs.length, if (arcPair G hG i).1 ∈ A ∧ (arcPair G hG i).2 ∈ B then q i else 0) =
      ∑ u ∈ A, ∑ v ∈ B, pairRawSum G q u v := by
  classical
  rw [raw_sum_partition G hG]
  calc
    _ = ∑ u : Vertex G, ∑ v : Vertex G, if u ∈ A ∧ v ∈ B then pairRawSum G q u v else 0 := by
      apply Finset.sum_congr rfl; intro u hu
      apply Finset.sum_congr rfl; intro v hv
      by_cases huv : u ∈ A ∧ v ∈ B
      · simp only [if_pos huv]
        unfold pairRawSum
        apply Finset.sum_congr rfl; intro i hi
        by_cases h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1
        · have hp := arcPair_eq G hG i u v h
          simp only [List.get_eq_getElem] at h ⊢
          simp [h, hp, huv]
        · simp only [List.get_eq_getElem] at h ⊢
          simp [h]
      · simp only [if_neg huv]
        apply Finset.sum_eq_zero
        intro i hi
        by_cases h : (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = v.1
        · have hp := arcPair_eq G hG i u v h
          simp only [List.get_eq_getElem] at h ⊢
          simp [h, hp, huv]
        · simp only [List.get_eq_getElem] at h ⊢
          simp [h]
    _ = _ := sum_pair_restrict G A B _

private lemma pairRaw_out (G : Network) (hG : G.Valid) (f : Vertex G → Vertex G → ℝ)
    (hsupp : FlowsNetworks.MaxFlow.SupportedOnArcs (simpleNetwork G hG) f)
    (hf0 : ∀ p ∈ (simpleNetwork G hG).arcs, 0 ≤ f p.1 p.2)
    (hfc : ∀ p ∈ (simpleNetwork G hG).arcs, f p.1 p.2 ≤ (simpleNetwork G hG).cap p.1 p.2)
    (x u v : Vertex G) :
    pairRawSum G (fun i => if (G.arcs.get i).tail = x.1 then splitFlow G hG f i else 0) u v =
      if u = x then f u v else 0 := by
  classical
  by_cases hu : u = x
  · subst u
    unfold pairRawSum
    calc
      _ = ∑ i : Fin G.arcs.length, if (G.arcs.get i).tail = x.1 ∧ (G.arcs.get i).head = v.1 then
          splitFlow G hG f i else 0 := by
        apply Finset.sum_congr rfl; intro i hi
        by_cases ht : (G.arcs.get i).tail = x.1
        <;> simp only [List.get_eq_getElem] at ht ⊢ <;> simp [ht]
      _ = f x v := pair_splitFlow_sum G hG f hsupp hf0 hfc x v
      _ = if x = x then f x v else 0 := by simp
  · have hux : u.1 ≠ x.1 := fun h => hu (Subtype.ext h)
    rw [if_neg hu]
    unfold pairRawSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [List.get_eq_getElem]
    split_ifs with h1 h2
    · exact (hux (h1.1.symm.trans h2)).elim
    all_goals rfl

private lemma pairRaw_in (G : Network) (hG : G.Valid) (f : Vertex G → Vertex G → ℝ)
    (hsupp : FlowsNetworks.MaxFlow.SupportedOnArcs (simpleNetwork G hG) f)
    (hf0 : ∀ p ∈ (simpleNetwork G hG).arcs, 0 ≤ f p.1 p.2)
    (hfc : ∀ p ∈ (simpleNetwork G hG).arcs, f p.1 p.2 ≤ (simpleNetwork G hG).cap p.1 p.2)
    (x u v : Vertex G) :
    pairRawSum G (fun i => if (G.arcs.get i).head = x.1 then splitFlow G hG f i else 0) u v =
      if v = x then f u v else 0 := by
  classical
  by_cases hv : v = x
  · subst v
    unfold pairRawSum
    calc
      _ = ∑ i : Fin G.arcs.length, if (G.arcs.get i).tail = u.1 ∧ (G.arcs.get i).head = x.1 then
          splitFlow G hG f i else 0 := by
        apply Finset.sum_congr rfl; intro i hi
        by_cases ht : (G.arcs.get i).head = x.1
        <;> simp only [List.get_eq_getElem] at ht ⊢ <;> simp [ht]
      _ = f u x := pair_splitFlow_sum G hG f hsupp hf0 hfc u x
      _ = if x = x then f u x else 0 := by simp
  · have hvx : v.1 ≠ x.1 := fun h => hv (Subtype.ext h)
    rw [if_neg hv]
    unfold pairRawSum
    apply Finset.sum_eq_zero
    intro i hi
    simp only [List.get_eq_getElem]
    split_ifs with h1 h2
    · exact (hvx (h1.2.symm.trans h2)).elim
    all_goals rfl

private lemma divergence_eq_net (G : Network) (hG : G.Valid) (f : Vertex G → Vertex G → ℝ)
    (flow : ℕ → ℝ) (hflow : ∀ i : Fin G.arcs.length, flow i = splitFlow G hG f i)
    (hsupp : FlowsNetworks.MaxFlow.SupportedOnArcs (simpleNetwork G hG) f)
    (hf0 : ∀ p ∈ (simpleNetwork G hG).arcs, 0 ≤ f p.1 p.2)
    (hfc : ∀ p ∈ (simpleNetwork G hG).arcs, f p.1 p.2 ≤ (simpleNetwork G hG).cap p.1 p.2)
    (x : Vertex G) : divergence G flow x.1 = FlowsNetworks.MaxFlow.netFlowOut (simpleNetwork G hG) f x := by
  classical
  have hdiag : f x x = 0 := by apply hsupp; simp [mem_simple_arcs]
  unfold divergence Network.incidence
  simp_rw [hflow]
  rw [Finset.sum_sub_distrib, raw_sum_partition G hG, raw_sum_partition G hG]
  simp_rw [pairRaw_out G hG f hsupp hf0 hfc, pairRaw_in G hG f hsupp hf0 hfc]
  unfold FlowsNetworks.MaxFlow.netFlowOut
  rw [simple_arc_sum, simple_arc_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    by_cases huv : u = v
    · subst v
      by_cases hux : u = x
      · subst u; simp [hdiag]
      · simp [hux]
    · simp [huv]
  · apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    by_cases huv : u = v
    · subst v
      by_cases hux : u = x
      · subst u; simp [hdiag]
      · simp [hux]
    · simp [huv]

private lemma mem_image_val {G : Network} (C : Finset (Vertex G)) (v : Vertex G) : v.1 ∈ C.image Subtype.val ↔ v ∈ C := by
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    have h : u = v := Subtype.ext huv
    simpa [h] using hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

private lemma cut_outside (G : Network) (hG : G.Valid) (C : Finset (Vertex G)) :
    cut G (G.vertices \ C.image Subtype.val) = FlowsNetworks.MaxFlow.cutCapacity (simpleNetwork G hG) C := by
  classical
  have hsub : C.image Subtype.val ⊆ G.vertices := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact u.property
  have hsource : G.vertices \ (G.vertices \ C.image Subtype.val) = C.image Subtype.val := by
    ext v
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hv, hn⟩
      by_contra hvC
      exact hn ⟨hv, hvC⟩
    · intro hv
      exact ⟨hsub hv, by simp [hsub hv, hv]⟩
  rw [cut, hsource, weight_eq_sum]
  calc
    _ = ∑ i : Fin G.arcs.length, if (arcPair G hG i).1 ∈ C ∧ (arcPair G hG i).2 ∈ Cᶜ then
          (G.arcs.get i).capacity else 0 := by
      apply Finset.sum_congr rfl; intro i hi
      have he := hG _ (List.get_mem G.arcs i)
      change (if (arcPair G hG i).1.1 ∈ C.image Subtype.val ∧
        (arcPair G hG i).2.1 ∈ G.vertices \ C.image Subtype.val then (G.arcs.get i).capacity else 0) = _
      simp only [mem_image_val]
      simp only [List.get_eq_getElem] at he ⊢
      simp [Finset.mem_sdiff, he.2.1]
    _ = ∑ u ∈ C, ∑ v ∈ Cᶜ, pairRawSum G (fun i => (G.arcs.get i).capacity) u v := raw_sum_restrict G hG C Cᶜ _
    _ = ∑ u ∈ C, ∑ v ∈ Cᶜ, weight G {u.1} {v.1} := by
      apply Finset.sum_congr rfl; intro u hu
      apply Finset.sum_congr rfl; intro v hv
      exact pair_capacity_sum G u.1 v.1
    _ = _ := (cutCapacity_eq G hG C).symm

private lemma ofFn_getD {n : ℕ} (g : Fin n → ℝ) (i : ℕ) (hi : i < n) : (List.ofFn g).getD i 0 = g ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

lemma exists_exact_answer (Q : ExactQuery) (hQ : Q.Valid) : ∃ A : ExactAnswer, A.Correct Q := by
  classical
  rcases hQ with ⟨hG, hs, ht, hst⟩
  let r : Vertex Q.graph := ⟨Q.source, hs⟩
  let z : Vertex Q.graph := ⟨Q.sink, ht⟩
  have hrz : r ≠ z := fun h => hst (congrArg Subtype.val h)
  obtain ⟨val, ⟨⟨f, hf⟩, hmax⟩, ⟨⟨C, hrC, hzC, hval⟩, hmin⟩⟩ :=
    FlowsNetworks.MaxFlow.max_flow_min_cut (simpleNetwork Q.graph hG) r z hrz
  let flowList : List ℝ := List.ofFn (splitFlow Q.graph hG f)
  let X : Finset ℕ := Q.graph.vertices \ C.image Subtype.val
  have hget : ∀ i : Fin Q.graph.arcs.length, flowList.getD i 0 = splitFlow Q.graph hG f i := by
    intro i
    exact ofFn_getD _ _ i.isLt
  have hzX : Q.sink ∈ X := Finset.mem_sdiff.mpr ⟨ht, (mem_image_val C z).not.mpr hzC⟩
  have hrX : Q.source ∉ X := by
    intro h
    apply (Finset.mem_sdiff.mp h).2
    exact Finset.mem_image.mpr ⟨r, hrC, rfl⟩
  refine ⟨⟨flowList, X⟩, by simp [flowList], hG, hs, ht, hst,
    ⟨⟨Finset.sdiff_subset, ⟨Q.sink, hzX⟩, hrX⟩, hzX⟩, ?_, ?_, ?_⟩
  · intro i hi
    let j : Fin Q.graph.arcs.length := ⟨i, hi⟩
    have hj : flowList.getD i 0 = splitFlow Q.graph hG f j := hget j
    change 0 ≤ flowList.getD i 0 ∧ flowList.getD i 0 ≤ Q.graph.arcs[i]!.capacity
    rw [hj]
    exact ⟨splitFlow_nonneg Q.graph hG f hf.2.1 j, by
      simpa [j, List.getElem!_eq_getElem?_getD, hi] using splitFlow_le_capacity Q.graph hG f hf.2.2.1 j⟩
  · intro v hv hvr hvz
    let x : Vertex Q.graph := ⟨v, hv⟩
    have hxr : x ≠ r := fun h => hvr (congrArg Subtype.val h)
    have hxz : x ≠ z := fun h => hvz (congrArg Subtype.val h)
    change divergence Q.graph (fun i => flowList.getD i 0) x.1 = 0
    rw [divergence_eq_net Q.graph hG f _ hget hf.1 hf.2.1 hf.2.2.1 x]
    exact hf.2.2.2.2.2 x hxr hxz
  · change divergence Q.graph (fun i => flowList.getD i 0) r.1 = cut Q.graph X
    calc
      _ = FlowsNetworks.MaxFlow.netFlowOut (simpleNetwork Q.graph hG) f r :=
        divergence_eq_net Q.graph hG f _ hget hf.1 hf.2.1 hf.2.2.1 r
      _ = val := hf.2.2.2.1
      _ = FlowsNetworks.MaxFlow.cutCapacity (simpleNetwork Q.graph hG) C := hval
      _ = cut Q.graph X := (cut_outside Q.graph hG C).symm

end ChenCapacityTerminals.Exact

theorem solution : ∃ O, ChenCapacityTerminals.Exact.LawfulExactOracle O := by
  classical
  let O : ExactQuery → ExactAnswer := fun Q => if hQ : Q.Valid then
    Classical.choose (ChenCapacityTerminals.Exact.exists_exact_answer Q hQ) else ⟨[], ∅⟩
  refine ⟨O, ?_⟩
  intro Q hQ
  simpa [O, hQ] using Classical.choose_spec (ChenCapacityTerminals.Exact.exists_exact_answer Q hQ)
