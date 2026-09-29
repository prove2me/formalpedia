-- Prove2me | solution 1 for CubicP3Partition.c02_finite_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T20:53:35.007713+00:00
-- url     : https://prove2.me/submissions/1a3cb46d-36f5-418b-a0e1-cf900f2feb7e

import Definitions.Def_cubic_p3_partition_models
import Mathlib.Tactic

open CubicP3Partition

namespace CubicP3FiniteScratch

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : DecidableRel (H 0).Adj := fun u v => by
  change Decidable
    (u ≠ v ∧
      (forwardEdge 0 u.val v.val ∨ forwardEdge 0 v.val u.val))
  unfold forwardEdge brickEdges
  infer_instance

def p3PermutationFun : Fin 18 → Fin 18 :=
  ![0, 1, 2, 4, 7, 5, 3, 8, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17]

noncomputable def p3Permutation : Equiv.Perm (Fin 18) :=
  Equiv.ofBijective p3PermutationFun (by decide)

noncomputable def p3Place : (Fin 6 × Fin 3) ≃ Fin 18 :=
  finProdFinEquiv.trans p3Permutation

theorem h0_has_p3Factor : Nonempty (P3Factor (H 0)) := by
  refine ⟨{
    blockCount := 6
    place := p3Place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    fin_cases i <;>
      simp [p3Place, p3Permutation, p3PermutationFun] <;>
      decide
  · intro i
    fin_cases i <;>
      simp [p3Place, p3Permutation, p3PermutationFun] <;>
      decide

theorem h0_cubic : Cubic (H 0) := by
  intro v
  unfold degree
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  fin_cases v <;> decide

def connectivityCore : Fin 7 → Finset (Fin 18) :=
  ![{0, 5, 7, 8, 9, 10, 11, 12},
    {2, 4, 5, 7, 10, 11, 12, 13},
    {0, 3, 5, 6, 8, 9, 10, 11, 14},
    {1, 4, 6, 8, 13, 14, 15, 16},
    {0, 3, 4, 9, 12, 13, 14, 17},
    {0, 1, 3, 4, 6, 8, 9, 16, 17},
    {1, 2, 3, 7, 14, 15, 16, 17}]

lemma connectivityCore_connected (i : Fin 7) :
    ((H 0).induce {v : Fin 18 | v ∈ connectivityCore i}).Connected := by
  fin_cases i
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨0, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨2, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨0, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨1, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨0, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨0, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨1, by decide⟩, ?_⟩
    rintro ⟨v, hv⟩
    fin_cases v <;> simp [connectivityCore] at hv ⊢ <;> decide +revert

lemma connectivityCore_dominates (i : Fin 7) (v : Fin 18)
    (hv : v ∉ connectivityCore i) :
    ∃ w ∈ connectivityCore i, (H 0).Adj v w := by
  fin_cases i <;> fin_cases v <;> decide

lemma connectivityCore_avoids_pair (u v : Fin 18) :
    ∃ i : Fin 7, u ∉ connectivityCore i ∧ v ∉ connectivityCore i := by
  fin_cases u <;> fin_cases v <;> decide

lemma connected_induce_of_connected_dominating
    {V : Type*} {G : SimpleGraph V} {C T : Set V}
    (hC : (G.induce C).Connected)
    (hCT : C ⊆ T)
    (hDom : ∀ v ∈ T, v ∉ C → ∃ w ∈ C, G.Adj v w) :
    (G.induce T).Connected := by
  obtain ⟨root, hrootC⟩ := hC.nonempty
  apply G.induce_connected_of_patches root (hCT hrootC)
  intro v hvT
  by_cases hvC : v ∈ C
  · refine ⟨C, hCT, hrootC, hvC, hC ⟨root, hrootC⟩ ⟨v, hvC⟩⟩
  · obtain ⟨w, hwC, hvw⟩ := hDom v hvT hvC
    let U : Set V := C ∪ {v}
    have hsingleton : (G.induce ({v} : Set V)).Preconnected := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      simp only [Set.mem_singleton_iff] at hx hy
      subst x
      subst y
      exact SimpleGraph.Reachable.refl _
    have hU : (G.induce U).Connected := by
      apply G.connected_induce_union hC.preconnected hsingleton hwC
        (Set.mem_singleton v)
      exact hvw.symm
    refine ⟨U, ?_, Set.mem_union_left _ hrootC,
      Set.mem_union_right _ (Set.mem_singleton v), ?_⟩
    · intro x hx
      rcases hx with hxC | hxv
      · exact hCT hxC
      · simpa only [Set.mem_singleton_iff] using hxv ▸ hvT
    · exact hU
        ⟨root, Set.mem_union_left _ hrootC⟩
        ⟨v, Set.mem_union_right _ (Set.mem_singleton v)⟩

lemma finset_card_le_two_subset_pair
    {α : Type*} [DecidableEq α] [Nonempty α]
    (S : Finset α) (hS : S.card ≤ 2) :
    ∃ u v : α, S ⊆ {u, v} := by
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h | h | h
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp h
    let u : α := Classical.choice inferInstance
    exact ⟨u, u, by simp [hEmpty]⟩
  · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨u, u, by simp⟩
  · obtain ⟨u, v, -, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨u, v, Finset.Subset.rfl⟩

theorem h0_threeVertexConnected : ThreeVertexConnected (H 0) := by
  constructor
  · decide
  intro S hS
  obtain ⟨u, v, hSuv⟩ := finset_card_le_two_subset_pair S hS
  obtain ⟨i, hui, hvi⟩ := connectivityCore_avoids_pair u v
  apply connected_induce_of_connected_dominating
      (connectivityCore_connected i)
  · intro x hx
    change x ∈ connectivityCore i at hx
    change x ∉ S
    intro hxS
    have hxuv := hSuv hxS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxuv
    rcases hxuv with rfl | rfl
    · exact hui hx
    · exact hvi hx
  · intro x hxT hxC
    change x ∉ connectivityCore i at hxC
    obtain ⟨w, hwC, hxw⟩ := connectivityCore_dominates i x hxC
    exact ⟨w, hwC, hxw⟩

namespace Obstruction

abbrev EdgeChoice (n : Nat) := Fin n → Bool

def pInternalEdges : Fin 12 → Fin 9 × Fin 9 :=
  ![(0, 1), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7),
    (3, 8), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8)]

def remoteInternalEdges : Fin 12 → Fin 9 × Fin 9 :=
  ![(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6),
    (6, 7), (7, 8), (0, 5), (1, 6), (2, 7), (3, 8)]

def pBoundaryVertices : Fin 3 → Fin 9 :=
  ![0, 3, 4]

def remoteBoundaryVertices : Fin 3 → Fin 9 :=
  ![0, 8, 4]

def internalAdj
    (edges : Fin 12 → Fin 9 × Fin 9) (s : EdgeChoice 12)
    (u v : Fin 9) : Bool :=
  (List.ofFn fun i : Fin 12 =>
    s i && decide (edges i = (u, v) ∨ edges i = (v, u))).any id

def internalDegree
    (edges : Fin 12 → Fin 9 × Fin 9) (s : EdgeChoice 12)
    (v : Fin 9) : Nat :=
  (Finset.univ.filter fun i =>
    s i && decide ((edges i).1 = v ∨ (edges i).2 = v)).card

def boundaryDegree
    (vertices : Fin 3 → Fin 9) (b : EdgeChoice 3) (v : Fin 9) : Nat :=
  (Finset.univ.filter fun i => b i && decide (vertices i = v)).card

def boundaryCount (b : EdgeChoice 3) : Nat :=
  (Finset.univ.filter fun i => b i).card

def localValid
    (edges : Fin 12 → Fin 9 × Fin 9) (vertices : Fin 3 → Fin 9)
    (s : EdgeChoice 12) (b : EdgeChoice 3) : Prop :=
  ∀ v : Fin 9,
    internalDegree edges s v + boundaryDegree vertices b v = 2

def cycleVertices : Fin 6 → Fin 5 → Fin 9 :=
  ![![1, 2, 7, 4, 6],
    ![4, 6, 8, 5, 7],
    ![2, 3, 8, 5, 7],
    ![1, 2, 3, 8, 6],
    ![0, 1, 2, 7, 5],
    ![0, 1, 6, 8, 5]]

def cycleFinset (k : Fin 6) : Finset (Fin 9) :=
  Finset.univ.image (cycleVertices k)

def embedP (v : Fin 9) : Fin 18 :=
  ⟨v.val, by omega⟩

def embedRemote (v : Fin 9) : Fin 18 :=
  ⟨v.val + 9, by omega⟩

def pGlobalInternalEdges : Fin 12 → Fin 18 × Fin 18 :=
  fun i => (embedP (pInternalEdges i).1, embedP (pInternalEdges i).2)

def cutEdges : Fin 3 → Fin 18 × Fin 18 :=
  fun i => (embedP (pBoundaryVertices i), embedRemote (remoteBoundaryVertices i))

def tableAdj {n : Nat}
    (edges : Fin n → Fin 18 × Fin 18) (s : EdgeChoice n)
    (u v : Fin 18) : Bool :=
  (List.ofFn fun i : Fin n =>
    s i && decide (edges i = (u, v) ∨ edges i = (v, u))).any id

def pPatternAdj (s : EdgeChoice 12) (b : EdgeChoice 3) (u v : Fin 18) : Bool :=
  tableAdj pGlobalInternalEdges s u v || tableAdj cutEdges b u v

def globalCycleFinset (k : Fin 6) : Finset (Fin 18) :=
  Finset.univ.image fun i => embedP (cycleVertices k i)

def cycleClosed (s : EdgeChoice 12) (b : EdgeChoice 3) (k : Fin 6) : Prop :=
  (∀ i : Fin 5,
      internalAdj pInternalEdges s (cycleVertices k i) (cycleVertices k (i + 1)) = true) ∧
  (∀ u : Fin 18, u ∈ globalCycleFinset k →
    ∀ v : Fin 18, pPatternAdj s b u v = true → v ∈ globalCycleFinset k)

instance instDecidableLocalValid
    (edges : Fin 12 → Fin 9 × Fin 9) (vertices : Fin 3 → Fin 9)
    (s : EdgeChoice 12) (b : EdgeChoice 3) :
    Decidable (localValid edges vertices s b) := by
  unfold localValid
  infer_instance

instance instDecidableCycleClosed (s : EdgeChoice 12) (b : EdgeChoice 3) (k : Fin 6) :
    Decidable (cycleClosed s b k) := by
  unfold cycleClosed
  infer_instance

end Obstruction

end CubicP3FiniteScratch

open CubicP3Partition

namespace CubicP3FiniteScratch.ObstructionBridge

open Obstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : DecidableRel (H 0).Adj := fun u v => by
  change Decidable
    (u ≠ v ∧
      (forwardEdge 0 u.val v.val ∨ forwardEdge 0 v.val u.val))
  unfold forwardEdge brickEdges
  infer_instance

def remoteGlobalInternalEdges : Fin 12 → Fin 18 × Fin 18 :=
  fun i =>
    (embedRemote (remoteInternalEdges i).1,
      embedRemote (remoteInternalEdges i).2)

noncomputable def pChoice (F : SimpleGraph (Fin 18)) : EdgeChoice 12 := by
  classical
  exact fun i =>
    if F.Adj (pGlobalInternalEdges i).1 (pGlobalInternalEdges i).2 then true else false

noncomputable def remoteChoice (F : SimpleGraph (Fin 18)) : EdgeChoice 12 := by
  classical
  exact fun i =>
    if F.Adj (remoteGlobalInternalEdges i).1 (remoteGlobalInternalEdges i).2 then true else false

noncomputable def cutChoice (F : SimpleGraph (Fin 18)) : EdgeChoice 3 := by
  classical
  exact fun i =>
    if F.Adj (cutEdges i).1 (cutEdges i).2 then true else false

@[simp]
theorem pChoice_eq_true_iff (F : SimpleGraph (Fin 18)) (i : Fin 12) :
    pChoice F i = true ↔
      F.Adj (pGlobalInternalEdges i).1 (pGlobalInternalEdges i).2 := by
  classical
  simp [pChoice]

@[simp]
theorem remoteChoice_eq_true_iff (F : SimpleGraph (Fin 18)) (i : Fin 12) :
    remoteChoice F i = true ↔
      F.Adj (remoteGlobalInternalEdges i).1 (remoteGlobalInternalEdges i).2 := by
  classical
  simp [remoteChoice]

@[simp]
theorem cutChoice_eq_true_iff (F : SimpleGraph (Fin 18)) (i : Fin 3) :
    cutChoice F i = true ↔ F.Adj (cutEdges i).1 (cutEdges i).2 := by
  classical
  simp [cutChoice]

def pNeighbors : Fin 9 → Finset (Fin 18) :=
  ![{1, 5, 9}, {0, 2, 6}, {1, 3, 7},
    {2, 8, 17}, {6, 7, 13}, {0, 7, 8},
    {1, 4, 8}, {2, 4, 5}, {3, 5, 6}]

def remoteNeighbors : Fin 9 → Finset (Fin 18) :=
  ![{0, 10, 14}, {9, 11, 15}, {10, 12, 16},
    {11, 13, 17}, {4, 12, 14}, {9, 13, 15},
    {10, 14, 16}, {11, 15, 17}, {3, 12, 16}]

theorem h0_p_neighborFinset (v : Fin 9) :
    (H 0).neighborFinset (embedP v) = pNeighbors v := by
  fin_cases v <;> decide

theorem h0_remote_neighborFinset (v : Fin 9) :
    (H 0).neighborFinset (embedRemote v) = remoteNeighbors v := by
  fin_cases v <;> decide

theorem neighborFinset_eq_filter_of_le
    {F G : SimpleGraph (Fin 18)} (hFG : F ≤ G) (v : Fin 18)
    [DecidableRel F.Adj] [DecidableRel G.Adj] :
    F.neighborFinset v = (G.neighborFinset v).filter (F.Adj v) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨hFG h, h⟩, fun h => h.2⟩

theorem missionDegree_eq_mathlibDegree
    (G : SimpleGraph (Fin 18)) (v : Fin 18) [DecidableRel G.Adj] :
    CubicP3Partition.degree G v = G.degree v := by
  unfold CubicP3Partition.degree
  rw [Nat.card_eq_fintype_card]
  exact SimpleGraph.card_neighborSet_eq_degree G v

def boolNat (b : Bool) : Nat :=
  if b then 1 else 0

theorem card_filter_three {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Finset.filter p {a, b, c}).card =
      (if p a then 1 else 0) + (if p b then 1 else 0) +
        (if p c then 1 else 0) := by
  rw [Finset.card_filter]
  have ha : a ∉ ({b, c} : Finset α) := by
    simp [hab, hac]
  have hb : b ∉ ({c} : Finset α) := by
    simp [hbc]
  rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_singleton]
  omega

@[simp]
theorem prop_ite_true_false_eq_true (p : Prop) [Decidable p] :
    (if p then true else false) = true ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem indicator_congr (p q : Prop) [Decidable p] [Decidable q]
    (h : p ↔ q) :
    (if p then 1 else 0) = (if q then 1 else 0) := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
  · have hq : ¬q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

theorem indicator_sum_three_congr
    (p₁ p₂ p₃ q₁ q₂ q₃ : Prop)
    [Decidable p₁] [Decidable p₂] [Decidable p₃]
    [Decidable q₁] [Decidable q₂] [Decidable q₃]
    (h₁ : p₁ ↔ q₁) (h₂ : p₂ ↔ q₂) (h₃ : p₃ ↔ q₃) :
    ((if p₁ then 1 else 0) + (if p₂ then 1 else 0)) +
        (if p₃ then 1 else 0) =
      ((if q₁ then 1 else 0) + (if q₂ then 1 else 0)) +
        (if q₃ then 1 else 0) := by
  rw [indicator_congr p₁ q₁ h₁, indicator_congr p₂ q₂ h₂,
    indicator_congr p₃ q₃ h₃]

@[simp]
theorem boolNat_pChoice (F : SimpleGraph (Fin 18)) [DecidableRel F.Adj] (i : Fin 12) :
    boolNat (pChoice F i) =
      if F.Adj (pGlobalInternalEdges i).1 (pGlobalInternalEdges i).2 then 1 else 0 := by
  classical
  by_cases h :
      F.Adj (pGlobalInternalEdges i).1 (pGlobalInternalEdges i).2 <;>
    simp [boolNat, pChoice, h]

@[simp]
theorem boolNat_remoteChoice
    (F : SimpleGraph (Fin 18)) [DecidableRel F.Adj] (i : Fin 12) :
    boolNat (remoteChoice F i) =
      if F.Adj (remoteGlobalInternalEdges i).1
          (remoteGlobalInternalEdges i).2 then 1 else 0 := by
  classical
  by_cases h :
      F.Adj (remoteGlobalInternalEdges i).1
        (remoteGlobalInternalEdges i).2 <;>
    simp [boolNat, remoteChoice, h]

@[simp]
theorem boolNat_cutChoice (F : SimpleGraph (Fin 18)) [DecidableRel F.Adj] (i : Fin 3) :
    boolNat (cutChoice F i) =
      if F.Adj (cutEdges i).1 (cutEdges i).2 then 1 else 0 := by
  classical
  by_cases h : F.Adj (cutEdges i).1 (cutEdges i).2 <;>
    simp [boolNat, cutChoice, h]

def pLocalDegreeFormula (s : EdgeChoice 12) (b : EdgeChoice 3) : Fin 9 → Nat :=
  ![boolNat (s 0) + boolNat (s 1) + boolNat (b 0),
    boolNat (s 0) + boolNat (s 2) + boolNat (s 3),
    boolNat (s 2) + boolNat (s 4) + boolNat (s 5),
    boolNat (s 4) + boolNat (s 6) + boolNat (b 1),
    boolNat (s 7) + boolNat (s 8) + boolNat (b 2),
    boolNat (s 1) + boolNat (s 9) + boolNat (s 10),
    boolNat (s 3) + boolNat (s 7) + boolNat (s 11),
    boolNat (s 5) + boolNat (s 8) + boolNat (s 9),
    boolNat (s 6) + boolNat (s 10) + boolNat (s 11)]

def pInternalDegreeFormula (s : EdgeChoice 12) : Fin 9 → Nat :=
  ![boolNat (s 0) + boolNat (s 1),
    boolNat (s 0) + boolNat (s 2) + boolNat (s 3),
    boolNat (s 2) + boolNat (s 4) + boolNat (s 5),
    boolNat (s 4) + boolNat (s 6),
    boolNat (s 7) + boolNat (s 8),
    boolNat (s 1) + boolNat (s 9) + boolNat (s 10),
    boolNat (s 3) + boolNat (s 7) + boolNat (s 11),
    boolNat (s 5) + boolNat (s 8) + boolNat (s 9),
    boolNat (s 6) + boolNat (s 10) + boolNat (s 11)]

def pBoundaryDegreeFormula (b : EdgeChoice 3) : Fin 9 → Nat :=
  ![boolNat (b 0), 0, 0, boolNat (b 1), boolNat (b 2), 0, 0, 0, 0]

def remoteLocalDegreeFormula (s : EdgeChoice 12) (b : EdgeChoice 3) : Fin 9 → Nat :=
  ![boolNat (b 0) + boolNat (s 0) + boolNat (s 8),
    boolNat (s 0) + boolNat (s 1) + boolNat (s 9),
    boolNat (s 1) + boolNat (s 2) + boolNat (s 10),
    boolNat (s 2) + boolNat (s 3) + boolNat (s 11),
    boolNat (b 2) + boolNat (s 3) + boolNat (s 4),
    boolNat (s 8) + boolNat (s 4) + boolNat (s 5),
    boolNat (s 9) + boolNat (s 5) + boolNat (s 6),
    boolNat (s 10) + boolNat (s 6) + boolNat (s 7),
    boolNat (b 1) + boolNat (s 11) + boolNat (s 7)]

def remoteInternalDegreeFormula (s : EdgeChoice 12) : Fin 9 → Nat :=
  ![boolNat (s 0) + boolNat (s 8),
    boolNat (s 0) + boolNat (s 1) + boolNat (s 9),
    boolNat (s 1) + boolNat (s 2) + boolNat (s 10),
    boolNat (s 2) + boolNat (s 3) + boolNat (s 11),
    boolNat (s 3) + boolNat (s 4),
    boolNat (s 4) + boolNat (s 5) + boolNat (s 8),
    boolNat (s 5) + boolNat (s 6) + boolNat (s 9),
    boolNat (s 6) + boolNat (s 7) + boolNat (s 10),
    boolNat (s 7) + boolNat (s 11)]

def remoteBoundaryDegreeFormula (b : EdgeChoice 3) : Fin 9 → Nat :=
  ![boolNat (b 0), 0, 0, 0, boolNat (b 2), 0, 0, 0, boolNat (b 1)]

def pIncidentIndices : Fin 9 → Finset (Fin 12) :=
  ![{0, 1}, {0, 2, 3}, {2, 4, 5}, {4, 6}, {7, 8},
    {1, 9, 10}, {3, 7, 11}, {5, 8, 9}, {6, 10, 11}]

def pBoundaryIndices : Fin 9 → Finset (Fin 3) :=
  ![{0}, ∅, ∅, {1}, {2}, ∅, ∅, ∅, ∅]

def remoteIncidentIndices : Fin 9 → Finset (Fin 12) :=
  ![{0, 8}, {0, 1, 9}, {1, 2, 10}, {2, 3, 11}, {3, 4},
    {4, 5, 8}, {5, 6, 9}, {6, 7, 10}, {7, 11}]

def remoteBoundaryIndices : Fin 9 → Finset (Fin 3) :=
  ![{0}, ∅, ∅, ∅, {2}, ∅, ∅, ∅, {1}]

lemma pInternalDegree_eq_filter
    (s : EdgeChoice 12) (v : Fin 9) :
    internalDegree pInternalEdges s v =
      ((pIncidentIndices v).filter fun i => s i = true).card := by
  unfold internalDegree
  apply congrArg Finset.card
  ext i
  fin_cases v <;> fin_cases i <;>
    simp [pIncidentIndices, pInternalEdges]

lemma pBoundaryDegree_eq_filter
    (b : EdgeChoice 3) (v : Fin 9) :
    boundaryDegree pBoundaryVertices b v =
      ((pBoundaryIndices v).filter fun i => b i = true).card := by
  unfold boundaryDegree
  apply congrArg Finset.card
  ext i
  fin_cases v <;> fin_cases i <;>
    simp [pBoundaryIndices, pBoundaryVertices]

lemma remoteInternalDegree_eq_filter
    (s : EdgeChoice 12) (v : Fin 9) :
    internalDegree remoteInternalEdges s v =
      ((remoteIncidentIndices v).filter fun i => s i = true).card := by
  unfold internalDegree
  apply congrArg Finset.card
  ext i
  fin_cases v <;> fin_cases i <;>
    simp [remoteIncidentIndices, remoteInternalEdges]

lemma remoteBoundaryDegree_eq_filter
    (b : EdgeChoice 3) (v : Fin 9) :
    boundaryDegree remoteBoundaryVertices b v =
      ((remoteBoundaryIndices v).filter fun i => b i = true).card := by
  unfold boundaryDegree
  apply congrArg Finset.card
  ext i
  fin_cases v <;> fin_cases i <;>
    simp [remoteBoundaryIndices, remoteBoundaryVertices]

lemma card_filter_two {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (a b : α) (hab : a ≠ b) :
    (Finset.filter p {a, b}).card =
      (if p a then 1 else 0) + (if p b then 1 else 0) := by
  rw [Finset.card_filter]
  have ha : a ∉ ({b} : Finset α) := by simpa
  rw [Finset.sum_insert ha, Finset.sum_singleton]

lemma card_filter_one {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (a : α) :
    (Finset.filter p {a}).card = if p a then 1 else 0 := by
  rw [Finset.card_filter, Finset.sum_singleton]

theorem p_internal_degree_formula
    (s : EdgeChoice 12) (v : Fin 9) :
    internalDegree pInternalEdges s v = pInternalDegreeFormula s v := by
  rw [pInternalDegree_eq_filter]
  fin_cases v <;>
    simp [pIncidentIndices, pInternalDegreeFormula, boolNat] <;>
    first
    | rw [card_filter_two] <;> norm_num
    | rw [card_filter_three] <;> norm_num
  all_goals decide

theorem p_boundary_degree_formula
    (b : EdgeChoice 3) (v : Fin 9) :
    boundaryDegree pBoundaryVertices b v = pBoundaryDegreeFormula b v := by
  rw [pBoundaryDegree_eq_filter]
  fin_cases v <;>
    simp [pBoundaryIndices, pBoundaryDegreeFormula, boolNat] <;>
    rw [card_filter_one]

theorem remote_internal_degree_formula
    (s : EdgeChoice 12) (v : Fin 9) :
    internalDegree remoteInternalEdges s v =
      remoteInternalDegreeFormula s v := by
  rw [remoteInternalDegree_eq_filter]
  fin_cases v <;>
    simp [remoteIncidentIndices, remoteInternalDegreeFormula, boolNat] <;>
    first
    | rw [card_filter_two] <;> norm_num
    | rw [card_filter_three] <;> norm_num
  all_goals decide

theorem remote_boundary_degree_formula
    (b : EdgeChoice 3) (v : Fin 9) :
    boundaryDegree remoteBoundaryVertices b v =
      remoteBoundaryDegreeFormula b v := by
  rw [remoteBoundaryDegree_eq_filter]
  fin_cases v <;>
    simp [remoteBoundaryIndices, remoteBoundaryDegreeFormula, boolNat] <;>
    rw [card_filter_one]

theorem p_local_degree_formula
    (s : EdgeChoice 12) (b : EdgeChoice 3) (v : Fin 9) :
    internalDegree pInternalEdges s v +
        boundaryDegree pBoundaryVertices b v =
      pLocalDegreeFormula s b v := by
  rw [p_internal_degree_formula, p_boundary_degree_formula]
  fin_cases v <;>
    simp [pInternalDegreeFormula, pBoundaryDegreeFormula, pLocalDegreeFormula,
      Nat.add_assoc]

theorem remote_local_degree_formula
    (s : EdgeChoice 12) (b : EdgeChoice 3) (v : Fin 9) :
    internalDegree remoteInternalEdges s v +
        boundaryDegree remoteBoundaryVertices b v =
      remoteLocalDegreeFormula s b v := by
  rw [remote_internal_degree_formula, remote_boundary_degree_formula]
  fin_cases v <;>
    simp [remoteInternalDegreeFormula, remoteBoundaryDegreeFormula,
      remoteLocalDegreeFormula, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem p_local_degree_eq
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0) (v : Fin 9) :
    CubicP3Partition.degree F (embedP v) =
      internalDegree pInternalEdges (pChoice F) v +
        boundaryDegree pBoundaryVertices (cutChoice F) v := by
  classical
  rw [missionDegree_eq_mathlibDegree]
  change (F.neighborFinset (embedP v)).card = _
  rw [neighborFinset_eq_filter_of_le hF, h0_p_neighborFinset]
  rw [p_local_degree_formula]
  fin_cases v <;>
    simp [pNeighbors]
  all_goals
    rw [card_filter_three] <;>
      norm_num
  all_goals
    simp [pLocalDegreeFormula, boolNat_pChoice, boolNat_cutChoice,
      pGlobalInternalEdges, cutEdges, pInternalEdges, pBoundaryVertices,
      remoteBoundaryVertices, embedP, embedRemote, SimpleGraph.adj_comm]
  all_goals
    apply indicator_sum_three_congr <;>
      first
      | rfl
      | exact F.adj_comm _ _

theorem remote_local_degree_eq
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0) (v : Fin 9) :
    CubicP3Partition.degree F (embedRemote v) =
      internalDegree remoteInternalEdges (remoteChoice F) v +
        boundaryDegree remoteBoundaryVertices (cutChoice F) v := by
  classical
  rw [missionDegree_eq_mathlibDegree]
  change (F.neighborFinset (embedRemote v)).card = _
  rw [neighborFinset_eq_filter_of_le hF, h0_remote_neighborFinset]
  rw [remote_local_degree_formula]
  fin_cases v <;>
    simp [remoteNeighbors]
  all_goals
    rw [card_filter_three] <;>
      norm_num
  all_goals
    simp [remoteLocalDegreeFormula, boolNat_remoteChoice, boolNat_cutChoice,
      remoteGlobalInternalEdges, cutEdges, remoteInternalEdges,
      pBoundaryVertices, remoteBoundaryVertices, embedP, embedRemote,
      SimpleGraph.adj_comm]
  all_goals
    apply indicator_sum_three_congr <;> rfl

theorem p_local_valid_of_degree_two
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0)
    (hDegree : ∀ v, CubicP3Partition.degree F v = 2) :
    localValid pInternalEdges pBoundaryVertices (pChoice F) (cutChoice F) := by
  intro v
  rw [← p_local_degree_eq F hF v]
  exact hDegree (embedP v)

theorem remote_local_valid_of_degree_two
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0)
    (hDegree : ∀ v, CubicP3Partition.degree F v = 2) :
    localValid remoteInternalEdges remoteBoundaryVertices
      (remoteChoice F) (cutChoice F) := by
  intro v
  rw [← remote_local_degree_eq F hF v]
  exact hDegree (embedRemote v)

end CubicP3FiniteScratch.ObstructionBridge

open CubicP3Partition

namespace CubicP3FiniteScratch.Obstruction

open ObstructionBridge

lemma boundaryCount_formula (b : EdgeChoice 3) :
    boundaryCount b = boolNat (b 0) + boolNat (b 1) + boolNat (b 2) := by
  unfold boundaryCount
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  rw [card_filter_three] <;> try decide
  simp [boolNat]

lemma boolNat_le_one (b : Bool) : boolNat b ≤ 1 := by
  cases b <;> simp [boolNat]

@[simp] lemma boolNat_false : boolNat false = 0 := rfl
@[simp] lemma boolNat_true : boolNat true = 1 := rfl

lemma boolNat_injective : Function.Injective boolNat := by
  intro a b
  cases a <;> cases b <;> simp [boolNat]

lemma boundaryCount_two_cases (b : EdgeChoice 3)
    (h : boundaryCount b = 2) :
    (b 0 = true ∧ b 1 = true ∧ b 2 = false) ∨
      (b 0 = true ∧ b 1 = false ∧ b 2 = true) ∨
      (b 0 = false ∧ b 1 = true ∧ b 2 = true) := by
  rw [boundaryCount_formula] at h
  cases h0 : b 0 <;> cases h1 : b 1 <;> cases h2 : b 2 <;>
    simp [boolNat, h0, h1, h2] at h ⊢

theorem remote_boundary_count_two (s : EdgeChoice 12) (b : EdgeChoice 3)
    (h : localValid remoteInternalEdges remoteBoundaryVertices s b) :
    boundaryCount b = 2 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  have h8 := h 8
  rw [remote_local_degree_formula] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [remoteLocalDegreeFormula] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hb0 := boolNat_le_one (b 0)
  have hb1 := boolNat_le_one (b 1)
  have hb2 := boolNat_le_one (b 2)
  have hs0 := boolNat_le_one (s 0)
  have hs1 := boolNat_le_one (s 1)
  have hs2 := boolNat_le_one (s 2)
  have hs3 := boolNat_le_one (s 3)
  have hs4 := boolNat_le_one (s 4)
  have hs5 := boolNat_le_one (s 5)
  have hs6 := boolNat_le_one (s 6)
  have hs7 := boolNat_le_one (s 7)
  have hs8 := boolNat_le_one (s 8)
  have hs9 := boolNat_le_one (s 9)
  have hs10 := boolNat_le_one (s 10)
  have hs11 := boolNat_le_one (s 11)
  rw [boundaryCount_formula]
  omega

def pCase0S : EdgeChoice 12 :=
  ![false, true, true, true, false, true, true, true, true, false, true, false]

def pCase0B : EdgeChoice 3 := ![true, true, false]

def pCase1S : EdgeChoice 12 :=
  ![true, false, true, false, true, false, false, true, true, true, true, true]

def pCase1B : EdgeChoice 3 := ![true, true, false]

def pCase2S : EdgeChoice 12 :=
  ![false, true, true, true, true, false, true, false, true, true, false, true]

def pCase2B : EdgeChoice 3 := ![true, false, true]

def pCase3S : EdgeChoice 12 :=
  ![true, false, false, true, true, true, true, true, false, true, true, false]

def pCase3B : EdgeChoice 3 := ![true, false, true]

def pCase4S : EdgeChoice 12 :=
  ![true, true, false, true, true, true, false, false, true, false, true, true]

def pCase4B : EdgeChoice 3 := ![false, true, true]

def pCase5S : EdgeChoice 12 :=
  ![true, true, true, false, false, true, true, true, false, true, false, true]

def pCase5B : EdgeChoice 3 := ![false, true, true]

lemma pCase0_cycle : cycleClosed pCase0S pCase0B 0 := by decide
lemma pCase1_cycle : cycleClosed pCase1S pCase1B 1 := by decide
lemma pCase2_cycle : cycleClosed pCase2S pCase2B 3 := by decide
lemma pCase3_cycle : cycleClosed pCase3S pCase3B 2 := by decide
lemma pCase4_cycle : cycleClosed pCase4S pCase4B 5 := by decide
lemma pCase5_cycle : cycleClosed pCase5S pCase5B 4 := by decide

theorem p_cycle_obstruction_cases (s : EdgeChoice 12) (b : EdgeChoice 3)
    (hvalid : localValid pInternalEdges pBoundaryVertices s b)
    (hboundary : boundaryCount b = 2) :
    cycleClosed s b 0 ∨ cycleClosed s b 1 ∨ cycleClosed s b 2 ∨
      cycleClosed s b 3 ∨ cycleClosed s b 4 ∨ cycleClosed s b 5 := by
  have h0 := hvalid 0
  have h1 := hvalid 1
  have h2 := hvalid 2
  have h3 := hvalid 3
  have h4 := hvalid 4
  have h5 := hvalid 5
  have h6 := hvalid 6
  have h7 := hvalid 7
  have h8 := hvalid 8
  rw [p_local_degree_formula] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  simp [pLocalDegreeFormula] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hs0le := boolNat_le_one (s 0)
  have hs1le := boolNat_le_one (s 1)
  have hs2le := boolNat_le_one (s 2)
  have hs3le := boolNat_le_one (s 3)
  have hs4le := boolNat_le_one (s 4)
  have hs5le := boolNat_le_one (s 5)
  have hs6le := boolNat_le_one (s 6)
  have hs7le := boolNat_le_one (s 7)
  have hs8le := boolNat_le_one (s 8)
  have hs9le := boolNat_le_one (s 9)
  have hs10le := boolNat_le_one (s 10)
  have hs11le := boolNat_le_one (s 11)
  rcases boundaryCount_two_cases b hboundary with hb | hb | hb
  · rcases hb with ⟨hb0, hb1, hb2⟩
    cases hs0 : s 0
    · simp [hb0, hb1, hb2, hs0] at h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hs : s = pCase0S := by
        funext i
        apply boolNat_injective
        fin_cases i <;> simp [pCase0S, hs0] <;> omega
      have hb' : b = pCase0B := by
        funext i
        fin_cases i <;> simp [pCase0B, hb0, hb1, hb2]
      subst s
      subst b
      exact Or.inl pCase0_cycle
    · simp [hb0, hb1, hb2, hs0] at h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hs : s = pCase1S := by
        funext i
        apply boolNat_injective
        fin_cases i <;> simp [pCase1S, hs0] <;> omega
      have hb' : b = pCase1B := by
        funext i
        fin_cases i <;> simp [pCase1B, hb0, hb1, hb2]
      subst s
      subst b
      exact Or.inr (Or.inl pCase1_cycle)
  · rcases hb with ⟨hb0, hb1, hb2⟩
    cases hs0 : s 0
    · simp [hb0, hb1, hb2, hs0] at h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hs : s = pCase2S := by
        funext i
        apply boolNat_injective
        fin_cases i <;> simp [pCase2S, hs0] <;> omega
      have hb' : b = pCase2B := by
        funext i
        fin_cases i <;> simp [pCase2B, hb0, hb1, hb2]
      subst s
      subst b
      exact Or.inr (Or.inr (Or.inr (Or.inl pCase2_cycle)))
    · simp [hb0, hb1, hb2, hs0] at h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hs : s = pCase3S := by
        funext i
        apply boolNat_injective
        fin_cases i <;> simp [pCase3S, hs0] <;> omega
      have hb' : b = pCase3B := by
        funext i
        fin_cases i <;> simp [pCase3B, hb0, hb1, hb2]
      subst s
      subst b
      exact Or.inr (Or.inr (Or.inl pCase3_cycle))
  · rcases hb with ⟨hb0, hb1, hb2⟩
    cases hs2 : s 2
    · simp [hb0, hb1, hb2, hs2] at h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hs : s = pCase4S := by
        funext i
        apply boolNat_injective
        fin_cases i <;> simp [pCase4S, hs2] <;> omega
      have hb' : b = pCase4B := by
        funext i
        fin_cases i <;> simp [pCase4B, hb0, hb1, hb2]
      subst s
      subst b
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr pCase4_cycle))))
    · simp [hb0, hb1, hb2, hs2] at h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hs : s = pCase5S := by
        funext i
        apply boolNat_injective
        fin_cases i <;> simp [pCase5S, hs2] <;> omega
      have hb' : b = pCase5B := by
        funext i
        fin_cases i <;> simp [pCase5B, hb0, hb1, hb2]
      subst s
      subst b
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl pCase5_cycle))))

theorem p_cycle_obstruction (s : EdgeChoice 12) (b : EdgeChoice 3)
    (hvalid : localValid pInternalEdges pBoundaryVertices s b)
    (hboundary : boundaryCount b = 2) :
    ∃ k : Fin 6, cycleClosed s b k := by
  rcases p_cycle_obstruction_cases s b hvalid hboundary with
    h | h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨5, h⟩

end CubicP3FiniteScratch.Obstruction

open CubicP3Partition

namespace CubicP3FiniteScratch.ObstructionCycleBridge

open Obstruction ObstructionBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

local instance : DecidableRel (H 0).Adj := fun u v => by
  change Decidable
    (u ≠ v ∧
      (forwardEdge 0 u.val v.val ∨ forwardEdge 0 v.val u.val))
  unfold forwardEdge brickEdges
  infer_instance

theorem p_tableAdj_embed
    (s : EdgeChoice 12) (u v : Fin 9) :
    tableAdj pGlobalInternalEdges s (embedP u) (embedP v) =
      internalAdj pInternalEdges s u v := by
  unfold tableAdj internalAdj pGlobalInternalEdges
  congr 2
  funext i
  simp [embedP, Prod.ext_iff, Fin.ext_iff, Bool.decide_and]

theorem internalAdj_imp_pPatternAdj
    (s : EdgeChoice 12) (b : EdgeChoice 3) (u v : Fin 9)
    (h : internalAdj pInternalEdges s u v = true) :
    pPatternAdj s b (embedP u) (embedP v) = true := by
  simp [pPatternAdj, p_tableAdj_embed, h]

theorem tableAdj_eq_true_iff {n : Nat}
    (edges : Fin n → Fin 18 × Fin 18) (s : EdgeChoice n)
    (u v : Fin 18) :
    tableAdj edges s u v = true ↔
      ∃ i : Fin n, s i = true ∧
        (edges i = (u, v) ∨ edges i = (v, u)) := by
  simp [tableAdj]

theorem tableAdj_imp_adj
    (F : SimpleGraph (Fin 18)) {n : Nat}
    (edges : Fin n → Fin 18 × Fin 18) (s : EdgeChoice n)
    (hSelected :
      ∀ i, s i = true → F.Adj (edges i).1 (edges i).2)
    {u v : Fin 18} (h : tableAdj edges s u v = true) :
    F.Adj u v := by
  rw [tableAdj_eq_true_iff] at h
  obtain ⟨i, hi, huv | hvu⟩ := h
  · simpa [huv] using hSelected i hi
  · have hAdj : F.Adj v u := by
      simpa [hvu] using hSelected i hi
    exact F.adj_symm hAdj

theorem pPatternAdj_imp_adj
    (F : SimpleGraph (Fin 18)) (u : Fin 9) (v : Fin 18)
    (h : pPatternAdj (pChoice F) (cutChoice F) (embedP u) v = true) :
    F.Adj (embedP u) v := by
  simp only [pPatternAdj, Bool.or_eq_true] at h
  rcases h with hInternal | hCut
  · exact tableAdj_imp_adj F pGlobalInternalEdges (pChoice F)
      (fun i hi => (pChoice_eq_true_iff F i).mp hi) hInternal
  · exact tableAdj_imp_adj F cutEdges (cutChoice F)
      (fun i hi => (cutChoice_eq_true_iff F i).mp hi) hCut

abbrev PEdgeLocation := Fin 12 ⊕ Fin 3

def pLocationEdge : PEdgeLocation → Fin 18 × Fin 18
  | Sum.inl i => pGlobalInternalEdges i
  | Sum.inr i => cutEdges i

theorem h0_adj_has_pLocation (u : Fin 9) (v : Fin 18)
    (h : (H 0).Adj (embedP u) v) :
    ∃ location : PEdgeLocation,
      pLocationEdge location = (embedP u, v) ∨
        pLocationEdge location = (v, embedP u) := by
  have hv : v ∈ pNeighbors u := by
    rw [← h0_p_neighborFinset]
    simpa only [SimpleGraph.mem_neighborFinset]
  fin_cases u <;> fin_cases v <;>
    simp [pNeighbors] at hv ⊢ <;> decide

theorem selected_edge_of_adj
    (F : SimpleGraph (Fin 18)) {edge : Fin 18 × Fin 18}
    {u v : Fin 18} (h : F.Adj u v)
    (hEdge : edge = (u, v) ∨ edge = (v, u)) :
    F.Adj edge.1 edge.2 := by
  rcases hEdge with huv | hvu
  · simpa [huv] using h
  · have h' : F.Adj v u := F.adj_symm h
    simpa [hvu] using h'

theorem adj_imp_pPatternAdj
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0)
    (u : Fin 9) (v : Fin 18) (h : F.Adj (embedP u) v) :
    pPatternAdj (pChoice F) (cutChoice F) (embedP u) v = true := by
  obtain ⟨location, hLocation⟩ :=
    h0_adj_has_pLocation u v (hF h)
  simp only [pPatternAdj, Bool.or_eq_true]
  rcases location with i | i
  · left
    rw [tableAdj_eq_true_iff]
    refine ⟨i, ?_, hLocation⟩
    apply (pChoice_eq_true_iff F i).mpr
    exact selected_edge_of_adj F h hLocation
  · right
    rw [tableAdj_eq_true_iff]
    refine ⟨i, ?_, hLocation⟩
    apply (cutChoice_eq_true_iff F i).mpr
    exact selected_edge_of_adj F h hLocation

theorem reachable_mem_of_closed
    (F : SimpleGraph (Fin 18)) (C : Finset (Fin 18))
    (hClosed : ∀ u, u ∈ C → ∀ v, F.Adj u v → v ∈ C)
    {u v : Fin 18} (hu : u ∈ C) (hReachable : F.Reachable u v) :
    v ∈ C := by
  rcases hReachable with ⟨walk⟩
  induction walk with
  | nil => exact hu
  | cons hAdj walk ih =>
      exact ih (hClosed _ hu _ hAdj)

theorem cycle_actual_closed
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0)
    (k : Fin 6)
    (hCycle : cycleClosed (pChoice F) (cutChoice F) k) :
    ∀ u, u ∈ globalCycleFinset k →
      ∀ v, F.Adj u v → v ∈ globalCycleFinset k := by
  intro u hu v huv
  rcases Finset.mem_image.mp hu with ⟨i, -, rfl⟩
  apply hCycle.2 _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) v
  exact adj_imp_pPatternAdj F hF (cycleVertices k i) v huv

theorem cycle_edge_adj
    (F : SimpleGraph (Fin 18)) (k : Fin 6)
    (hCycle : cycleClosed (pChoice F) (cutChoice F) k)
    (i : Fin 5) :
    F.Adj (embedP (cycleVertices k i))
      (embedP (cycleVertices k (i + 1))) := by
  apply pPatternAdj_imp_adj F (cycleVertices k i)
  apply internalAdj_imp_pPatternAdj
  exact hCycle.1 i

def cycleAnchor (k : Fin 6) : Fin 18 :=
  embedP (cycleVertices k 0)

theorem cycle_vertex_reachable
    (F : SimpleGraph (Fin 18)) (k : Fin 6)
    (hCycle : cycleClosed (pChoice F) (cutChoice F) k)
    (j : Fin 5) :
    F.Reachable (cycleAnchor k) (embedP (cycleVertices k j)) := by
  have e₀ := (cycle_edge_adj F k hCycle 0).reachable
  have e₁ := (cycle_edge_adj F k hCycle 1).reachable
  have e₂ := (cycle_edge_adj F k hCycle 2).reachable
  have e₃ := (cycle_edge_adj F k hCycle 3).reachable
  fin_cases j
  · exact SimpleGraph.Reachable.refl _
  · simpa [cycleAnchor] using e₀
  · simpa [cycleAnchor] using e₀.trans e₁
  · simpa [cycleAnchor] using (e₀.trans e₁).trans e₂
  · simpa [cycleAnchor] using ((e₀.trans e₁).trans e₂).trans e₃

theorem cycle_member_reachable
    (F : SimpleGraph (Fin 18)) (k : Fin 6)
    (hCycle : cycleClosed (pChoice F) (cutChoice F) k)
    {v : Fin 18} (hv : v ∈ globalCycleFinset k) :
    F.Reachable (cycleAnchor k) v := by
  rcases Finset.mem_image.mp hv with ⟨j, -, rfl⟩
  exact cycle_vertex_reachable F k hCycle j

theorem cycle_reachable_iff_mem
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0)
    (k : Fin 6)
    (hCycle : cycleClosed (pChoice F) (cutChoice F) k)
    (v : Fin 18) :
    F.Reachable (cycleAnchor k) v ↔ v ∈ globalCycleFinset k := by
  constructor
  · apply reachable_mem_of_closed F (globalCycleFinset k)
      (cycle_actual_closed F hF k hCycle)
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩
  · exact cycle_member_reachable F k hCycle

theorem globalCycleFinset_card (k : Fin 6) :
    (globalCycleFinset k).card = 5 := by
  fin_cases k <;> decide

theorem cycle_componentOrder_eq_five
    (F : SimpleGraph (Fin 18)) (hF : F ≤ H 0)
    (k : Fin 6)
    (hCycle : cycleClosed (pChoice F) (cutChoice F) k) :
    componentOrder F (cycleAnchor k) = 5 := by
  unfold componentOrder
  calc
    Nat.card {v : Fin 18 // F.Reachable (cycleAnchor k) v} =
        (globalCycleFinset k).card :=
      Nat.subtype_card (globalCycleFinset k)
        (fun v => (cycle_reachable_iff_mem F hF k hCycle v).symm)
    _ = 5 := globalCycleFinset_card k

theorem h0_no_divisible_twoFactor :
    ¬HasDivisibleTwoFactor (H 0) := by
  rintro ⟨F, hTwoFactor, hComponentOrders⟩
  rcases hTwoFactor with ⟨hF, hDegree⟩
  have hPValid :=
    p_local_valid_of_degree_two F hF hDegree
  have hRemoteValid :=
    remote_local_valid_of_degree_two F hF hDegree
  have hBoundary :
      boundaryCount (cutChoice F) = 2 :=
    remote_boundary_count_two (remoteChoice F) (cutChoice F) hRemoteValid
  obtain ⟨k, hCycle⟩ :=
    p_cycle_obstruction (pChoice F) (cutChoice F) hPValid hBoundary
  have hDivisible := hComponentOrders (cycleAnchor k)
  rw [cycle_componentOrder_eq_five F hF k hCycle] at hDivisible
  norm_num at hDivisible

theorem h0_no_divisible_complement :
    ¬HasDivisibleComplement (H 0) := by
  rintro ⟨M, -, hDivisible⟩
  exact h0_no_divisible_twoFactor
    ⟨matchingComplement (H 0) M, hDivisible⟩

end CubicP3FiniteScratch.ObstructionCycleBridge

open CubicP3Partition

theorem solution :
    Cubic (H 0) ∧ ThreeVertexConnected (H 0) ∧
      Nonempty (P3Factor (H 0)) ∧ ¬ HasDivisibleComplement (H 0) := by
  exact
    ⟨CubicP3FiniteScratch.h0_cubic,
      CubicP3FiniteScratch.h0_threeVertexConnected,
      CubicP3FiniteScratch.h0_has_p3Factor,
      CubicP3FiniteScratch.ObstructionCycleBridge.h0_no_divisible_complement⟩
