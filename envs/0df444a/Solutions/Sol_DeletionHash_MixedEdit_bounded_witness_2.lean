-- Prove2me | solution 2 for DeletionHash.MixedEdit.bounded_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:09:43.313771+00:00
-- url     : https://prove2.me/submissions/3d69ed8f-7e14-4477-858c-0b1b44e5eb10

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
import Definitions.Def_DeletionHash_MixedEdit_Generation
import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Logic.Relation
import Theorems.Thm_DeletionHash_MixedEdit_confusable_record
import Theorems.Thm_DeletionHash_MixedEdit_connected_blocks
import Theorems.Thm_DeletionHash_MixedEdit_relation_savings
import Theorems.Thm_DeletionHash_MixedEdit_separated_coverage
import Theorems.Thm_DeletionHash_MixedEdit_spectrum_simple_path


/-!
A non-two-colorable connected graph has an odd closed walk based at any
specified vertex. The same conclusion holds at a vertex whose own connected
component is non-two-colorable. The final interface indexes the actual walk by
`Fin (m + 1)`, including both endpoints, for use with finite scan arguments.
No finiteness assumption on the ambient graph is needed.
-/
namespace DeletionGraph.OddGraphWalk

variable {V : Type*} {G : SimpleGraph V}

/-- Negating mathlib's closed-walk characterization of two-colorability gives
an odd loop, initially without any constraint on its base vertex. -/
theorem exists_odd_loop (hnot : ¬ G.Colorable 2) :
    ∃ u : V, ∃ q : G.Walk u u, Odd q.length := by
  classical
  by_contra hnone
  apply hnot
  apply SimpleGraph.two_colorable_iff_forall_loop_even.mpr
  intro u q
  exact Nat.not_odd_iff_even.mp (fun hq => hnone ⟨u, q, hq⟩)

/-- Travelling to an odd loop and returning along the reverse connecting walk
changes its length by an even number. -/
theorem exists_odd_loop_at (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ q : G.Walk x x, Odd q.length := by
  classical
  obtain ⟨u, q, hq⟩ := exists_odd_loop hnot
  let a : G.Walk x u := (hconnected x u).some
  refine ⟨(a.append q).append a.reverse, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  obtain ⟨r, hr⟩ := hq
  refine ⟨a.length + r, ?_⟩
  omega

/-- The odd loop can be based at the actual ambient vertex `x`, when only its
own induced connected component is known to be non-two-colorable. -/
theorem component_exists_odd_loop_at (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ q : G.Walk x x, Odd q.length := by
  classical
  let C := G.connectedComponentMk x
  let xc : C := ⟨x, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  obtain ⟨q, hq⟩ := exists_odd_loop_at C.connected_toSimpleGraph hnot xc
  have hm : Odd (q.map C.toSimpleGraph_hom).length := by
    simpa only [SimpleGraph.Walk.length_map] using hq
  exact ⟨q.map C.toSimpleGraph_hom, hm⟩

/-- A walk supplies its own finite vertex sequence: no enumeration or edge
realization assumption is added when converting to the scan interface. -/
theorem indexed_of_odd_loop {x : V} (q : G.Walk x x) (hq : Odd q.length) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  refine ⟨q.length, hq, fun i => q.getVert i.val, ?_, ?_, ?_⟩
  · exact q.getVert_zero
  · exact q.getVert_length
  · intro i
    exact q.adj_getVert_succ i.isLt

/-- Finite-index form for a non-two-colorable connected graph. -/
theorem connected_odd_walk (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  obtain ⟨q, hq⟩ := exists_odd_loop_at hconnected hnot x
  exact indexed_of_odd_loop q hq

/-- Finite-index form based at `x`, assuming only that the component containing
`x` is non-two-colorable. Other components impose no hypotheses. -/
theorem component_odd_walk (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by
  obtain ⟨q, hq⟩ := component_exists_odd_loop_at x hnot
  exact indexed_of_odd_loop q hq


end DeletionGraph.OddGraphWalk

/-!
Finite connected sets can be built from one member by repeatedly adding a
member adjacent to the current set. The growth order is proved to exist from
induced connectedness; no enumeration or spanning tree is assumed.
-/

namespace DeletionGraph.FiniteConnectedGrowth

variable {α : Type*} [DecidableEq α]

/-- Edges are restricted to the chosen finite vertex set. -/
def Induced (B : Finset α) (r : α → α → Prop) (u v : α) : Prop :=
  u ∈ B ∧ v ∈ B ∧ r u v

/-- Every nonempty proper subset of a connected finite set has an outgoing edge. -/
theorem frontier (B S : Finset α) (r : α → α → Prop)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (hsub : S ⊆ B) (hS : S.Nonempty) (hproper : S ≠ B) :
    ∃ w ∈ B, w ∉ S ∧ ∃ u ∈ S, r w u ∨ r u w := by
  classical
  by_contra hnone
  have preserve : ∀ a b, Relation.EqvGen (Induced B r) a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hpath
    induction hpath with
    | rel a b hedge =>
      obtain ⟨haB, hbB, hr⟩ := hedge
      constructor
      · intro haS
        by_contra hbS
        exact hnone ⟨b, hbB, hbS, a, haS, Or.inr hr⟩
      · intro hbS
        by_contra haS
        exact hnone ⟨a, haB, haS, b, hbS, Or.inl hr⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  obtain ⟨a, haS⟩ := hS
  have hback : B ⊆ S := by
    intro b hbB
    exact (preserve a b (hconnected a (hsub haS) b hbB)).mp haS
  exact hproper (Finset.Subset.antisymm hsub hback)

/-- Induction by adjoining adjacent members of a nonempty induced connected set. -/
theorem connected_induction (B : Finset α) (r : α → α → Prop)
    (hB : B.Nonempty)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (P : Finset α → Prop)
    (hsingleton : ∀ a ∈ B, P {a})
    (hgrowth : ∀ U : Finset α, U ⊆ B → ∀ w ∈ B, w ∉ U →
      (∃ u ∈ U, r w u ∨ r u w) → P U → P (insert w U)) : P B := by
  have aux : ∀ d : ℕ, ∀ U : Finset α, U ⊆ B → U.Nonempty →
      P U → B.card - U.card = d → P B := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro U hsub hU hP hdiff
      by_cases heq : U = B
      · simpa only [heq] using hP
      · obtain ⟨w, hwB, hwU, hadj⟩ := frontier B U r hconnected hsub hU heq
        have hsub' : insert w U ⊆ B := Finset.insert_subset_iff.mpr ⟨hwB, hsub⟩
        have hP' : P (insert w U) := hgrowth U hsub w hwB hwU hadj hP
        have hcard : (insert w U).card = U.card + 1 := Finset.card_insert_of_notMem hwU
        have hbound : (insert w U).card ≤ B.card := Finset.card_le_card hsub'
        have hsmaller : B.card - (insert w U).card < d := by omega
        exact ih (B.card - (insert w U).card) hsmaller (insert w U) hsub'
          ⟨w, Finset.mem_insert_self w U⟩ hP' rfl
  obtain ⟨a, ha⟩ := hB
  exact aux (B.card - ({a} : Finset α).card) {a}
    (Finset.singleton_subset_iff.mpr ha) ⟨a, Finset.mem_singleton_self a⟩
    (hsingleton a ha) rfl

/-- One saved unit at every connected addition gives the usual (d-1)|B|+1 bound. -/
theorem connected_count_bound (B : Finset α) (r : α → α → Prop)
    (hB : B.Nonempty)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (f : Finset α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hsingleton : ∀ a ∈ B, f {a} ≤ d)
    (hgrowth : ∀ U : Finset α, U ⊆ B → ∀ w ∈ B, w ∉ U →
      (∃ u ∈ U, r w u ∨ r u w) → f (insert w U) + 1 ≤ f U + d) :
    f B ≤ (d - 1) * B.card + 1 := by
  apply connected_induction B r hB hconnected (fun U => f U ≤ (d - 1) * U.card + 1)
  · intro a ha
    have hbase := hsingleton a ha
    simp only [Finset.card_singleton, Nat.mul_one]
    omega
  · intro U hsub w hwB hwU hadj hbound
    have hstep := hgrowth U hsub w hwB hwU hadj
    rw [Finset.card_insert_of_notMem hwU, Nat.mul_add, Nat.mul_one]
    omega


end DeletionGraph.FiniteConnectedGrowth
/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGraph.OverlapCollision
variable (α : Type*) [Fintype α]
abbrev Bits (n : ℕ) := Fin n → α
def padBits {n : ℕ} (x : Bits α n) (i : ℕ) : Option α :=
  if hi : i < n then some (x ⟨i, hi⟩) else none
def Agree (p : ℕ → Option α) (a : ℕ) (q : ℕ → Option α) (b k : ℕ) : Prop :=
  ∀ i, i < k → p (a+i) = q (b+i)
/-- Actual length-n words over an arbitrary finite alphabet whose indicated length-k windows agree. -/
abbrev Collision (n k a b : ℕ) :=
  {x : Bits α n // Agree α (padBits α x) a (padBits α x) b k}

noncomputable instance collisionFintype (n k a b : ℕ) :
    Fintype (Collision α n k a b) := by
  classical
  unfold Collision
  infer_instance

/-- Indices outside the later interval `[b,b+k)`, in their original order. -/
def keptIndex (n k b : ℕ) (hb : b + k ≤ n) (i : Fin (n - k)) : Fin n :=
  if h : i.val < b then ⟨i.val, by omega⟩
  else ⟨i.val + k, by omega⟩

/-- Remove exactly the later substring; retain n-k actual letters. -/
def encode (n k b : ℕ) (hb : b + k ≤ n) (x : Bits α n) : Bits α (n - k) :=
  fun i => x (keptIndex n k b hb i)

/-- Equality of encodings preserves each letter outside the removed interval. -/
theorem encode_eq_at (n k b : ℕ) (hb : b + k ≤ n)
    (x y : Bits α n) (heq : encode α n k b hb x = encode α n k b hb y)
    (j : ℕ) (hj : j < n) (hout : j < b ∨ b + k ≤ j) :
    padBits α x j = padBits α y j := by
  rcases hout with hbefore | hafter
  · have hj' : j < n - k := by omega
    have hh := congrFun heq (⟨j, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_pos hbefore, padBits, dif_pos hj, Option.some.injEq] using hh
  · have hj' : j - k < n - k := by omega
    have hbefore : ¬j - k < b := by omega
    have hrestore : j - k + k = j := by omega
    have hh := congrFun heq (⟨j - k, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_neg hbefore, hrestore,
      padBits, dif_pos hj, Option.some.injEq] using hh

/-- A collision reconstructs each deleted letter from a strictly earlier letter.
No disjointness of the two windows is used. -/
theorem encode_injective_of_agree (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) (x y : Bits α n)
    (hx : Agree α (padBits α x) a (padBits α x) b k)
    (hy : Agree α (padBits α y) a (padBits α y) b k)
    (heq : encode α n k b hb x = encode α n k b hb y) : x = y := by
  have hall : ∀ j, j < n → padBits α x j = padBits α y j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hbefore : j < b
      · exact encode_eq_at α n k b hb x y heq j hj (Or.inl hbefore)
      by_cases hafter : b + k ≤ j
      · exact encode_eq_at α n k b hb x y heq j hj (Or.inr hafter)
      have hoffset : j - b < k := by omega
      have hearlier : a + (j - b) < j := by omega
      have hearlier_bound : a + (j - b) < n := by omega
      have hrestore : b + (j - b) = j := by omega
      have hxcopy := hx (j - b) hoffset
      have hycopy := hy (j - b) hoffset
      rw [hrestore] at hxcopy hycopy
      exact hxcopy.symm.trans ((ih (a + (j - b)) hearlier hearlier_bound).trans hycopy)
  funext j
  simpa only [padBits, dif_pos j.isLt, Option.some.injEq] using hall j.val j.isLt

def collisionEncode (n k a b : ℕ) (hb : b + k ≤ n) :
    Collision α n k a b → Bits α (n - k) :=
  fun x => encode α n k b hb x.val

theorem collisionEncode_injective (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) : Function.Injective (collisionEncode α n k a b hb) := by
  intro x y heq
  apply Subtype.ext
  exact encode_injective_of_agree α n k a b hab hb x.val y.val x.property y.property heq

/-- The concrete collision set has at most q^(n-k) members, even when the
windows overlap. The earlier window bound follows already from a<b and hb. -/
theorem collision_card_le (n k a b : ℕ) (hab : a < b)
    (_ha : a + k ≤ n) (hb : b + k ≤ n) :
    Fintype.card (Collision α n k a b) ≤ Fintype.card α ^ (n - k) := by
  calc
    Fintype.card (Collision α n k a b) ≤ Fintype.card (Bits α (n - k)) :=
      Fintype.card_le_of_injective (collisionEncode α n k a b hb)
        (collisionEncode_injective α n k a b hab hb)
    _ = Fintype.card α ^ (n - k) := by simp [Bits]

end DeletionGraph.OverlapCollision

/-!
A finite union bound over actual pairs of distinct ordered positions a < b.
Their number is derived by an explicit equivalence with a triangular sigma
type; no pair-count or union-cardinality inequality is assumed.
-/
namespace DeletionGraph.FinitePairUnion

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Choose the larger position b, then one of its b smaller positions. -/
def orderedPairEquiv (n : ℕ) : OrderedPair n ≃ Σ b : Fin n, Fin b.val where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv := by rintro ⟨⟨a, b⟩, hab⟩; rfl
  right_inv := by rintro ⟨b, a⟩; rfl

/-- The number of pairs a < b among n positions is exactly choose n 2,
including the empty cases n = 0 and n = 1. -/
theorem ordered_pair_card (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by
  rw [Fintype.card_congr (orderedPairEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

/-- A union of events indexed by a < b has at most choose n 2 times the
maximum event size. The counted set contains each outcome only once. -/
theorem ordered_pair_union_bound {α : Type*} [Fintype α] [DecidableEq α]
    (n M : ℕ) (P : Fin n → Fin n → α → Prop)
    (hcount : ∀ a b, a < b → (univ.filter (P a b)).card ≤ M) :
    (univ.filter (fun x => ∃ a b, a < b ∧ P a b x)).card ≤ n.choose 2 * M := by
  let events : OrderedPair n → Finset α := fun p => univ.filter (P p.val.1 p.val.2)
  have hcover : univ.filter (fun x => ∃ a b, a < b ∧ P a b x) =
      (univ : Finset (OrderedPair n)).biUnion events := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, events]
    constructor
    · rintro ⟨a, b, hab, hx⟩
      exact ⟨⟨(a, b), hab⟩, hx⟩
    · rintro ⟨p, hx⟩
      exact ⟨p.val.1, p.val.2, p.property, hx⟩
  rw [hcover]
  calc
    ((univ : Finset (OrderedPair n)).biUnion events).card ≤
        (univ : Finset (OrderedPair n)).card * M :=
      Finset.card_biUnion_le_card_mul _ events M
        (fun p _ => hcount p.val.1 p.val.2 p.property)
    _ = n.choose 2 * M := by rw [Finset.card_univ, ordered_pair_card]


end

end DeletionGraph.FinitePairUnion
namespace DeletionGraph.UniqueWordCount
open OverlapCollision
variable (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
attribute [local instance] Classical.propDecidable

def KUnique (p : ℕ → Option α) (n k : ℕ) : Prop :=
  ∀ a b, a+k ≤ n → b+k ≤ n → Agree α p a p b k → a=b
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique α (padBits α x) n k)

noncomputable def nonuniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ KUnique α (padBits α x) n k)

/-- Both starting positions are actual valid windows in the finite word. -/
def RepeatedWindow {n : ℕ} (k : ℕ) (a b : Fin n) (x : Bits α n) : Prop :=
  a.val + k ≤ n ∧ b.val + k ≤ n ∧ Agree α (padBits α x) a.val (padBits α x) b.val k

theorem not_unique_iff_pair {n k : ℕ} (hk : 1 ≤ k) (x : Bits α n) :
    ¬ KUnique α (padBits α x) n k ↔
      ∃ a b : Fin n, a < b ∧ RepeatedWindow α k a b x := by
  classical
  constructor
  · intro hx
    simp only [KUnique, not_forall] at hx
    obtain ⟨a, b, ha, hb, hab, hne⟩ := hx
    have han : a < n := by omega
    have hbn : b < n := by omega
    by_cases hlt : a < b
    · exact ⟨⟨a, han⟩, ⟨b, hbn⟩, hlt, ha, hb, hab⟩
    · refine ⟨⟨b, hbn⟩, ⟨a, han⟩, ?_, hb, ha, ?_⟩
      · change b < a
        omega
      · intro i hi
        exact (hab i hi).symm
  · rintro ⟨a, b, hlt, ha, hb, hab⟩ hx
    have heq := hx a.val b.val ha hb hab
    exact (Nat.ne_of_lt hlt) heq

theorem family_partition (n k : ℕ) :
    (uniqueWords α n k).card + (nonuniqueWords α n k).card = Fintype.card α ^ n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Bits α n))) (fun x => KUnique α (padBits α x) n k)
  simpa only [uniqueWords, nonuniqueWords, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin] using h

theorem unique_of_length_lt {n k : ℕ} (hk : n < k) (x : Bits α n) :
    KUnique α (padBits α x) n k := by
  intro a b ha hb hab
  omega

theorem uniqueWords_eq_univ_of_length_lt {n k : ℕ} (hk : n < k) :
    uniqueWords α n k = Finset.univ := by
  classical
  ext x
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact unique_of_length_lt α hk x

theorem card_uniqueWords_of_length_lt {n k : ℕ} (hk : n < k) :
    (uniqueWords α n k).card = Fintype.card α ^ n := by
  rw [uniqueWords_eq_univ_of_length_lt α hk]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- A fixed pair contributes at most 2^(n-k) words, with overlapping and
out-of-bounds pairs both handled explicitly. -/
theorem repeatedWindow_card_le (n k : ℕ) (a b : Fin n) (hab : a < b) :
    (Finset.univ.filter (RepeatedWindow α k a b)).card ≤ Fintype.card α ^ (n - k) := by
  classical
  by_cases ha : a.val + k ≤ n
  · by_cases hb : b.val + k ≤ n
    · have heq : (Finset.univ.filter (RepeatedWindow α k a b)).card =
          Fintype.card (OverlapCollision.Collision α n k a.val b.val) := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, RepeatedWindow, ha, hb, true_and]
      rw [heq]
      exact OverlapCollision.collision_card_le α n k a.val b.val hab ha hb
    · have hz : Finset.univ.filter (RepeatedWindow α k a b) = ∅ := by
        ext x
        simp [RepeatedWindow, hb]
      rw [hz]
      exact Nat.zero_le _
  · have hz : Finset.univ.filter (RepeatedWindow α k a b) = ∅ := by
      ext x
      simp [RepeatedWindow, ha]
    rw [hz]
    exact Nat.zero_le _

/-- Union bound on the actual nonunique family, counted once per word. -/
theorem nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card ≤ n.choose 2 * Fintype.card α ^ (n - k) := by
  classical
  have h := FinitePairUnion.ordered_pair_union_bound n (Fintype.card α ^ (n - k))
    (RepeatedWindow α k) (repeatedWindow_card_le α n k)
  simpa only [nonuniqueWords, not_unique_iff_pair α hk] using h

theorem scaled_nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card * Fintype.card α ^ k ≤ n.choose 2 * Fintype.card α ^ n := by
  by_cases hkn : k ≤ n
  · have h := Nat.mul_le_mul_right (Fintype.card α ^ k) (nonunique_card_le α n k hk)
    have hp : Fintype.card α ^ (n - k) * Fintype.card α ^ k = Fintype.card α ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    simpa only [Nat.mul_assoc, hp] using h
  · have h := family_partition α n k
    rw [card_uniqueWords_of_length_lt α (by omega)] at h
    have hz : (nonuniqueWords α n k).card = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.zero_le]

/-- The manuscript's union-bound estimate, with the cardinality of the
actual k-unique family and no assumed collision-probability premise. -/
theorem card_unique_lower_bound (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n ≤
      (uniqueWords α n k).card := by
  have hpow : (0 : ℚ) < Fintype.card α ^ k := pow_pos (by exact_mod_cast Fintype.card_pos (α := α)) _
  have hscaled : ((nonuniqueWords α n k).card : ℚ) * (Fintype.card α : ℚ) ^ k ≤
      (n.choose 2 : ℚ) * (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast scaled_nonunique_card_le α n k hk
  have hbad : ((nonuniqueWords α n k).card : ℚ) ≤
      (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k * (Fintype.card α : ℚ) ^ n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hpart : ((uniqueWords α n k).card : ℚ) + (nonuniqueWords α n k).card = (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast family_partition α n k
  nlinarith

theorem card_unique_lower_bound_real (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℝ) / (Fintype.card α : ℝ) ^ k) * (Fintype.card α : ℝ) ^ n ≤
      (uniqueWords α n k).card := by
  have h : (((1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n : ℚ) : ℝ) ≤
      (((uniqueWords α n k).card : ℚ) : ℝ) := by
    exact_mod_cast card_unique_lower_bound α n k hk
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using h

end DeletionGraph.UniqueWordCount
namespace DeletionGraph.UniqueBridge
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem window_as_ofFn {n k a : ℕ} (x : Word α n) (ha : a+k ≤ n) :
    window k (letters x) a = List.ofFn (fun i : Fin k => x ⟨a+i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [window, letters, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [window, letters, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem window_eq_iff {n k a b : ℕ} (x : Word α n)
    (ha : a+k ≤ n) (hb : b+k ≤ n) :
    window k (letters x) a = window k (letters x) b ↔
      OverlapCollision.Agree α (OverlapCollision.padBits α x) a
        (OverlapCollision.padBits α x) b k := by
  rw [window_as_ofFn x ha, window_as_ofFn x hb, List.ofFn_inj]
  constructor
  · intro h i hi
    have he := congrFun h (⟨i, hi⟩ : Fin k)
    simpa only [OverlapCollision.padBits, dif_pos (show a+i<n by omega),
      dif_pos (show b+i<n by omega), Option.some.injEq] using he
  · intro h
    funext i
    have he := h i.val i.isLt
    simpa only [OverlapCollision.padBits, dif_pos (show a+i.val<n by omega),
      dif_pos (show b+i.val<n by omega), Option.some.injEq] using he

theorem unique_iff {n k : ℕ} (x : Word α n) :
    IsUnique k (letters x) ↔ UniqueWordCount.KUnique α (OverlapCollision.padBits α x) n k := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range, letters, List.length_ofFn]
  constructor
  · intro h a b ha hb hab
    have hkn : k ≤ n := by omega
    apply h a (by simp only [if_pos hkn]; omega) b (by simp only [if_pos hkn]; omega)
    exact (window_eq_iff x ha hb).mpr hab
  · intro h a ha b hb hab
    by_cases hkn : k ≤ n
    · simp only [if_pos hkn] at ha hb
      exact h a b (by omega) (by omega) ((window_eq_iff x (by omega) (by omega)).mp hab)
    · simp only [if_neg hkn] at ha
      omega

theorem family_eq (n k : ℕ) : uniqueFamily α n k = UniqueWordCount.uniqueWords α n k := by
  classical
  ext x
  simp only [uniqueFamily, UniqueWordCount.uniqueWords, Finset.mem_filter,
    Finset.mem_univ, true_and, unique_iff]

end DeletionGraph.UniqueBridge
namespace DeletionGraph.WordPaths
open OverlapCollision UniqueWordCount
variable (α : Type*)
/-- A length-L window has a valid occurrence in the finite prefix of x. -/
def Occurs (x : (ℕ → Option α)) (n : ℕ) (p : (ℕ → Option α)) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree α x a p i L

/-- Two consecutive L-windows must occur consecutively in a k-unique x. -/
theorem consecutive_occurrences
    (x p : (ℕ → Option α)) (n k L i a b : ℕ)
    (hx : KUnique α x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree α x a p i L) (hright : Agree α x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree α x (a + 1) x b k := by
    intro j hj
    have hl := hleft (j + 1) (by omega)
    have hr := hright j (by omega)
    calc
      x (a + 1 + j) = x (a + (j + 1)) := congrArg x (by omega)
      _ = p (i + (j + 1)) := hl
      _ = p (i + 1 + j) := congrArg p (by omega)
      _ = x (b + j) := hr.symm
  exact (hx (a + 1) b (by omega) (by omega) hmatch).symm

/--
All L-windows of p occurring in x forces the whole length-(L+D) word to
occur in x. This establishes contiguity rather than taking it as a premise.
-/
theorem all_windows_occur_implies_subword
    (x p : (ℕ → Option α)) (n k L D : ℕ)
    (hx : KUnique α x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs α x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree α x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree α x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences α x p n k L i (a + i) b
        hx hk hprev.1 hb hprev.2 hnext
      constructor
      · omega
      · have hindex : a + (i + 1) = b := by omega
        simpa only [hindex] using hnext
  refine ⟨a, by have hlast := (aligned D le_rfl).1; omega, ?_⟩
  intro j hj
  let i := min j D
  have hiD : i ≤ D := Nat.min_le_right j D
  have hij : i ≤ j := Nat.min_le_left j D
  have hlocal : j - i < L := by
    dsimp [i]
    by_cases h : j ≤ D
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have heq := (aligned i hiD).2 (j - i) hlocal
  have hsource : a + i + (j - i) = a + j := by omega
  have htarget : i + (j - i) = 0 + j := by omega
  simpa only [hsource, htarget] using heq

/-- The full word occurrence is unique; no second root position is needed. -/
theorem subword_position_unique
    (x p : (ℕ → Option α)) (n k m a b : ℕ)
    (hx : KUnique α x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree α x a p 0 m) (hright : Agree α x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm

end DeletionGraph.WordPaths
namespace DeletionGraph.SpectrumPath
open DeletionHash.MixedEdit UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem nonzero_iff_mem (L : ℕ) (x : List α) (g : Gram α L) :
    spectrum L x g ≠ 0 ↔ List.ofFn g ∈ windows L x := by
  simp [DeletionHash.MixedEdit.spectrum, List.count_eq_zero]

theorem windows_mem_iff {n L : ℕ} (x : Word α n) (g : Gram α L) :
    List.ofFn g ∈ windows L (letters x) ↔
      ∃ a, a+L ≤ n ∧ window L (letters x) a = List.ofFn g := by
  unfold windows starts
  simp only [List.mem_map, List.mem_range, letters, List.length_ofFn]
  constructor
  · rintro ⟨a, ha, hg⟩
    by_cases h : L ≤ n
    · simp only [if_pos h] at ha
      exact ⟨a, by omega, hg⟩
    · simp only [if_neg h] at ha
      omega
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ?_, hg⟩
    rw [if_pos (show L ≤ n by omega)]
    omega

theorem spectrum_boolean {n L : ℕ} (y : Word α n)
    (hy : IsUnique (L-1) (letters y)) :
    ∀ g, spectrum L (letters y) g = 0 ∨ spectrum L (letters y) g = 1 := by
  have hsmall := (unique_iff y).mp hy
  have hlarge : IsUnique L (letters y) := (unique_iff y).mpr (by
    intro a b ha hb hab
    apply hsmall a b (by omega) (by omega)
    intro i hi
    exact hab i (by omega))
  intro g
  have hc := (List.nodup_iff_count_le_one.mp hlarge) (List.ofFn g)
  unfold DeletionHash.MixedEdit.spectrum
  omega

theorem spells {n L : ℕ} (y : Word α n) (hL : 1 ≤ L)
    (hy : IsUnique (L-1) (letters y)) : SpellsSimplePath L (letters y) := by
  refine ⟨hy, ?_, fun g => nonzero_iff_mem L (letters y) g⟩
  intro i hi
  have hiL : i+L ≤ n := by
    simp only [starts, letters, List.length_ofFn, List.mem_range] at hi
    split_ifs at hi <;> omega
  let g : Gram α L := fun j => y ⟨i+j.val, by omega⟩
  refine ⟨g, (window_as_ofFn y hiL).symm, ?_, ?_⟩
  · rw [window_as_ofFn y (show i+(L-1) ≤ n by omega)]
    rfl
  · rw [window_as_ofFn y (show i+1+(L-1) ≤ n by omega)]
    apply congrArg List.ofFn
    funext j
    dsimp [gramSuffix, g]
    congr 1
    apply Fin.ext
    dsimp
    omega

theorem recovers {n L : ℕ} (y z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hy : IsUnique (L-1) (letters y))
    (hs : spectrum L (letters z) = spectrum L (letters y)) : z=y := by
  have hw : ∀ i, i ≤ n-L → WordPaths.Occurs α (OverlapCollision.padBits α y) n
      (OverlapCollision.padBits α z) i L := by
    intro i hi
    have hiL : i+L ≤ n := by omega
    let g : Gram α L := fun j => z ⟨i+j.val, by omega⟩
    have hmem : List.ofFn g ∈ windows L (letters z) :=
      (windows_mem_iff z g).mpr ⟨i, hiL, window_as_ofFn z hiL⟩
    have hz := (nonzero_iff_mem L (letters z) g).mpr hmem
    rw [hs] at hz
    obtain ⟨a, ha, he⟩ := (windows_mem_iff y g).mp ((nonzero_iff_mem L (letters y) g).mp hz)
    rw [window_as_ofFn y ha, List.ofFn_inj] at he
    refine ⟨a, ha, ?_⟩
    intro j hj
    have h := congrFun he (⟨j,hj⟩ : Fin L)
    simpa only [OverlapCollision.padBits, dif_pos (show a+j<n by omega),
      dif_pos (show i+j<n by omega), Option.some.injEq, g] using h
  obtain ⟨a, ha, he⟩ := WordPaths.all_windows_occur_implies_subword α
    (OverlapCollision.padBits α y) (OverlapCollision.padBits α z) n (L-1) L (n-L)
    ((unique_iff y).mp hy) (by omega) hw
  have hl : L+(n-L)=n := by omega
  rw [hl] at ha he
  have ha0 : a=0 := by omega
  subst a
  funext j
  have h := (he j.val j.isLt).symm
  simpa only [OverlapCollision.padBits, Nat.zero_add, dif_pos j.isLt, Option.some.injEq] using h

end DeletionGraph.SpectrumPath
namespace DeletionGraph.WindowTools
open DeletionHash.MixedEdit
universe u
variable {α : Type u}

theorem window_window (x : List α) (a h i k : ℕ) (hi : i+k ≤ h) :
    window k (window h x a) i = window k x (a+i) := by
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop]
    omega
  · intro j hj hk
    simp only [window, List.getElem_take, List.getElem_drop, Nat.add_assoc]

theorem window_take (x : List α) (h i k : ℕ) (hi : i+k ≤ h) :
    window k (x.take h) i = window k x i := by
  simpa only [window, List.drop_zero, Nat.zero_add] using window_window x 0 h i k hi

theorem window_of_append (X P Y : List α) :
    window P.length (X++P++Y) X.length = P := by
  simp [window, List.drop_append]

theorem windows_length (k : ℕ) (x : List α) : (windows k x).length = x.length+1-k := by
  simp only [windows, starts, List.length_map, List.length_range]
  split_ifs <;> omega

theorem windows_get (k : ℕ) (x : List α) (i : ℕ) (hi : i < (windows k x).length) :
    (windows k x)[i] = window k x i := by
  simp [windows, starts, List.getElem_map, List.getElem_range]

theorem unique_positions {k : ℕ} {x : List α} :
    IsUnique k x ↔ ∀ a b, a+k ≤ x.length → b+k ≤ x.length →
      window k x a = window k x b → a=b := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range]
  constructor
  · intro h a b ha hb he
    have hk : k ≤ x.length := by omega
    apply h a (by rw [if_pos hk]; omega) b (by rw [if_pos hk]; omega) he
  · intro h a ha b hb he
    by_cases hk : k ≤ x.length
    · simp only [if_pos hk] at ha hb
      exact h a b (by omega) (by omega) he
    · simp [hk] at ha

theorem unique_subwindow {k : ℕ} {x : List α} (hx : IsUnique k x)
    (a h : ℕ) (ha : a+h ≤ x.length) : IsUnique k (window h x a) := by
  apply unique_positions.mpr
  intro i j hi hj he
  have hlen : (window h x a).length=h := by
    simp only [window, List.length_take, List.length_drop]
    omega
  rw [hlen] at hi hj
  rw [window_window x a h i k hi, window_window x a h j k hj] at he
  have h := unique_positions.mp hx (a+i) (a+j) (by omega) (by omega) he
  omega

theorem spells_list [Fintype α] [DecidableEq α] [Nonempty α]
    (L : ℕ) (x : List α) (hL : 1 ≤ L) (hx : IsUnique (L-1) x) :
    SpellsSimplePath L x := by
  let y : Word α x.length := fun i => x.get i
  have hy : letters y=x := by simp [letters,y]
  have h := SpectrumPath.spells y hL (by rwa [hy])
  simpa only [hy] using h


theorem first_of_window (x P : List α) (a m : ℕ)
    (he : window P.length x a=P) (hm : m ≤ P.length) :
    P.take m=window m x a := by
  have h := window_window x a P.length 0 m (by omega)
  rw [he] at h
  simpa only [window,List.drop_zero,Nat.add_zero] using h

theorem last_of_window (x P : List α) (a m : ℕ)
    (he : window P.length x a=P) (hm : m ≤ P.length) :
    P.drop (P.length-m)=window m x (a+(P.length-m)) := by
  have h := window_window x a P.length (P.length-m) m (by omega)
  rw [he] at h
  have hd : (P.drop (P.length-m)).length=m := by simp only [List.length_drop]; omega
  have ht : (P.drop (P.length-m)).take m=P.drop (P.length-m) := by
    apply List.take_of_length_le
    omega
  simpa only [window,ht] using h


end DeletionGraph.WindowTools
namespace DeletionGraph.BubbleSupport
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem mem_windows (x : List α) (k i : ℕ) (hi : i+k ≤ x.length) :
    window k x i ∈ windows k x := by
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [starts,List.mem_range,if_pos (show k ≤ x.length by omega)]
  omega

theorem occurrence {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (g : Gram α L)
    (hg : List.ofFn g ∈ windows L P) :
    ∃ i, i+L ≤ P.length ∧ List.ofFn g=window L P i ∧
      List.ofFn (gramPrefix g)=window (L-1) P i ∧
      List.ofFn (gramSuffix g)=window (L-1) P (i+1) := by
  obtain ⟨i,hi,hgi⟩ := List.mem_map.mp hg
  obtain ⟨g',hg',hp,hs⟩ := hP.2.1 i hi
  have he : g'=g := List.ofFn_inj.mp (hg'.trans hgi)
  subst g'
  refine ⟨i,?_,hgi.symm,hp,hs⟩
  simp only [starts,List.mem_range] at hi
  split_ifs at hi <;> omega

theorem window_last (P : List α) (m : ℕ) (hm : m ≤ P.length) :
    window m P (P.length-m)=P.drop (P.length-m) := by
  unfold window
  apply List.take_of_length_le
  simp only [List.length_drop]
  omega

theorem prefix_not_last {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    List.ofFn (gramPrefix g) ≠ P.drop (P.length-(L-1)) := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  intro he
  have hm : L-1 ≤ P.length := by omega
  have h := unique_positions.mp hP.1 i (P.length-(L-1)) (by omega) (by omega)
    (hpre.symm.trans (he.trans (window_last P (L-1) hm).symm))
  omega

theorem suffix_not_first {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    List.ofFn (gramSuffix g) ≠ P.take (L-1) := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  intro he
  have h := unique_positions.mp hP.1 (i+1) 0 (by omega) (by omega)
    (by simpa only [window,List.drop_zero] using hsuf.symm.trans he)
  omega

theorem endpoint_mem {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    gramPrefix g ∈ PathVertices L P ∧ gramSuffix g ∈ PathVertices L P := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  constructor
  · change List.ofFn (gramPrefix g) ∈ windows (L-1) P
    rw [hpre]
    exact mem_windows P (L-1) i (by omega)
  · change List.ofFn (gramSuffix g) ∈ windows (L-1) P
    rw [hsuf]
    exact mem_windows P (L-1) (i+1) (by omega)

theorem gram_spans_whole {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P)
    (hp : List.ofFn (gramPrefix g)=P.take (L-1))
    (hs : List.ofFn (gramSuffix g)=P.drop (P.length-(L-1))) :
    List.ofFn g=P := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  have hi0 : i=0 := unique_positions.mp hP.1 i 0 (by omega) (by omega)
    (by simpa only [window,List.drop_zero] using hpre.symm.trans hp)
  have hiend := unique_positions.mp hP.1 (i+1) (P.length-(L-1)) (by omega) (by omega)
    (hsuf.symm.trans (hs.trans (window_last P (L-1) (by omega)).symm))
  have hlen : P.length=L := by omega
  simpa only [hi0,window,List.drop_zero,← hlen,List.take_length] using hg

theorem bubble_words_ne {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q) : P ≠ Q := by
  obtain ⟨A,U,V,B,hP,hQ,hne,_⟩ := hB.1
  intro he
  rw [hP,hQ] at he
  exact hne (by simpa using he)

theorem bubble_grams_disjoint {k L b : ℕ} {P Q : List α}
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) (g : Gram α L) :
    ¬ (List.ofFn g ∈ windows L P ∧ List.ofFn g ∈ windows L Q) := by
  intro ⟨hgP,hgQ⟩
  obtain ⟨hform,hPl,hPu,hQl,hQu,hfirst,hlast,hpathP,hpathQ,hmeet⟩ := hB
  have ep := endpoint_mem P hpathP hL g hgP
  have eq := endpoint_mem Q hpathQ hL g hgQ
  have hp := hmeet (gramPrefix g) ep.1 eq.1
  have hs := hmeet (gramSuffix g) ep.2 eq.2
  have hp' : List.ofFn (gramPrefix g)=P.take (L-1) :=
    hp.resolve_right (prefix_not_last P hpathP hL g hgP)
  have hs' : List.ofFn (gramSuffix g)=P.drop (P.length-(L-1)) :=
    hs.resolve_left (suffix_not_first P hpathP hL g hgP)
  have hP := gram_spans_whole P hpathP hL g hgP hp' hs'
  have hQ := gram_spans_whole Q hpathQ hL g hgQ (hp'.trans hfirst) (hs'.trans hlast)
  apply bubble_words_ne ⟨hform,hPl,hPu,hQl,hQu,hfirst,hlast,hpathP,hpathQ,hmeet⟩
  exact hP.symm.trans hQ

theorem spectrum_boolean {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) :
    ∀ g, spectrum L P g=0 ∨ spectrum L P g=1 := by
  have hlarge : IsUnique L P := unique_positions.mpr (by
    intro i j hi hj he
    apply unique_positions.mp hP.1 i j (by omega) (by omega)
    have h := congrArg (List.take (L-1)) he
    simpa only [window,List.take_take,Nat.min_eq_left (show L-1 ≤ L by omega)] using h)
  intro g
  have h := List.nodup_iff_count_le_one.mp hlarge (List.ofFn g)
  unfold DeletionHash.MixedEdit.spectrum
  omega


theorem nonzero_iff_mem (L : ℕ) (P : List α) (g : Gram α L) :
    spectrum L P g ≠ 0 ↔ List.ofFn g ∈ windows L P := by
  simp [DeletionHash.MixedEdit.spectrum,List.count_eq_zero]

theorem difference_support {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) :
    (spectrum L Q-spectrum L P) g ≠ 0 ↔
      List.ofFn g ∈ windows L P ∨ List.ofFn g ∈ windows L Q := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  have hp := spectrum_boolean P hP g
  have hq := spectrum_boolean Q hQ g
  have hn := bubble_grams_disjoint hB hL g
  rw [← nonzero_iff_mem L P g,← nonzero_iff_mem L Q g] at hn ⊢
  change (spectrum L Q g-spectrum L P g ≠ 0) ↔ _
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all

theorem difference_values {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (g : Gram α L) :
    (spectrum L Q-spectrum L P) g=0 ∨
      (spectrum L Q-spectrum L P) g=1 ∨ (spectrum L Q-spectrum L P) g= -1 := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  have hp := spectrum_boolean P hP g
  have hq := spectrum_boolean Q hQ g
  change spectrum L Q g-spectrum L P g=0 ∨
    spectrum L Q g-spectrum L P g=1 ∨ spectrum L Q g-spectrum L P g= -1
  omega

theorem difference_endpoint {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) (hg : (spectrum L Q-spectrum L P) g ≠ 0) :
    gramPrefix g ∈ bubbleVertices L P Q ∧ gramSuffix g ∈ bubbleVertices L P Q := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  rcases (difference_support hB hL g).mp hg with hg | hg
  · have he := endpoint_mem P hP hL g hg
    exact ⟨Or.inl he.1,Or.inl he.2⟩
  · have he := endpoint_mem Q hQ hL g hg
    exact ⟨Or.inr he.1,Or.inr he.2⟩


end DeletionGraph.BubbleSupport
namespace DeletionGraph.CatalogueSupport
open DeletionHash.MixedEdit BubbleSupport
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem distinct_piece_zero {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (i j : ι) (hij : i ≠ j) (g : Gram α L)
    (hi : (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    (spectrum L (B j).2-spectrum L (B j).1) g = 0 := by
  by_contra hj
  have hp := (difference_endpoint (hB i) hL g hi).1
  have hq := (difference_endpoint (hB j) hL g hj).1
  exact Set.disjoint_left.mp (hdis i j hij) hp hq

theorem sum_piece_eq {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (i : ι) (g : Gram α L)
    (hi : (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    (∑ j, (spectrum L (B j).2-spectrum L (B j).1)) g =
      (spectrum L (B i).2-spectrum L (B i).1) g := by
  rw [Finset.sum_apply]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact distinct_piece_zero B hB hdis hL i j hji.symm g hi
  · simp

theorem sum_support {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (g : Gram α L) :
    (∑ j, (spectrum L (B j).2-spectrum L (B j).1)) g ≠ 0 ↔
      ∃ j, (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => hn i)
  · rintro ⟨i,hi⟩
    rwa [sum_piece_eq B hB hdis hL i g hi]

theorem catalogue_values {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (g : Gram α L) :
    w g=0 ∨ w g=1 ∨ w g= -1 := by
  obtain ⟨B,hB,hdis,rfl⟩ := hw
  by_cases hn : ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0
  · obtain ⟨i,hi⟩ := hn
    rw [sum_piece_eq B hB hdis hL i g hi]
    exact difference_values (hB i) g
  · left
    push_neg at hn
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => hn i)

theorem parity_zero_iff {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (g : Gram α L) :
    parity w g=0 ↔ w g=0 := by
  rcases catalogue_values w hw hL g with h | h | h <;> simp [parity,h]

theorem relation_support_subset {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (I : Finset (Spectrum α L))
    (hrel : parity w=∑ z ∈ I, parity z) :
    supportUnion {w} ⊆ supportUnion I := by
  intro g hg
  obtain ⟨v,hv,hvg⟩ := hg
  have hvw : v=w := Finset.mem_singleton.mp hv
  subst v
  by_contra hnone
  have hz : ∀ z ∈ I, z g=0 := by
    intro z hz
    by_contra hzg
    exact hnone ⟨z,hz,hzg⟩
  have hp : parity w g ≠ 0 := by
    intro hp
    exact hvg ((parity_zero_iff w hw hL g).mp hp)
  apply hp
  have hc := congrFun hrel g
  simp only [Finset.sum_apply] at hc
  rw [hc]
  apply Finset.sum_eq_zero
  intro z hzi
  simp [parity,hz z hzi]

end DeletionGraph.CatalogueSupport
namespace DeletionGraph.SupportPaths
open DeletionHash.MixedEdit BubbleSupport WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem mem_starts (P : List α) (L i : ℕ) (hi : i+L ≤ P.length) : i ∈ starts L P := by
  simp only [starts,List.mem_range,if_pos (show L ≤ P.length by omega)]
  omega

theorem vertices_incident {L : ℕ} (F : Finset (Spectrum α L)) (P : List α)
    (hP : SpellsSimplePath L P) (hL : 1 ≤ L) (hlen : L ≤ P.length)
    (hedges : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F)
    (v : Gram α (L-1)) (hv : v ∈ PathVertices L P) : v ∈ incidentVertices F := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
  have him : i+(L-1) ≤ P.length := by
    simp only [starts,List.mem_range,if_pos (show L-1 ≤ P.length by omega)] at hi
    omega
  by_cases hil : i+L ≤ P.length
  · obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 i (mem_starts P L i hil)
    refine ⟨g,hedges g (by rw [hg]; exact mem_windows P L i hil),Or.inl ?_⟩
    exact List.ofFn_inj.mp (he.symm.trans hpre.symm)
  · have hipos : 1 ≤ i := by omega
    have hib : i-1+L ≤ P.length := by omega
    obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 (i-1) (mem_starts P L (i-1) hib)
    have hidx : i-1+1=i := by omega
    rw [hidx] at hsuf
    refine ⟨g,hedges g (by rw [hg]; exact mem_windows P L (i-1) hib),Or.inr ?_⟩
    exact List.ofFn_inj.mp (he.symm.trans hsuf.symm)

theorem edge_reachable {L : ℕ} (F : Finset (Spectrum α L))
    (v w : {v : Gram α (L-1) // v ∈ incidentVertices F}) (g : Gram α L)
    (hg : g ∈ supportUnion F) (hv : v.val=gramPrefix g) (hw : w.val=gramSuffix g) :
    (supportGraph F).Reachable v w := by
  classical
  by_cases he : v=w
  · subst w
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact ⟨he,g,hg,Or.inl ⟨hv,hw⟩⟩

def gramAt (P : List α) (i k : ℕ) (hi : i+k ≤ P.length) : Gram α k :=
  fun j => P[i+j.val]'(by omega)

theorem ofFn_gramAt (P : List α) (i k : ℕ) (hi : i+k ≤ P.length) :
    List.ofFn (gramAt P i k hi)=window k P i := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,window,List.length_take,List.length_drop]
    omega
  · intro j hj hk
    simp only [List.getElem_ofFn,gramAt,window,List.getElem_take,List.getElem_drop]


theorem path_connected {L : ℕ} (F : Finset (Spectrum α L)) (P : List α)
    (hP : SpellsSimplePath L P) (hL : 1 ≤ L) (hlen : L ≤ P.length)
    (hedges : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F)
    (v w : {v : Gram α (L-1) // v ∈ incidentVertices F})
    (hv : v.val ∈ PathVertices L P) (hw : w.val ∈ PathVertices L P) :
    (supportGraph F).Reachable v w := by
  let m := L-1
  let N := P.length-m+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  let V : Fin N → {v : Gram α (L-1) // v ∈ incidentVertices F} := fun q =>
    ⟨gramAt P q.val m (by have h := q.isLt; dsimp [N] at h; omega),
      vertices_incident F P hP hL hlen hedges _ (by
        change List.ofFn (gramAt P q.val m (by have h := q.isLt; dsimp [N] at h; omega)) ∈ windows m P
        rw [ofFn_gramAt]
        exact mem_windows P m q.val (by have h := q.isLt; dsimp [N] at h; omega))⟩
  have hstep : ∀ q (hq : q+1<N),
      (supportGraph F).Reachable (V ⟨q,by omega⟩) (V ⟨q+1,hq⟩) := by
    intro q hq
    have hqL : q+L ≤ P.length := by dsimp [N,m] at hq; omega
    obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 q (mem_starts P L q hqL)
    apply edge_reachable F _ _ g (hedges g (by rw [hg]; exact mem_windows P L q hqL))
    · apply List.ofFn_inj.mp
      change List.ofFn (gramAt P q m (by dsimp [m]; omega)) = List.ofFn (gramPrefix g)
      rw [ofFn_gramAt]
      exact hpre.symm
    · apply List.ofFn_inj.mp
      change List.ofFn (gramAt P (q+1) m (by dsimp [m]; omega)) = List.ofFn (gramSuffix g)
      rw [ofFn_gramAt]
      exact hsuf.symm
  have hreach : ∀ q (hq : q<N),
      (supportGraph F).Reachable (V ⟨0,by omega⟩) (V ⟨q,hq⟩) := by
    intro q
    induction q with
    | zero =>
      intro hq
      exact SimpleGraph.Reachable.refl _
    | succ q ih =>
      intro hq
      exact (ih (by omega)).trans (hstep q hq)
  have hcover : ∀ z : {v : Gram α (L-1) // v ∈ incidentVertices F},
      z.val ∈ PathVertices L P → ∃ q, V q=z := by
    intro z hz
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hz
    have hib : i+m ≤ P.length := by
      simp only [starts,List.mem_range,if_pos (show L-1 ≤ P.length by omega)] at hi
      dsimp [m]
      omega
    refine ⟨⟨i,by dsimp [N]; omega⟩,Subtype.ext ?_⟩
    apply List.ofFn_inj.mp
    change List.ofFn (gramAt P i m hib)=List.ofFn z.val
    rw [ofFn_gramAt]
    exact he
  obtain ⟨i,hi⟩ := hcover v hv
  obtain ⟨j,hj⟩ := hcover w hw
  rw [← hi,← hj]
  exact (hreach i.val i.isLt).symm.trans (hreach j.val j.isLt)


end DeletionGraph.SupportPaths
namespace DeletionGraph.BubbleConnectivity
open DeletionHash.MixedEdit BubbleSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem bubble_connected {k L b : ℕ} (F : Finset (Spectrum α L)) (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L)
    (hsupport : ∀ g, (spectrum L Q-spectrum L P) g ≠ 0 → g ∈ supportUnion F) :
    ∃ r : {v : Gram α (L-1) // v ∈ incidentVertices F},
      r.val ∈ bubbleVertices L P Q ∧
      ∀ v : {v : Gram α (L-1) // v ∈ incidentVertices F},
        v.val ∈ bubbleVertices L P Q → (supportGraph F).Reachable r v := by
  have hcopy := hB
  obtain ⟨_,hPl,_,hQl,_,hfirst,_,hpathP,hpathQ,_⟩ := hcopy
  have hedgesP : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F := by
    intro g hg
    exact hsupport g ((difference_support hB hL g).mpr (Or.inl hg))
  have hedgesQ : ∀ g, List.ofFn g ∈ windows L Q → g ∈ supportUnion F := by
    intro g hg
    exact hsupport g ((difference_support hB hL g).mpr (Or.inr hg))
  let v0 := gramAt P 0 (L-1) (by omega)
  have hvP : v0 ∈ PathVertices L P := by
    change List.ofFn v0 ∈ windows (L-1) P
    rw [ofFn_gramAt]
    exact mem_windows P (L-1) 0 (by omega)
  have hvQ : v0 ∈ PathVertices L Q := by
    change List.ofFn v0 ∈ windows (L-1) Q
    have h : List.ofFn v0=Q.take (L-1) := by
      rw [ofFn_gramAt]
      simpa only [window,List.drop_zero] using hfirst
    rw [h]
    simpa only [window,List.drop_zero] using mem_windows Q (L-1) 0 (by omega)
  let r : {v : Gram α (L-1) // v ∈ incidentVertices F} :=
    ⟨v0,vertices_incident F P hpathP hL hPl hedgesP v0 hvP⟩
  refine ⟨r,Or.inl hvP,?_⟩
  intro v hv
  rcases hv with hv | hv
  · exact path_connected F P hpathP hL hPl hedgesP r v hvP hv
  · exact path_connected F Q hpathQ hL hQl hedgesQ r v hvQ hv

theorem bubble_nonzero {k L b : ℕ} (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    ∃ g, (spectrum L Q-spectrum L P) g ≠ 0 := by
  have hPl : L ≤ P.length := hB.2.1
  let g := gramAt P 0 L (by omega)
  refine ⟨g,(difference_support hB hL g).mpr (Or.inl ?_)⟩
  rw [ofFn_gramAt]
  exact mem_windows P L 0 (by omega)

theorem bubble_vertices_eq {k L b : ℕ} (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    bubbleVertices L P Q=incidentVertices {spectrum L Q-spectrum L P} := by
  ext v
  constructor
  · intro hv
    have hcopy := hB
    obtain ⟨_,hPl,_,hQl,_,_,_,hP,hQ,_⟩ := hcopy
    rcases hv with hv | hv
    · apply vertices_incident _ P hP hL hPl _ v hv
      intro g hg
      exact ⟨_,Finset.mem_singleton_self _,(difference_support hB hL g).mpr (Or.inl hg)⟩
    · apply vertices_incident _ Q hQ hL hQl _ v hv
      intro g hg
      exact ⟨_,Finset.mem_singleton_self _,(difference_support hB hL g).mpr (Or.inr hg)⟩
  · rintro ⟨g,⟨z,hz,hg⟩,hv⟩
    have he : z=spectrum L Q-spectrum L P := Finset.mem_singleton.mp hz
    subst z
    have hends := difference_endpoint hB hL g hg
    rcases hv with rfl | rfl
    · exact hends.1
    · exact hends.2

end DeletionGraph.BubbleConnectivity
namespace DeletionGraph.ComponentCover
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity CatalogueSupport
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {ι : Type v} [Fintype ι]

theorem cover_by_bubbles {k L b : ℕ} (F : Finset (Spectrum α L))
    (B : ι → List α × List α) (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    ∃ r : ι → {v : Gram α (L-1) // v ∈ incidentVertices F},
      (∀ i, (r i).val ∈ bubbleVertices L (B i).1 (B i).2) ∧
      (∀ i (v : {v : Gram α (L-1) // v ∈ incidentVertices F}),
        v.val ∈ bubbleVertices L (B i).1 (B i).2 → (supportGraph F).Reachable (r i) v) ∧
      Function.Surjective (fun i => (supportGraph F).connectedComponentMk (r i)) := by
  classical
  choose r hr hreach using fun i => bubble_connected F (B i).1 (B i).2 (hB i) hL (hsupport i)
  refine ⟨r,hr,hreach,?_⟩
  intro C
  refine SimpleGraph.ConnectedComponent.ind ?_ C
  intro v
  obtain ⟨g,hg,hv⟩ := v.property
  obtain ⟨i,hi⟩ := hcover g hg
  have he := difference_endpoint (hB i) hL g hi
  have hvmem : v.val ∈ bubbleVertices L (B i).1 (B i).2 := by
    rcases hv with hv | hv
    · rw [hv]
      exact he.1
    · rw [hv]
      exact he.2
  exact ⟨i,SimpleGraph.ConnectedComponent.sound (hreach i v hvmem)⟩

theorem count_le_bubbles {k L b : ℕ} (F : Finset (Spectrum α L))
    (B : ι → List α × List α) (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    componentCount F ≤ Fintype.card ι := by
  classical
  obtain ⟨r,hr,hreach,hsurj⟩ := cover_by_bubbles F B hB hL hsupport hcover
  have h := Nat.card_le_card_of_surjective _ hsurj
  simpa only [componentCount,Nat.card_eq_fintype_card] using h

theorem catalogue_count_le {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) :
    componentCount {w} ≤ 2*t := by
  classical
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 →
      g ∈ supportUnion {w} := by
    intro i g hg
    refine ⟨w,Finset.mem_singleton_self _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  have hcover : ∀ g ∈ supportUnion {w},
      ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 := by
    rintro g ⟨z,hz,hg⟩
    have hz : z=w := Finset.mem_singleton.mp hz
    subst z
    rw [heq] at hg
    exact (sum_support B hB hdis hL g).mp hg
  simpa only [Fintype.card_fin] using count_le_bubbles {w} B hB hL hsupport hcover

end DeletionGraph.ComponentCover
namespace DeletionGraph.ComponentInsert
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity CatalogueSupport
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem support_mono {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    supportUnion F ⊆ supportUnion H := by
  rintro g ⟨w,hw,hg⟩
  exact ⟨w,h hw,hg⟩

theorem incident_mono {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    incidentVertices F ⊆ incidentVertices H := by
  rintro v ⟨g,hg,hv⟩
  exact ⟨g,support_mono h hg,hv⟩

def inclusion {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    supportGraph F →g supportGraph H where
  toFun v := ⟨v.val,incident_mono h v.property⟩
  map_rel' := by
    rintro v z ⟨hne,g,hg,he⟩
    refine ⟨?_,g,support_mono h hg,he⟩
    intro hvz
    exact hne (Subtype.ext (congrArg (fun x : {v : Gram α (L-1) // v ∈ incidentVertices H} => x.val) hvz))

theorem insert_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (F : Finset (Spectrum α L)) (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hadj : ∃ z ∈ F, RuleAdjacent w z) :
    componentCount (insert w F) ≤ componentCount F+(2*t-1) := by
  classical
  let H := insert w F
  have hsub : F ⊆ H := Finset.subset_insert _ _
  let φ := inclusion hsub
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hs : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion H := by
    intro i g hg
    refine ⟨w,Finset.mem_insert_self _ _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  choose r hr hreach using fun i => bubble_connected H (B i).1 (B i).2 (hB i) hL (hs i)
  let f : (supportGraph F).ConnectedComponent ⊕ Fin (2*t) → (supportGraph H).ConnectedComponent :=
    Sum.elim (fun C => C.map φ) (fun i => (supportGraph H).connectedComponentMk (r i))
  have hsurj : Function.Surjective f := by
    intro C
    refine SimpleGraph.ConnectedComponent.ind ?_ C
    intro v
    obtain ⟨g,⟨z,hz,hg⟩,hv⟩ := v.property
    rcases Finset.mem_insert.mp hz with hzw | hz
    · subst z
      rw [heq] at hg
      obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
      have he := difference_endpoint (hB i) hL g hi
      have hvmem : v.val ∈ bubbleVertices L (B i).1 (B i).2 := by
        rcases hv with hv | hv
        · rw [hv]; exact he.1
        · rw [hv]; exact he.2
      exact ⟨Sum.inr i,SimpleGraph.ConnectedComponent.sound (hreach i v hvmem)⟩
    · let vF : {v : Gram α (L-1) // v ∈ incidentVertices F} := ⟨v.val,⟨g,⟨z,hz,hg⟩,hv⟩⟩
      refine ⟨Sum.inl ((supportGraph F).connectedComponentMk vF),?_⟩
      rfl
  have hnot : ¬Function.Injective f := by
    obtain ⟨z,hz,v,hvw,hvz⟩ := hadj
    have hvF : v ∈ incidentVertices F :=
      incident_mono (Finset.singleton_subset_iff.mpr hz) hvz
    let vF : {v : Gram α (L-1) // v ∈ incidentVertices F} := ⟨v,hvF⟩
    obtain ⟨g,⟨z',hz',hg⟩,hv⟩ := hvw
    have hz' : z'=w := Finset.mem_singleton.mp hz'
    subst z'
    rw [heq] at hg
    obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
    have he := difference_endpoint (hB i) hL g hi
    have hvmem : (φ vF).val ∈ bubbleVertices L (B i).1 (B i).2 := by
      change v ∈ bubbleVertices L (B i).1 (B i).2
      rcases hv with hv | hv
      · rw [hv]; exact he.1
      · rw [hv]; exact he.2
    have heqC : f (Sum.inr i)=f (Sum.inl ((supportGraph F).connectedComponentMk vF)) :=
      SimpleGraph.ConnectedComponent.sound (hreach i (φ vF) hvmem)
    intro hinj
    have h := hinj heqC
    cases h
  letI : Fintype (supportGraph F).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype (supportGraph H).ConnectedComponent := Fintype.ofFinite _
  have hc := Fintype.card_lt_of_surjective_not_injective f hsurj hnot
  simp only [Fintype.card_sum,Fintype.card_fin] at hc
  have heF : Fintype.card (supportGraph F).ConnectedComponent=componentCount F := by
    simp [componentCount,Nat.card_eq_fintype_card]
  have heH : Fintype.card (supportGraph H).ConnectedComponent=componentCount (insert w F) := by
    simp [H,componentCount,Nat.card_eq_fintype_card]
  rw [heF,heH] at hc
  omega

end DeletionGraph.ComponentInsert
namespace DeletionGraph.BubbleVertexCount
open DeletionHash.MixedEdit WindowTools SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem path_card (L : ℕ) (P : List α) :
    (PathVertices L P).ncard ≤ P.length+1-(L-1) := by
  classical
  let T := (windows (L-1) P).toFinset
  have hc : (PathVertices L P).ncard ≤ (T : Set (List α)).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun v : Gram α (L-1) => List.ofFn v)
    · intro v hv
      exact List.mem_toFinset.mpr hv
    · intro v hv w hw he
      exact List.ofFn_injective he
  have ht : (T : Set (List α)).ncard ≤ (windows (L-1) P).length := by
    simpa only [Finset.coe_sort_coe,Set.ncard_coe_finset] using List.toFinset_card_le (windows (L-1) P)
  exact hc.trans (by simpa only [windows_length] using ht)

theorem two_common {k L b : ℕ} (P Q : List α) (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    2 ≤ (PathVertices L P ∩ PathVertices L Q).ncard := by
  have hPl : L ≤ P.length := hB.2.1
  have hQl : L ≤ Q.length := hB.2.2.2.1
  have hfirst := hB.2.2.2.2.2.1
  have hlast := hB.2.2.2.2.2.2.1
  have hu := hB.2.2.2.2.2.2.2.1.1
  let v0 := gramAt P 0 (L-1) (by omega)
  let v1 := gramAt P (P.length-(L-1)) (L-1) (by omega)
  have hv0 : v0 ∈ PathVertices L P ∩ PathVertices L Q := by
    constructor
    · change List.ofFn v0 ∈ windows (L-1) P
      rw [ofFn_gramAt]
      exact BubbleSupport.mem_windows P (L-1) 0 (by omega)
    · change List.ofFn v0 ∈ windows (L-1) Q
      rw [ofFn_gramAt]
      have he : window (L-1) P 0=window (L-1) Q 0 := by
        simpa only [window,List.drop_zero] using hfirst
      rw [he]
      exact BubbleSupport.mem_windows Q (L-1) 0 (by omega)
  have hv1 : v1 ∈ PathVertices L P ∩ PathVertices L Q := by
    have heP : window (L-1) P (P.length-(L-1))=P.drop (P.length-(L-1)) := by
      unfold window
      apply List.take_of_length_le
      simp only [List.length_drop];omega
    have heQ : window (L-1) Q (Q.length-(L-1))=Q.drop (Q.length-(L-1)) := by
      unfold window
      apply List.take_of_length_le
      simp only [List.length_drop];omega
    constructor
    · change List.ofFn v1 ∈ windows (L-1) P
      rw [ofFn_gramAt]
      exact BubbleSupport.mem_windows P (L-1) _ (by omega)
    · change List.ofFn v1 ∈ windows (L-1) Q
      rw [ofFn_gramAt,heP,hlast,←heQ]
      exact BubbleSupport.mem_windows Q (L-1) _ (by omega)
  have hne : v0 ≠ v1 := by
    intro he
    have hg := congrArg (fun v : Gram α (L-1) => List.ofFn v) he
    simp only [v0,v1,ofFn_gramAt] at hg
    have hi := unique_positions.mp hu 0 (P.length-(L-1)) (by omega) (by omega) hg
    omega
  have hs : ({v0,v1} : Set (Gram α (L-1))) ⊆ PathVertices L P ∩ PathVertices L Q := by
    intro v hv
    rcases hv with rfl | hv
    · exact hv0
    · have he : v=v1 := hv
      subst v
      exact hv1
  have hc := Set.ncard_le_ncard hs
  simpa only [Set.ncard_pair hne] using hc

theorem bubble_card {k L b : ℕ} (P Q : List α) (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    (bubbleVertices L P Q).ncard ≤ 2*L+2*b-2 := by
  have hp := path_card L P
  have hq := path_card L Q
  have htwo := two_common P Q hB hL
  have he := Set.ncard_union_add_ncard_inter (PathVertices L P) (PathVertices L Q)
  have hPu := hB.2.2.1
  have hQu := hB.2.2.2.2.1
  change (PathVertices L P ∪ PathVertices L Q).ncard ≤ _
  omega

end DeletionGraph.BubbleVertexCount
namespace DeletionGraph.CatalogueVertexCount
open DeletionHash.MixedEdit BubbleSupport CatalogueSupport BubbleVertexCount
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem vertices_le {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) :
    (incidentVertices {w}).ncard ≤ 2*t*(2*L+2*b-2) := by
  classical
  obtain ⟨B,hB,hdis,heq⟩ := hw
  let S : Fin (2*t) → Finset (Gram α (L-1)) :=
    fun i => (bubbleVertices L (B i).1 (B i).2).toFinite.toFinset
  let T := Finset.univ.biUnion S
  have hsub : incidentVertices {w} ⊆ (T : Set (Gram α (L-1))) := by
    rintro v ⟨g,⟨z,hz,hg⟩,hv⟩
    have hz : z=w := Finset.mem_singleton.mp hz
    subst z
    rw [heq] at hg
    obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
    have ends := difference_endpoint (hB i) hL g hi
    have hvm : v ∈ bubbleVertices L (B i).1 (B i).2 := by
      rcases hv with rfl | rfl
      · exact ends.1
      · exact ends.2
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ _,by simpa [S] using hvm⟩
  have hcard : (incidentVertices {w}).ncard ≤ T.card := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub
  calc
    _ ≤ T.card := hcard
    _ ≤ ∑ i : Fin (2*t), (S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin (2*t), (2*L+2*b-2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hc := bubble_card (B i).1 (B i).2 (hB i) hL
      rw [Set.ncard_eq_toFinset_card] at hc
      exact hc
    _ = 2*t*(2*L+2*b-2) := by simp

end DeletionGraph.CatalogueVertexCount
namespace DeletionGraph.ConnectedBlocks
open DeletionHash.MixedEdit ComponentInsert ComponentCover
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem reachable_mem {V : Type v} (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S)
    {v w : V} (hv : v ∈ S) (h : G.Reachable v w) : w ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hv
  | cons he p ih => exact ih (hclosed _ hv _ he)


end DeletionGraph.ConnectedBlocks
namespace DeletionGraph.WitnessBlocks
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

abbrev Incident {L : ℕ} (F : Finset (Spectrum α L)) (v : Gram α (L-1)) : Prop :=
  v ∈ incidentVertices F

theorem adjacent_symm {L : ℕ} {w z : Spectrum α L} (h : RuleAdjacent w z) : RuleAdjacent z w := by
  obtain ⟨v,hv,hz⟩ := h
  exact ⟨v,hz,hv⟩

def ConnectedIn {L : ℕ} (U : Finset (Spectrum α L))
    (a b : Spectrum α L) : Prop :=
  Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) a b

/-- The entire old block of one rule, with every adjacency restricted to U. -/
noncomputable def blockOf {L : ℕ} (U : Finset (Spectrum α L))
    (a : Spectrum α L) : Finset (Spectrum α L) := by
  classical
  exact U.filter (fun b => ConnectedIn U a b)

/-- The actual finite collection of old rule blocks. -/
noncomputable def blocks {L : ℕ} (U : Finset (Spectrum α L)) : Finset (Finset (Spectrum α L)) := by
  classical
  exact U.image (blockOf U)

@[simp] theorem mem_blockOf {L : ℕ} (U : Finset (Spectrum α L))
    (a b : Spectrum α L) :
    b ∈ blockOf U a ↔ b ∈ U ∧ ConnectedIn U a b := by
  classical
  simp [blockOf]

@[simp] theorem mem_blocks {L : ℕ} (U B : Finset (Spectrum α L)) :
    B ∈ blocks U ↔ ∃ a ∈ U, blockOf U a = B := by
  classical
  simp [blocks]

theorem blockOf_nonempty {L : ℕ} (U : Finset (Spectrum α L))
    (a : Spectrum α L) (ha : a ∈ U) : (blockOf U a).Nonempty := by
  refine ⟨a, (mem_blockOf U a a).mpr ⟨ha, ?_⟩⟩
  exact Relation.EqvGen.refl _

theorem blockOf_eq_of_connected {L : ℕ} (U : Finset (Spectrum α L))
    (a b : Spectrum α L) (hab : ConnectedIn U a b) :
    blockOf U a = blockOf U b := by
  classical
  ext c
  simp only [mem_blockOf]
  constructor
  · rintro ⟨hc, hac⟩
    exact ⟨hc, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hac⟩
  · rintro ⟨hc, hbc⟩
    exact ⟨hc, Relation.EqvGen.trans _ _ _ hab hbc⟩

/-- Every incident vertex of a support union belongs to an actual rule in it. -/
theorem incident_iff_rule {L : ℕ} (U : Finset (Spectrum α L))
    (v : Gram α (L-1)) :
    Incident U v ↔ ∃ w ∈ U, Incident {w} v := by
  constructor
  · rintro ⟨g,⟨w,hw,hg⟩,hv⟩
    exact ⟨w,hw,g,⟨w,Finset.mem_singleton_self _,hg⟩,hv⟩
  · rintro ⟨w,hw,hv⟩
    exact ComponentInsert.incident_mono (Finset.singleton_subset_iff.mpr hw) hv

/-- Sharing even one actual support vertex would merge two old rule blocks. -/
theorem blocks_support_disjoint {L : ℕ} (U : Finset (Spectrum α L)) :
    ∀ B ∈ blocks U, ∀ C ∈ blocks U, B ≠ C →
      ∀ v, Incident B v → ¬ Incident C v := by
  intro B hB C hC hne v hvB hvC
  obtain ⟨a, ha, rfl⟩ := (mem_blocks U B).mp hB
  obtain ⟨d, hd, rfl⟩ := (mem_blocks U C).mp hC
  obtain ⟨b, hb, hvb⟩ := (incident_iff_rule (blockOf U a) v).mp hvB
  obtain ⟨c, hc, hvc⟩ := (incident_iff_rule (blockOf U d) v).mp hvC
  obtain ⟨hbU, hab⟩ := (mem_blockOf U a b).mp hb
  obtain ⟨hcU, hdc⟩ := (mem_blockOf U d c).mp hc
  have hbc : ConnectedIn U b c :=
    Relation.EqvGen.rel _ _ ⟨hbU, hcU, v, hvb, hvc⟩
  have had : ConnectedIn U a d := Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.trans _ _ _ hab hbc) (Relation.EqvGen.symm _ _ hdc)
  exact hne (blockOf_eq_of_connected U a d had)

/-- Old blocks actually touching the newly adjoined rule. -/
noncomputable def attachedBlocks {L : ℕ} (U : Finset (Spectrum α L))
    (w : Spectrum α L) : Finset (Finset (Spectrum α L)) := by
  classical
  exact (blocks U).filter (fun B => ∃ v, Incident B v ∧ Incident {w} v)

@[simp] theorem mem_attachedBlocks {L : ℕ} (U B : Finset (Spectrum α L))
    (w : Spectrum α L) :
    B ∈ attachedBlocks U w ↔
      B ∈ blocks U ∧ ∃ v, Incident B v ∧ Incident {w} v := by
  classical
  simp [attachedBlocks]

theorem attached_count {L : ℕ} (U : Finset (Spectrum α L)) (w : Spectrum α L) :
    (attachedBlocks U w).card ≤ (incidentVertices {w}).ncard := by
  classical
  let A := attachedBlocks U w
  have hex : ∀ B : {B : Finset (Spectrum α L) // B ∈ A},
      ∃ v, Incident B.val v ∧ Incident {w} v := by
    intro B
    exact ((mem_attachedBlocks U B.val w).mp B.property).2
  choose v hv hW using hex
  let f : {B : Finset (Spectrum α L) // B ∈ A} → {v : Gram α (L-1) // Incident {w} v} :=
    fun B => ⟨v B,hW B⟩
  have hinj : Function.Injective f := by
    intro B C he
    apply Subtype.ext
    by_contra hne
    have hbc : v B=v C := congrArg Subtype.val he
    exact blocks_support_disjoint U B.val ((mem_attachedBlocks U B.val w).mp B.property).1
      C.val ((mem_attachedBlocks U C.val w).mp C.property).1 hne (v B) (hv B)
      (hbc.symm ▸ hv C)
  have hc := Nat.card_le_card_of_injective f hinj
  calc
    (attachedBlocks U w).card = Nat.card {B : Finset (Spectrum α L) // B ∈ A} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_coe,A]
    _ ≤ Nat.card {v : Gram α (L-1) // Incident {w} v} := hc
    _ = (incidentVertices {w}).ncard := rfl

theorem attached_union_bound {k L t b : ℕ} (U : Finset (Spectrum α L))
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L)
    (hsize : ∀ B ∈ blocks U, B.card ≤ L) :
    (insert w ((attachedBlocks U w).biUnion id)).card ≤ 1+2*t*(2*L+2*b-2)*L := by
  classical
  have hc := (attached_count U w).trans (CatalogueVertexCount.vertices_le w hw hL)
  have hsum : ∑ B ∈ attachedBlocks U w, B.card ≤ (attachedBlocks U w).card*L := by
    calc
      _ ≤ ∑ _B ∈ attachedBlocks U w, L := by
        apply Finset.sum_le_sum
        intro B hB
        exact hsize B ((mem_attachedBlocks U B w).mp hB).1
      _ = _ := by simp
  have hcu : ((attachedBlocks U w).biUnion id).card ≤ ∑ B ∈ attachedBlocks U w, B.card :=
    Finset.card_biUnion_le
  have hins := Finset.card_insert_le w ((attachedBlocks U w).biUnion id)
  have hm := Nat.mul_le_mul_right L hc
  omega

def Connected {L : ℕ} (U : Finset (Spectrum α L)) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, ConnectedIn U a b

theorem connected_mem {L : ℕ} (U : Finset (Spectrum α L)) {a b : Spectrum α L}
    (h : ConnectedIn U a b) : a ∈ U ↔ b ∈ U := by
  induction h with
  | rel a b h => exact ⟨fun _ => h.2.1,fun _ => h.1⟩
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem connected_reachable {L : ℕ} (U : Finset (Spectrum α L)) {a b : Spectrum α L}
    (h : ConnectedIn U a b) :
    ∀ (ha : a ∈ U) (hb : b ∈ U), (ruleGraph U).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
  induction h with
  | rel a b h =>
    intro ha hb
    by_cases he : a=b
    · subst b;exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      exact ⟨fun h' => he (congrArg Subtype.val h'),h.2.2⟩
  | refl a => intro ha hb;exact SimpleGraph.Reachable.refl _
  | symm a b h ih => intro ha hb;exact (ih hb ha).symm
  | trans a b c h1 h2 ih1 ih2 =>
    intro ha hc
    have hb := (connected_mem U h1).mp ha
    exact (ih1 ha hb).trans (ih2 hb hc)

theorem connected_rules {L : ℕ} (U : Finset (Spectrum α L)) (hne : U.Nonempty)
    (hc : Connected U) : ConnectedRules U :=
  ⟨hne,fun a b => connected_reachable U (hc a.val a.property b.val b.property) a.property b.property⟩

end DeletionGraph.WitnessBlocks
namespace DeletionGraph.WitnessSupport
open DeletionHash.MixedEdit WitnessBlocks BubbleSupport BubbleConnectivity CatalogueSupport
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem incident_closed {L : ℕ} (G : Finset (Spectrum α L)) (a : Spectrum α L)
    (v z : {v : Gram α (L-1) // v ∈ incidentVertices G})
    (hv : Incident (blockOf G a) v.val) (hadj : (supportGraph G).Adj v z) :
    Incident (blockOf G a) z.val := by
  obtain ⟨u,hu,hvu⟩ := (incident_iff_rule (blockOf G a) v.val).mp hv
  obtain ⟨huG,hau⟩ := (mem_blockOf G a u).mp hu
  obtain ⟨hne,g,⟨w,hw,hg⟩,hends⟩ := hadj
  have hvw : Incident {w} v.val := by
    refine ⟨g,⟨w,Finset.mem_singleton_self _,hg⟩,?_⟩
    rcases hends with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2
  have huw : ConnectedIn G u w := Relation.EqvGen.rel _ _ ⟨huG,hw,v.val,hvu,hvw⟩
  have hwB : w ∈ blockOf G a := (mem_blockOf G a w).mpr
    ⟨hw,Relation.EqvGen.trans _ _ _ hau huw⟩
  refine ⟨g,⟨w,hwB,hg⟩,?_⟩
  rcases hends with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

theorem reachable_incident {L : ℕ} (G : Finset (Spectrum α L)) (a : Spectrum α L)
    (v z : {v : Gram α (L-1) // v ∈ incidentVertices G})
    (hv : Incident (blockOf G a) v.val) (h : (supportGraph G).Reachable v z) :
    Incident (blockOf G a) z.val :=
  ConnectedBlocks.reachable_mem (supportGraph G) {v | Incident (blockOf G a) v.val}
    (fun v hv z h => incident_closed G a v z hv h) hv h

theorem catalogue_block_count {k L t b : ℕ} (G : Finset (Spectrum α L))
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L)
    (Q : Finset (Finset (Spectrum α L))) (hQ : ∀ B ∈ Q, B ∈ blocks G)
    (hsupport : supportUnion {w} ⊆ supportUnion G)
    (hmeet : ∀ B ∈ Q, ∃ g, w g ≠ 0 ∧ Incident B (gramPrefix g)) :
    Q.card ≤ 2*t := by
  classical
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hs : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion G := by
    intro i g hg
    apply hsupport
    refine ⟨w,Finset.mem_singleton_self _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  choose root hroot hreach using fun i => bubble_connected G (B i).1 (B i).2 (hB i) hL (hs i)
  have hchoose : ∀ C : {C : Finset (Spectrum α L) // C ∈ Q},
      ∃ i : Fin (2*t), Incident C.val (root i).val := by
    intro C
    obtain ⟨g,hg,hCg⟩ := hmeet C.val C.property
    rw [heq] at hg
    obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
    obtain ⟨a,ha,hC⟩ := (mem_blocks G C.val).mp (hQ C.val C.property)
    let v : {v : Gram α (L-1) // v ∈ incidentVertices G} :=
      ⟨gramPrefix g,⟨g,hs i g hi,Or.inl rfl⟩⟩
    have hvm : v.val ∈ bubbleVertices L (B i).1 (B i).2 := (difference_endpoint (hB i) hL g hi).1
    have hvC : Incident (blockOf G a) v.val := by simpa only [hC] using hCg
    have hres := reachable_incident G a v (root i) hvC (hreach i v hvm).symm
    exact ⟨i,by simpa only [hC] using hres⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro C D he
    apply Subtype.ext
    by_contra hne
    exact blocks_support_disjoint G C.val (hQ C.val C.property) D.val (hQ D.val D.property)
      hne (root (f C)).val (hf C) (by simpa only [he] using hf D)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe,Fintype.card_fin] using hc

end DeletionGraph.WitnessSupport
namespace DeletionGraph.WitnessAdjunction
open DeletionHash.MixedEdit WitnessBlocks
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem connectedIn_mono {L : ℕ} {U V : Finset (Spectrum α L)} (hUV : U ⊆ V)
    {a b : Spectrum α L} (h : ConnectedIn U a b) : ConnectedIn V a b := by
  induction h with
  | rel a b hab =>
    exact Relation.EqvGen.rel _ _ ⟨hUV hab.1, hUV hab.2.1, hab.2.2⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

/-- Paths within an equivalence class can be restricted to that class itself. -/
theorem path_within_block {L : ℕ} (U : Finset (Spectrum α L))
    {b c : Spectrum α L} (hbc : ConnectedIn U b c) :
    ∀ a, ConnectedIn U a b → ConnectedIn (blockOf U a) b c := by
  induction hbc with
  | rel b c hbc =>
    intro a hab
    have hb : b ∈ blockOf U a := (mem_blockOf U a b).mpr ⟨hbc.1, hab⟩
    have hc : c ∈ blockOf U a := (mem_blockOf U a c).mpr
      ⟨hbc.2.1, Relation.EqvGen.trans _ _ _ hab (Relation.EqvGen.rel _ _ hbc)⟩
    exact Relation.EqvGen.rel _ _ ⟨hb, hc, hbc.2.2⟩
  | refl b =>
    intro a hab
    exact Relation.EqvGen.refl _
  | symm b c hbc ih =>
    intro a hac
    have hab : ConnectedIn U a b :=
      Relation.EqvGen.trans _ _ _ hac (Relation.EqvGen.symm _ _ hbc)
    exact Relation.EqvGen.symm _ _ (ih a hab)
  | trans b c d hbc hcd ihbc ihcd =>
    intro a hab
    exact Relation.EqvGen.trans _ _ _ (ihbc a hab)
      (ihcd a (Relation.EqvGen.trans _ _ _ hab hbc))

/-- Every actual rule block is connected using only its own rules. -/
theorem blockOf_connected {L : ℕ} (U : Finset (Spectrum α L))
    (a : Spectrum α L) : Connected (blockOf U a) := by
  intro b hb c hc
  have hab := ((mem_blockOf U a b).mp hb).2
  have hac := ((mem_blockOf U a c).mp hc).2
  exact path_within_block U
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hac) a hab

private theorem adjacent_mem_attached_union {L : ℕ} (U : Finset (Spectrum α L))
    (w b : Spectrum α L) (hb : b ∈ U) (hwb : RuleAdjacent w b) :
    b ∈ (attachedBlocks U w).biUnion id := by
  classical
  have hbblock : b ∈ blockOf U b :=
    (mem_blockOf U b b).mpr ⟨hb, Relation.EqvGen.refl _⟩
  obtain ⟨v, hvw, hvb⟩ := hwb
  have hvblock : Incident (blockOf U b) v :=
    ComponentInsert.incident_mono (Finset.singleton_subset_iff.mpr hbblock) hvb
  have hblock : blockOf U b ∈ attachedBlocks U w :=
    (mem_attachedBlocks U (blockOf U b) w).mpr
      ⟨(mem_blocks U (blockOf U b)).mpr ⟨b, hb, rfl⟩, v, hvblock, hvw⟩
  exact Finset.mem_biUnion.mpr ⟨blockOf U b, hblock, hbblock⟩

private theorem attached_union_closed {L : ℕ} (U : Finset (Spectrum α L))
    (w a b : Spectrum α L)
    (ha : a ∈ (attachedBlocks U w).biUnion id) (hb : b ∈ U)
    (hab : RuleAdjacent a b) : b ∈ (attachedBlocks U w).biUnion id := by
  classical
  obtain ⟨B, hB, haB⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨d, hd, hBvalue⟩ := (mem_blocks U B).mp ((mem_attachedBlocks U B w).mp hB).1
  have had : a ∈ blockOf U d := by simpa only [id_eq, hBvalue] using haB
  obtain ⟨haU, hda⟩ := (mem_blockOf U d a).mp had
  have hdb : ConnectedIn U d b := Relation.EqvGen.trans _ _ _ hda
    (Relation.EqvGen.rel _ _ ⟨haU, hb, hab⟩)
  have hbB : b ∈ B := by
    rw [← hBvalue]
    exact (mem_blockOf U d b).mpr ⟨hb, hdb⟩
  exact Finset.mem_biUnion.mpr ⟨B, hB, hbB⟩

/-- The new block is exactly the new rule and the old blocks touching it.
Freshness of w is unnecessary for this identity. -/
theorem blockOf_insert_eq {L : ℕ} (U : Finset (Spectrum α L))
    (w : Spectrum α L) :
    blockOf (insert w U) w = insert w ((attachedBlocks U w).biUnion id) := by
  classical
  let M := insert w ((attachedBlocks U w).biUnion id)
  have hstep (a b : Spectrum α L)
      (ha : a ∈ insert w U) (hb : b ∈ insert w U) (hab : RuleAdjacent a b) :
      a ∈ M → b ∈ M := by
    intro haM
    by_cases hbw : b = w
    · subst b
      exact Finset.mem_insert_self _ _
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hbw
      rcases Finset.mem_insert.mp haM with haw | haUnion
      · subst a
        exact Finset.mem_insert_of_mem (adjacent_mem_attached_union U w b hbU hab)
      · exact Finset.mem_insert_of_mem (attached_union_closed U w a b haUnion hbU hab)
  have hpreserve (a b : Spectrum α L)
      (h : ConnectedIn (insert w U) a b) : a ∈ M ↔ b ∈ M := by
    induction h with
    | rel a b hab =>
      exact ⟨hstep a b hab.1 hab.2.1 hab.2.2,
        hstep b a hab.2.1 hab.1 (adjacent_symm hab.2.2)⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  ext b
  constructor
  · intro hb
    have hpath := ((mem_blockOf (insert w U) w b).mp hb).2
    exact (hpreserve w b hpath).mp (Finset.mem_insert_self _ _)
  · intro hb
    rcases Finset.mem_insert.mp hb with hbw | hbUnion
    · subst b
      exact (mem_blockOf (insert w U) w w).mpr
        ⟨Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩
    · obtain ⟨B, hB, hbB⟩ := Finset.mem_biUnion.mp hbUnion
      obtain ⟨hBold, v, hvB, hvw⟩ := (mem_attachedBlocks U B w).mp hB
      obtain ⟨a, haB, hva⟩ := (incident_iff_rule B v).mp hvB
      obtain ⟨d, hd, hBvalue⟩ := (mem_blocks U B).mp hBold
      have haBlock : a ∈ blockOf U d := by simpa only [id_eq, hBvalue] using haB
      have hbBlock : b ∈ blockOf U d := by simpa only [id_eq, hBvalue] using hbB
      obtain ⟨haU, hda⟩ := (mem_blockOf U d a).mp haBlock
      obtain ⟨hbU, hdb⟩ := (mem_blockOf U d b).mp hbBlock
      have habOld : ConnectedIn U a b :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hda) hdb
      have habNew : ConnectedIn (insert w U) a b :=
        connectedIn_mono (Finset.subset_insert _ _) habOld
      have hwa : ConnectedIn (insert w U) w a := Relation.EqvGen.rel _ _
        ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem haU, v, hvw, hva⟩
      exact (mem_blockOf (insert w U) w b).mpr
        ⟨Finset.mem_insert_of_mem hbU, Relation.EqvGen.trans _ _ _ hwa habNew⟩

theorem new_block_card_bound {k L t b : ℕ} (U : Finset (Spectrum α L))
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L)
    (hsize : ∀ B ∈ blocks U, B.card ≤ L) :
    (blockOf (insert w U) w).card ≤ 1+2*t*(2*L+2*b-2)*L := by
  rw [blockOf_insert_eq]
  exact attached_union_bound U w hw hL hsize

theorem new_block_component_bound {k L t b : ℕ} (n : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (U : Finset (Spectrum α L)) (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hcat : ∀ u ∈ U, u ∈ Catalogue k L t b) :
    componentCount (blockOf (insert w U) w) ≤
      (2*t-1)*(blockOf (insert w U) w).card+1 := by
  apply (DeletionHash.MixedEdit.connected_blocks n t b k L hreg).2
  · intro u hu
    have hmem := ((mem_blockOf (insert w U) w u).mp hu).1
    rcases Finset.mem_insert.mp hmem with rfl | hu
    · exact hw
    · exact hcat u hu
  · exact connected_rules _ (blockOf_nonempty _ _ (Finset.mem_insert_self _ _))
      (blockOf_connected _ _)

end DeletionGraph.WitnessAdjunction
namespace DeletionGraph.WitnessHull
open DeletionHash.MixedEdit WitnessBlocks WitnessAdjunction
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

noncomputable def blockHull {L : ℕ} (G I : Finset (Spectrum α L)) : Finset (Spectrum α L) := by
  classical
  exact G.filter (fun z => ∃ i ∈ I, ConnectedIn G i z)

@[simp] theorem mem_hull {L : ℕ} (G I : Finset (Spectrum α L)) (z : Spectrum α L) :
    z ∈ blockHull G I ↔ z ∈ G ∧ ∃ i ∈ I, ConnectedIn G i z := by
  classical
  simp [blockHull]

theorem hull_subset {L : ℕ} (G I : Finset (Spectrum α L)) : blockHull G I ⊆ G := by
  intro z hz
  exact ((mem_hull G I z).mp hz).1

theorem subset_hull {L : ℕ} (G I : Finset (Spectrum α L)) (hIG : I ⊆ G) : I ⊆ blockHull G I := by
  intro z hz
  exact (mem_hull G I z).mpr ⟨hIG hz,z,hz,Relation.EqvGen.refl z⟩

theorem hull_closed {L : ℕ} (G I : Finset (Spectrum α L)) {a b : Spectrum α L}
    (ha : a ∈ blockHull G I) (hab : ConnectedIn G a b) : b ∈ blockHull G I := by
  obtain ⟨haG,i,hi,hia⟩ := (mem_hull G I a).mp ha
  exact (mem_hull G I b).mpr ⟨(connected_mem G hab).mp haG,i,hi,
    Relation.EqvGen.trans _ _ _ hia hab⟩

theorem hull_path {L : ℕ} (G I : Finset (Spectrum α L)) (z : Spectrum α L)
    (hz : z ∈ blockHull G I) :
    ∃ i ∈ I, ConnectedIn (blockHull G I) i z := by
  obtain ⟨hzG,i,hi,hiz⟩ := (mem_hull G I z).mp hz
  have hpath := path_within_block G hiz i (Relation.EqvGen.refl i)
  have hsub : blockOf G i ⊆ blockHull G I := by
    intro w hw
    obtain ⟨hwG,hiw⟩ := (mem_blockOf G i w).mp hw
    exact (mem_hull G I w).mpr ⟨hwG,i,hi,hiw⟩
  exact ⟨i,hi,connectedIn_mono hsub hpath⟩

theorem growth_bound {k L t b : ℕ} (n : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (I H : Finset (Spectrum α L)) (hIH : I ⊆ H)
    (hcat : ∀ w ∈ H, w ∈ Catalogue k L t b)
    (hpath : ∀ z ∈ H, ∃ i ∈ I, ConnectedIn H i z)
    (hbound : componentCount I ≤ (2*t-1)*I.card) :
    componentCount H ≤ (2*t-1)*H.card := by
  classical
  let S := H.powerset.filter (fun F => I ⊆ F ∧ componentCount F ≤ (2*t-1)*F.card)
  have hseed : I ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hIH,Finset.Subset.refl I,hbound⟩
  obtain ⟨F,hF,hmax⟩ := Finset.exists_max_image S Finset.card ⟨I,hseed⟩
  have hf := Finset.mem_filter.mp hF
  have hFH := Finset.mem_powerset.mp hf.1
  have hIF := hf.2.1
  have hcount := hf.2.2
  have hclosed : ∀ a ∈ F, ∀ z ∈ H, RuleAdjacent a z → z ∈ F := by
    intro a ha z hz hadj
    by_contra hzf
    have hc := (DeletionHash.MixedEdit.connected_blocks n t b k L hreg).1 F (fun u hu => hcat u (hFH hu)) z (hcat z hz) hzf ⟨a,ha,adjacent_symm hadj⟩
    have hnewcount : componentCount (insert z F) ≤ (2*t-1)*(insert z F).card := by
      rw [Finset.card_insert_of_notMem hzf,Nat.mul_add,Nat.mul_one]
      omega
    have hnew : insert z F ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset hz hFH),
        hIF.trans (Finset.subset_insert z F),hnewcount⟩
    have hm := hmax _ hnew
    rw [Finset.card_insert_of_notMem hzf] at hm
    omega
  have hpres : ∀ a z, ConnectedIn H a z → (a ∈ F ↔ z ∈ F) := by
    intro a z h
    induction h with
    | rel a z h =>
      exact ⟨fun ha => hclosed a ha z h.2.1 h.2.2,
        fun hz => hclosed z hz a h.1 (adjacent_symm h.2.2)⟩
    | refl a => rfl
    | symm a z h ih => exact ih.symm
    | trans a z w h1 h2 ih1 ih2 => exact ih1.trans ih2
  have hHF : H ⊆ F := by
    intro z hz
    obtain ⟨i,hi,hiz⟩ := hpath z hz
    exact (hpres i z hiz).mp (hIF hi)
  have heq := Finset.Subset.antisymm hFH hHF
  rwa [heq] at hcount

theorem relation_hull_bound (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (G I : Finset (Spectrum α L)) (hIG : I ⊆ G) (hI : 2 ≤ I.card)
    (hcat : ∀ z ∈ G, z ∈ Catalogue k L t b)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hrel : parity w=∑ z ∈ I, parity z) :
    componentCount (blockHull G I) ≤ (2*t-1)*(blockHull G I).card := by
  have hL : 1 ≤ L := by have h:=hreg.2.2.2.2.1;omega
  have ht : 1 ≤ t := by have h:=hreg.2.1;omega
  apply growth_bound n hreg I (blockHull G I) (subset_hull G I hIG)
  · intro z hz
    exact hcat z (hull_subset G I hz)
  · exact hull_path G I
  · exact (DeletionHash.MixedEdit.relation_savings n t b k L hreg I (fun z hz => hcat z (hIG hz)) w hw hrel).2 hI

end DeletionGraph.WitnessHull
namespace DeletionGraph.GeneratingSets
open DeletionHash.MixedEdit WitnessBlocks
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem nonzero_incident {L : ℕ} (w : Spectrum α L) (g : Gram α L) (hg : w g ≠ 0) :
    Incident {w} (gramPrefix g) :=
  ⟨g,⟨w,Finset.mem_singleton_self _,hg⟩,Or.inl rfl⟩

def GeneratingOn {L : ℕ} (v : Spectrum α L) (G : Finset (Spectrum α L))
    (rank : (Spectrum α L) → ℕ) : Prop :=
  ∀ u ∈ G, ∀ g, u g = -1 → v g ≠ 0 ∨ ∃ z ∈ G, rank z < rank u ∧ z g ≠ 0

def Independent {L : ℕ} (G : Finset (Spectrum α L)) : Prop :=
  LinearIndependent (ZMod 2) (fun u : G => parity u.val)

/-- A finite independent generating set with an actual strict ordering. -/
structure GeneratingAt {L : ℕ} (v : Spectrum α L) (G : Finset (Spectrum α L)) : Prop where
  independent : Independent G
  ordered : ∃ rank : (Spectrum α L) → ℕ,
    Set.InjOn rank (↑G : Set _) ∧ GeneratingOn v G rank

def ClosedIn {L : ℕ} (G U : Finset (Spectrum α L)) : Prop :=
  ∀ a ∈ U, ∀ b ∈ G, ConnectedIn G a b → b ∈ U

theorem independent_restrict {L : ℕ} {G U : Finset (Spectrum α L)} (hUG : U ⊆ G)
    (hind : Independent G) : Independent U := by
  let f : U → G := fun u => ⟨u.val, hUG u.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun u : G => u.val) hab)
  exact hind.comp f hf

theorem generating_restrict {L : ℕ} (v : Spectrum α L)
    (G U : Finset (Spectrum α L)) (rank : (Spectrum α L) → ℕ)
    (hUG : U ⊆ G) (hclosed : ClosedIn G U) (hgen : GeneratingOn v G rank) :
    GeneratingOn v U rank := by
  intro u hu g hneg
  rcases hgen u (hUG hu) g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · have hconnect : ConnectedIn G u z := Relation.EqvGen.rel _ _
      ⟨hUG hu, hz, gramPrefix g,
        nonzero_incident u g (by omega),
        nonzero_incident z g hzg⟩
    exact Or.inr ⟨z, hclosed u hu z hz hconnect, hrank, hzg⟩

theorem GeneratingAt.restrict {L : ℕ} {v : Spectrum α L}
    {G U : Finset (Spectrum α L)} (hgen : GeneratingAt v G) (hUG : U ⊆ G)
    (hclosed : ClosedIn G U) : GeneratingAt v U := by
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  refine ⟨independent_restrict hUG hgen.independent, rank, ?_,
    generating_restrict v G U rank hUG hclosed horder⟩
  intro a ha b hb hab
  exact hinj (hUG ha) (hUG hb) hab

theorem blockHull_closed {L : ℕ} (G I : Finset (Spectrum α L)) :
    ClosedIn G (WitnessHull.blockHull G I) := by
  intro a ha b _ hab
  exact WitnessHull.hull_closed G I ha hab

theorem generating_blockHull {L : ℕ} {v : Spectrum α L}
    {G : Finset (Spectrum α L)} (hgen : GeneratingAt v G) (I : Finset (Spectrum α L)) :
    GeneratingAt v (WitnessHull.blockHull G I) :=
  hgen.restrict (WitnessHull.hull_subset G I) (blockHull_closed G I)

theorem blockOf_closed {L : ℕ} (G : Finset (Spectrum α L)) (a : Spectrum α L) :
    ClosedIn G (blockOf G a) := by
  intro b hb c hc hbc
  exact (mem_blockOf G a c).mpr
    ⟨hc, Relation.EqvGen.trans _ _ _ ((mem_blockOf G a b).mp hb).2 hbc⟩

theorem generating_blockOf {L : ℕ} {v : Spectrum α L}
    {G : Finset (Spectrum α L)} (hgen : GeneratingAt v G) (a : Spectrum α L) :
    GeneratingAt v (blockOf G a) := by
  apply hgen.restrict
  · intro u hu
    exact ((mem_blockOf G a u).mp hu).1
  · exact blockOf_closed G a


end DeletionGraph.GeneratingSets
namespace DeletionGraph.RelationBlocks
open DeletionHash.MixedEdit WitnessBlocks WitnessAdjunction GeneratingSets WitnessHull CatalogueSupport
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

noncomputable def selectedBlocks {L : ℕ} (G I : Finset (Spectrum α L)) :
    Finset (Finset (Spectrum α L)) := by
  classical
  exact (blocks G).filter (fun B => (I ∩ B).Nonempty)

@[simp] theorem mem_selected {L : ℕ} (G I B : Finset (Spectrum α L)) :
    B ∈ selectedBlocks G I ↔ B ∈ blocks G ∧ (I ∩ B).Nonempty := by
  classical
  simp [selectedBlocks]

theorem outside_zero {L : ℕ} (G : Finset (Spectrum α L)) (a w : Spectrum α L)
    (hw : w ∈ G) (hout : w ∉ blockOf G a) (g : Gram α L)
    (hv : Incident (blockOf G a) (gramPrefix g)) : w g=0 := by
  by_contra hg
  obtain ⟨z,hz,hvz⟩ := (incident_iff_rule (blockOf G a) (gramPrefix g)).mp hv
  obtain ⟨hzG,haz⟩ := (mem_blockOf G a z).mp hz
  have hzw : ConnectedIn G z w := Relation.EqvGen.rel _ _
    ⟨hzG,hw,gramPrefix g,hvz,nonzero_incident w g hg⟩
  exact hout ((mem_blockOf G a w).mpr ⟨hw,Relation.EqvGen.trans _ _ _ haz hzw⟩)

theorem independent_sum_ne {L : ℕ} (G I : Finset (Spectrum α L))
    (hIG : I ⊆ G) (hI : I.Nonempty) (hG : Independent G) :
    (∑ z ∈ I, parity z) ≠ 0 := by
  classical
  intro hz
  have hind := independent_restrict hIG hG
  have hs : (∑ z : I, (1 : ZMod 2) • parity z.val)=0 := by
    simpa only [one_smul,Finset.sum_coe_sort] using hz
  obtain ⟨z,hzI⟩ := hI
  have hc : (1 : ZMod 2)=0 :=
    (linearIndependent_iff'.mp hind) Finset.univ (fun _ => 1) hs ⟨z,hzI⟩ (Finset.mem_univ _)
  exact one_ne_zero hc

theorem selected_meets {L : ℕ} (G I : Finset (Spectrum α L)) (hIG : I ⊆ G)
    (w : Spectrum α L) (hind : Independent G)
    (hrel : parity w=∑ z ∈ I, parity z)
    (B : Finset (Spectrum α L)) (hB : B ∈ selectedBlocks G I) :
    ∃ g, w g ≠ 0 ∧ Incident B (gramPrefix g) := by
  classical
  obtain ⟨hBG,hIB⟩ := (mem_selected G I B).mp hB
  obtain ⟨a,ha,hBa⟩ := (mem_blocks G B).mp hBG
  have hne := independent_sum_ne G (I∩B) (Finset.inter_subset_left.trans hIG) hIB hind
  have hex : ∃ g, (∑ z ∈ I∩B, parity z) g ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hne
    funext g
    exact hn g
  obtain ⟨g,hg⟩ := hex
  have hexz : ∃ z ∈ I∩B, z g ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hg
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro z hz
    simp only [parity,hn z hz,Int.cast_zero]
  obtain ⟨z,hz,hzg⟩ := hexz
  have hvB : Incident B (gramPrefix g) :=
    ⟨g,⟨z,(Finset.mem_inter.mp hz).2,hzg⟩,Or.inl rfl⟩
  have hs : (∑ z ∈ I∩B, parity z) g=(∑ z ∈ I, parity z) g := by
    simp only [Finset.sum_apply]
    apply Finset.sum_subset Finset.inter_subset_left
    intro u hu hnot
    have huB : u ∉ B := by intro huB;exact hnot (Finset.mem_inter.mpr ⟨hu,huB⟩)
    have huz := outside_zero G a u (hIG hu) (by simpa only [hBa] using huB) g
      (by simpa only [hBa] using hvB)
    simp only [parity,huz,Int.cast_zero]
  refine ⟨g,?_,hvB⟩
  intro hwg
  apply hg
  rw [hs,←hrel]
  simp only [parity,hwg,Int.cast_zero]

theorem hull_union {L : ℕ} (G I : Finset (Spectrum α L)) (hIG : I ⊆ G) :
    WitnessHull.blockHull G I=(selectedBlocks G I).biUnion id := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzG,i,hi,hiz⟩ := (mem_hull G I z).mp hz
    have hiG := hIG hi
    have hiB : i ∈ blockOf G i := (mem_blockOf G i i).mpr ⟨hiG,Relation.EqvGen.refl _⟩
    have hB : blockOf G i ∈ selectedBlocks G I := (mem_selected G I _).mpr
      ⟨(mem_blocks G _).mpr ⟨i,hiG,rfl⟩,i,Finset.mem_inter.mpr ⟨hi,hiB⟩⟩
    exact Finset.mem_biUnion.mpr ⟨blockOf G i,hB,(mem_blockOf G i z).mpr ⟨hzG,hiz⟩⟩
  · intro hz
    obtain ⟨B,hB,hzB⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hBG,i,hi⟩ := (mem_selected G I B).mp hB
    obtain ⟨a,ha,hBa⟩ := (mem_blocks G B).mp hBG
    have hiz : ConnectedIn G i z := by
      have hiB : i ∈ blockOf G a := by simpa only [hBa] using (Finset.mem_inter.mp hi).2
      have hzB' : z ∈ blockOf G a := by simpa only [hBa,id_eq] using hzB
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ((mem_blockOf G a i).mp hiB).2)
        ((mem_blockOf G a z).mp hzB').2
    exact (mem_hull G I z).mpr ⟨(connected_mem G hiz).mp (hIG (Finset.mem_inter.mp hi).1),
      i,(Finset.mem_inter.mp hi).1,hiz⟩

theorem hull_card {k L t b : ℕ} (G I : Finset (Spectrum α L)) (hIG : I ⊆ G)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L)
    (hind : Independent G) (hrel : parity w=∑ z ∈ I, parity z)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L) :
    (WitnessHull.blockHull G I).card ≤ 2*t*L := by
  have hs : supportUnion {w} ⊆ supportUnion G :=
    (relation_support_subset w hw hL I hrel).trans (ComponentInsert.support_mono hIG)
  have hc := WitnessSupport.catalogue_block_count G w hw hL (selectedBlocks G I)
    (fun B hB => ((mem_selected G I B).mp hB).1) hs
    (fun B hB => selected_meets G I hIG w hind hrel B hB)
  rw [hull_union G I hIG]
  calc
    _ ≤ ∑ B ∈ selectedBlocks G I, B.card := Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ selectedBlocks G I, L := by
      apply Finset.sum_le_sum
      intro B hB
      exact hsize B ((mem_selected G I B).mp hB).1
    _ = (selectedBlocks G I).card*L := by simp
    _ ≤ 2*t*L := Nat.mul_le_mul_right L hc

end DeletionGraph.RelationBlocks
namespace DeletionGraph.LargeBlock
open DeletionHash.MixedEdit WitnessBlocks WitnessAdjunction
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A new block excluding the adjoined rule consists entirely of old rules. -/
theorem blockOf_insert_subset_of_not_mem {L : ℕ} (G : Finset (Spectrum α L))
    (w a : Spectrum α L)
    (hw : w ∉ blockOf (insert w G) a) : blockOf (insert w G) a ⊆ G := by
  classical
  intro b hb
  have hbNew := ((mem_blockOf (insert w G) a b).mp hb).1
  rcases Finset.mem_insert.mp hbNew with hbw | hbG
  · exact False.elim (hw (by simpa only [hbw] using hb))
  · exact hbG

/-- A block that does not contain the new rule is unchanged. No freshness
assumption on w, or membership assumption on its representative a, is needed. -/
theorem blockOf_insert_eq_of_not_mem {L : ℕ} (G : Finset (Spectrum α L))
    (w a : Spectrum α L)
    (hw : w ∉ blockOf (insert w G) a) :
    blockOf (insert w G) a = blockOf G a := by
  classical
  have hsub := blockOf_insert_subset_of_not_mem G w a hw
  ext b
  constructor
  · intro hb
    have hab := ((mem_blockOf (insert w G) a b).mp hb).2
    have hpath : ConnectedIn (blockOf (insert w G) a) a b :=
      path_within_block (insert w G) hab a (Relation.EqvGen.refl a)
    exact (mem_blockOf G a b).mpr
      ⟨hsub hb, connectedIn_mono hsub hpath⟩
  · intro hb
    obtain ⟨hbG, hab⟩ := (mem_blockOf G a b).mp hb
    exact (mem_blockOf (insert w G) a b).mpr
      ⟨Finset.mem_insert_of_mem hbG,
        connectedIn_mono (Finset.subset_insert w G) hab⟩

/-- Any actual new block excluding w is an actual old block. -/
theorem block_not_containing_new_is_old {L : ℕ} (G : Finset (Spectrum α L))
    (w : Spectrum α L) (B : Finset (Spectrum α L))
    (hB : B ∈ blocks (insert w G)) (hw : w ∉ B) : B ∈ blocks G := by
  classical
  obtain ⟨a, ha, hvalue⟩ := (mem_blocks (insert w G) B).mp hB
  have hw' : w ∉ blockOf (insert w G) a := by simpa only [hvalue] using hw
  have haBlock : a ∈ blockOf (insert w G) a :=
    (mem_blockOf (insert w G) a a).mpr ⟨ha, Relation.EqvGen.refl a⟩
  have haG := blockOf_insert_subset_of_not_mem G w a hw' haBlock
  exact (mem_blocks G B).mpr
    ⟨a, haG, (blockOf_insert_eq_of_not_mem G w a hw').symm.trans hvalue⟩

/-- An actual block containing w is the actual block represented by w. -/
theorem block_containing_new_eq {L : ℕ} (G : Finset (Spectrum α L))
    (w : Spectrum α L) (B : Finset (Spectrum α L))
    (hB : B ∈ blocks (insert w G)) (hw : w ∈ B) :
    B = blockOf (insert w G) w := by
  classical
  obtain ⟨a, _, hvalue⟩ := (mem_blocks (insert w G) B).mp hB
  have hw' : w ∈ blockOf (insert w G) a := by simpa only [hvalue] using hw
  have haw := ((mem_blockOf (insert w G) a w).mp hw').2
  exact hvalue.symm.trans (blockOf_eq_of_connected (insert w G) a w haw)

/-- If every old block has size at most M, an oversized new block must be the
block of the adjoined rule. -/
theorem oversized_block_eq_new_block {L : ℕ} (G : Finset (Spectrum α L))
    (w : Spectrum α L) (M : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ M)
    (B : Finset (Spectrum α L)) (hB : B ∈ blocks (insert w G)) (hlarge : M < B.card) :
    B = blockOf (insert w G) w := by
  classical
  by_cases hw : w ∈ B
  · exact block_containing_new_eq G w B hB hw
  · have hold := hsize B (block_not_containing_new_is_old G w B hB hw)
    omega

/-- The stopping condition that some new block is too large gives the lower
bound on the specific new block used in the witness construction. -/
theorem new_block_large_of_exists {L : ℕ} (G : Finset (Spectrum α L))
    (w : Spectrum α L) (M : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ M)
    (hlarge : ∃ B ∈ blocks (insert w G), M < B.card) :
    M < (blockOf (insert w G) w).card := by
  obtain ⟨B, hB, hcard⟩ := hlarge
  simpa only [oversized_block_eq_new_block G w M hsize B hB hcard] using hcard


end DeletionGraph.LargeBlock
namespace DeletionGraph.BinaryRelations
open DeletionHash.MixedEdit CatalogueSupport BubbleConnectivity
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem span_coefficients {L : ℕ} (G : Finset (Spectrum α L)) (v : Gram α L → ZMod 2)
    (hv : v ∈ Submodule.span (ZMod 2) (parity '' (G : Set (Spectrum α L)))) :
    ∃ c : Spectrum α L → ZMod 2, v=∑ w ∈ G, c w • parity w := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w,hw,rfl⟩ := hv
    change w ∈ G at hw
    refine ⟨fun z => if z=w then 1 else 0,?_⟩
    simp [hw]
  | zero =>
    exact ⟨fun _ => 0,by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨c,hc⟩ := ihx
    obtain ⟨d,hd⟩ := ihy
    refine ⟨fun w => c w+d w,?_⟩
    simp only [add_smul,Finset.sum_add_distrib,hc,hd]
  | smul a x hx ih =>
    obtain ⟨c,hc⟩ := ih
    refine ⟨fun w => a*c w,?_⟩
    rw [hc,Finset.smul_sum]
    simp only [mul_smul]

theorem nonzero_one (a : ZMod 2) (ha : a ≠ 0) : a=1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

theorem span_subset_sum {L : ℕ} (G : Finset (Spectrum α L)) (v : Gram α L → ZMod 2)
    (hv : v ∈ Submodule.span (ZMod 2) (parity '' (G : Set (Spectrum α L)))) :
    ∃ I : Finset (Spectrum α L), I ⊆ G ∧ v=∑ w ∈ I, parity w := by
  classical
  obtain ⟨c,hc⟩ := span_coefficients G v hv
  refine ⟨G.filter (fun w => c w ≠ 0),Finset.filter_subset _ _,?_⟩
  rw [hc,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hz : c w=0
  · simp [hz]
  · simp [hz,nonzero_one (c w) hz]

theorem catalogue_parity_ne {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (ht : 1 ≤ t) : parity w ≠ 0 := by
  classical
  have hcopy := hw
  obtain ⟨B,hB,hdis,heq⟩ := hcopy
  let i : Fin (2*t) := ⟨0,by omega⟩
  obtain ⟨g,hg⟩ := bubble_nonzero (B i).1 (B i).2 (hB i) hL
  have hwg : w g ≠ 0 := by
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  intro hz
  apply hwg
  apply (parity_zero_iff w hw hL g).mp
  rw [hz];rfl

theorem new_relation {k L t b : ℕ} (G : Finset (Spectrum α L)) (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (ht : 1 ≤ t)
    (hnew : ∀ z ∈ G, parity w ≠ parity z)
    (hspan : parity w ∈ Submodule.span (ZMod 2) (parity '' (G : Set (Spectrum α L)))) :
    ∃ I : Finset (Spectrum α L), I ⊆ G ∧ 2 ≤ I.card ∧ parity w=∑ z ∈ I, parity z := by
  classical
  obtain ⟨I,hIG,hrel⟩ := span_subset_sum G (parity w) hspan
  refine ⟨I,hIG,?_,hrel⟩
  by_contra hcard
  have hzero : I.card=0 ∨ I.card=1 := by omega
  rcases hzero with hzero | hone
  · have hI : I=∅ := Finset.card_eq_zero.mp hzero
    have hz : parity w=0 := by simpa only [hI,Finset.sum_empty] using hrel
    exact catalogue_parity_ne w hw hL ht hz
  · obtain ⟨z,hI⟩ := Finset.card_eq_one.mp hone
    have hz : z ∈ G := hIG (hI ▸ Finset.mem_singleton_self z)
    apply hnew z hz
    simpa only [hI,Finset.sum_singleton] using hrel

end DeletionGraph.BinaryRelations
namespace DeletionGraph.GeneratingOrder
open DeletionHash.MixedEdit GeneratingSets
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Sort the actual finite set by its injective ranks. -/
theorem rank_sorted_enumeration {L : ℕ} (G : Finset (Spectrum α L))
    (rank : (Spectrum α L) → ℕ)
    (hinj : Set.InjOn rank (↑G : Set _)) :
    ∃ e : Fin G.card ≃ G, StrictMono (fun i => rank (e i).val) := by
  classical
  let S := G.image rank
  let f : G → S := fun u => ⟨rank u.val, Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact hinj u.property v.property (congrArg Subtype.val huv)
    · intro r
      obtain ⟨u, hu, hur⟩ := Finset.mem_image.mp r.property
      exact ⟨⟨u, hu⟩, Subtype.ext hur⟩
  let er : G ≃ S := Equiv.ofBijective f hf
  have hcard : S.card = G.card := by
    simpa using Fintype.card_congr er.symm
  let sorted : Fin G.card ≃o S := S.orderIsoOfFin hcard
  let e : Fin G.card ≃ G := sorted.toEquiv.trans er.symm
  have hrank (i : Fin G.card) : rank (e i).val = (sorted i).val := by
    exact congrArg Subtype.val (er.apply_symm_apply (sorted i))
  refine ⟨e, ?_⟩
  intro i j hij
  change rank (e i).val < rank (e j).val
  rw [hrank i, hrank j]
  exact sorted.strictMono hij

/-- The earlier-supplier property survives the rank-sorted finite enumeration. -/
theorem exists_ordered_enumeration {L : ℕ} (v : Spectrum α L)
    (G : Finset (Spectrum α L)) (hgen : GeneratingAt v G) :
    ∃ e : Fin G.card ≃ G, ∀ i g, (e i).val g = -1 →
      v g ≠ 0 ∨ ∃ j : Fin G.card, j < i ∧ (e j).val g ≠ 0 := by
  classical
  obtain ⟨rank, hinj, horder⟩ := hgen.ordered
  obtain ⟨e, hmono⟩ := rank_sorted_enumeration G rank hinj
  refine ⟨e, ?_⟩
  intro i g hneg
  rcases horder (e i).val (e i).property g hneg with hv | ⟨z, hz, hrank, hzg⟩
  · exact Or.inl hv
  · let j : Fin G.card := e.symm ⟨z, hz⟩
    have hj : (e j).val = z := by simp [j]
    have hji : j < i := by
      by_contra hnot
      have hij : i ≤ j := le_of_not_gt hnot
      have hrle := hmono.monotone hij
      rw [hj] at hrle
      omega
    exact Or.inr ⟨j, hji, by simpa only [hj] using hzg⟩

theorem mission_enumeration {k L t b : ℕ} (v : Spectrum α L)
    (F : Finset (Spectrum α L)) (hgen : GeneratingAt v F)
    (hcat : ∀ w ∈ F, w ∈ Catalogue k L t b) :
    ∃ G : Fin F.card → Spectrum α L, GeneratingSequence k t b v G ∧ ruleSet G=F := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  obtain ⟨e,horder⟩ := exists_ordered_enumeration v F hgen
  let G : Fin F.card → Spectrum α L := fun i => (e i).val
  refine ⟨G,⟨fun i => hcat _ (e i).property,?_,horder⟩,?_⟩
  · have hind : LinearIndependent (ZMod 2) (fun z : F => parity z.val) := hgen.independent
    change LinearIndependent (ZMod 2) (fun i : Fin F.card => parity (e i).val)
    exact hind.comp (fun i : Fin F.card => e i) e.injective
  · unfold ruleSet
    apply Finset.ext
    intro w
    constructor
    · intro hw
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
      exact (e i).property
    · intro hw
      obtain ⟨i,hi⟩ := e.surjective ⟨w,hw⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩

end DeletionGraph.GeneratingOrder
namespace DeletionGraph.WitnessCases
open DeletionHash.MixedEdit WitnessBlocks WitnessAdjunction WitnessHull GeneratingSets
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

structure Witness (k L t b : ℕ) (v : Spectrum α L) (K : Set (Spectrum α L))
    (U : Finset (Spectrum α L)) : Prop where
  generating : GeneratingAt v U
  catalogue : ∀ w ∈ U, w ∈ Catalogue k L t b
  surviving : ∀ w ∈ U, w ∈ K
  size_lower : 2 ≤ U.card
  size_upper : U.card ≤ witnessBound t b L
  components : componentCount U ≤ (2*t-1)*U.card+1
  small_components : U.card ≤ L → componentCount U ≤ (2*t-1)*U.card

theorem relation_case (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (v : Spectrum α L) (K : Set (Spectrum α L))
    (G I : Finset (Spectrum α L)) (hIG : I ⊆ G) (hI : 2 ≤ I.card)
    (hgen : GeneratingAt v G) (hcat : ∀ w ∈ G, w ∈ Catalogue k L t b)
    (hK : ∀ w ∈ G, w ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hrel : parity w=∑ z ∈ I, parity z) :
    Witness k L t b v K (WitnessHull.blockHull G I) := by
  let U := WitnessHull.blockHull G I
  have hUG : U ⊆ G := hull_subset G I
  have hlow : 2 ≤ U.card := hI.trans (Finset.card_le_card (subset_hull G I hIG))
  have hL : 2 ≤ L := by have h:=hreg.2.2.2.2.1;omega
  have hb : 1 ≤ b := hreg.2.2.1
  have hupper : U.card ≤ 2*t*L :=
    RelationBlocks.hull_card G I hIG w hw (by omega) hgen.independent hrel hsize
  have hM : 2*t*L ≤ witnessBound t b L := by
    have hfactor : 1 ≤ 2*L+2*b-2 := by omega
    have hmul := Nat.mul_le_mul_left (2*t) hfactor
    have hm := Nat.mul_le_mul_right L hmul
    unfold witnessBound
    nlinarith
  have hc := relation_hull_bound n t b k L hreg G I hIG hI hcat w hw hrel
  exact ⟨generating_blockHull hgen I,fun w hw => hcat w (hUG hw),
    fun w hw => hK w (hUG hw),hlow,hupper.trans hM,by omega,fun _ => hc⟩

theorem relation_of_span (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (v : Spectrum α L) (K : Set (Spectrum α L)) (G : Finset (Spectrum α L))
    (hgen : GeneratingAt v G) (hcat : ∀ w ∈ G, w ∈ Catalogue k L t b)
    (hK : ∀ w ∈ G, w ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hnew : ∀ z ∈ G, parity w ≠ parity z)
    (hspan : parity w ∈ Submodule.span (ZMod 2) (parity '' (G : Set (Spectrum α L)))) :
    ∃ U, Witness k L t b v K U := by
  have hL : 1 ≤ L := by have h:=hreg.2.2.2.2.1;omega
  have ht : 1 ≤ t := by have h:=hreg.2.1;omega
  obtain ⟨I,hIG,hI,hrel⟩ := BinaryRelations.new_relation G w hw hL ht hnew hspan
  exact ⟨_,relation_case n t b k L hreg v K G I hIG hI hgen hcat hK hsize w hw hrel⟩

theorem large_case (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (v : Spectrum α L) (K : Set (Spectrum α L)) (G : Finset (Spectrum α L)) (w : Spectrum α L)
    (hgen : GeneratingAt v (insert w G)) (hw : w ∈ Catalogue k L t b)
    (hcat : ∀ z ∈ G, z ∈ Catalogue k L t b)
    (hK : ∀ z ∈ insert w G, z ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (hbad : ¬∀ B ∈ blocks (insert w G), B.card ≤ L) :
    Witness k L t b v K (blockOf (insert w G) w) := by
  classical
  have hex : ∃ B ∈ blocks (insert w G), L < B.card := by
    push Not at hbad
    exact hbad
  have hlarge := LargeBlock.new_block_large_of_exists G w L hsize hex
  have hL : 2 ≤ L := by have h:=hreg.2.2.2.2.1;omega
  have ht : 1 ≤ t := by have h:=hreg.2.1;omega
  have hsub : blockOf (insert w G) w ⊆ insert w G := by
    intro z hz
    exact ((mem_blockOf (insert w G) w z).mp hz).1
  refine ⟨generating_blockOf hgen w,?_,fun z hz => hK z (hsub hz),by omega,
    new_block_card_bound G w hw (by omega) hsize,
    new_block_component_bound n hreg G w hw hcat,?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp (hsub hz) with rfl | hz
    · exact hw
    · exact hcat z hz
  · intro hsmall
    omega

end DeletionGraph.WitnessCases
namespace DeletionGraph.BinaryClosedWalk
open scoped BigOperators

theorem sum_displacements {V : Type*} [AddCommGroup V] {m : ℕ}
    (p : Fin (m+1) → V) :
    (∑ i : Fin m, (p i.succ-p i.castSucc))=p (Fin.last m)-p 0 := by
  rw [Finset.sum_sub_distrib]
  have h := (Fin.sum_univ_succ p).symm.trans (Fin.sum_univ_castSucc p)
  calc
    _=(p 0+∑ i : Fin m,p i.succ)-(p 0+∑ i : Fin m,p i.castSucc) := by abel
    _=((∑ i : Fin m,p i.castSucc)+p (Fin.last m))-(p 0+∑ i : Fin m,p i.castSucc) := by rw [h]
    _=_ := by abel

theorem independent_sum_even {I J V : Type*} [Fintype I] [Fintype J]
    [AddCommGroup V] [Module (ZMod 2) V] (G : I → V)
    (hG : LinearIndependent (ZMod 2) G) (label : J → I)
    (hsum : (∑ j, G (label j))=0) : Even (Fintype.card J) := by
  classical
  let c : I → ZMod 2 := fun i => ∑ j, if label j=i then 1 else 0
  have hgrouped : (∑ i, c i • G i)=0 := by
    calc
      _=∑ j, ∑ i, (if label j=i then (1 : ZMod 2) else 0) • G i := by
        simp only [c,Finset.sum_smul]
        rw [Finset.sum_comm]
      _=∑ j, G (label j) := by simp
      _=0 := hsum
  have hc : ∀ i, c i=0 := fun i =>
    (linearIndependent_iff'.mp hG) Finset.univ c hgrouped i (Finset.mem_univ i)
  have htotal : (Fintype.card J : ZMod 2)=0 := by
    calc
      _=∑ i, c i := by
        simp only [c]
        rw [Finset.sum_comm]
        simp
      _=0 := Finset.sum_eq_zero (fun i hi => hc i)
  exact ZMod.natCast_eq_zero_iff_even.mp htotal

theorem neg_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (v : V) : -v=v := by
  have h : (-1 : ZMod 2)=1 := by decide
  rw [←neg_one_smul (ZMod 2),h,one_smul]

theorem not_odd_signed_independent_closed_walk {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}
    (G : I → V) (hG : LinearIndependent (ZMod 2) G) (p : Fin (m+1) → V)
    (label : Fin m → I) (hclosed : p 0=p (Fin.last m))
    (hsteps : ∀ i : Fin m, p i.succ-p i.castSucc=G (label i) ∨
      p i.succ-p i.castSucc= -G (label i)) : ¬Odd m := by
  have hs : ∀ i : Fin m,p i.succ-p i.castSucc=G (label i) := by
    intro i
    rcases hsteps i with h | h
    · exact h
    · simpa only [neg_self] using h
  have hsum : (∑ i : Fin m,G (label i))=0 := by
    simp_rw [←hs]
    rw [sum_displacements,←hclosed,sub_self]
  have he := independent_sum_even G hG label hsum
  rintro ⟨a,ha⟩
  obtain ⟨b,hb⟩ := he
  simp only [Fintype.card_fin] at hb
  omega

end DeletionGraph.BinaryClosedWalk

/-!
A finite greedy scan of the actual step indices of a closed walk. Before a
stop, the selected earlier steps are independent, satisfy the chosen cutoff,
and represent every earlier step up to sign. The representation is causal:
its selected index is no later than the step it represents. If the scan never
stops, closed-walk parity contradicts an odd length.
-/
namespace DeletionGraph.WalkScan

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}

def walkStep (p : Fin (m + 1) → V) (i : Fin m) : V := p i.succ - p i.castSucc

def selectedSpan (step : Fin m → V) (S : Finset (Fin m)) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (step '' (S : Set (Fin m)))

def SignedMember (step : Fin m → V) (S : Finset (Fin m)) (v : V) : Prop :=
  ∃ r ∈ S, v = step r ∨ v = -step r

theorem selected_mem_span (step : Fin m → V) (S : Finset (Fin m))
    (r : Fin m) (hr : r ∈ S) : step r ∈ selectedSpan step S :=
  Submodule.subset_span ⟨r, hr, rfl⟩

theorem signed_mem_span (step : Fin m → V) (S : Finset (Fin m))
    (v : V) (hv : SignedMember step S v) : v ∈ selectedSpan step S := by
  obtain ⟨r, hr, h | h⟩ := hv
  · rw [h]
    exact selected_mem_span step S r hr
  · rw [h]
    exact (selectedSpan step S).neg_mem (selected_mem_span step S r hr)

/-- The concrete invariant after scanning the indices smaller than n. -/
structure ScanState (step : Fin m → V) (Good : Finset (Fin m) → Prop)
    (n : ℕ) (S : Finset (Fin m)) : Prop where
  before : ∀ r ∈ S, r.val < n
  good : Good S
  independent : LinearIndepOn (ZMod 2) step (S : Set (Fin m))
  covered : ∀ j : Fin m, j.val < n →
    ∃ r ∈ S, r.val ≤ j.val ∧ (step j = step r ∨ step j = -step r)

theorem ScanState.earlier_span {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (h : ScanState step Good n S)
    (j : Fin m) (hj : j.val < n) : step j ∈ selectedSpan step S := by
  obtain ⟨r, hr, _, heq⟩ := h.covered j hj
  exact signed_mem_span step S (step j) ⟨r, hr, heq⟩

theorem independent_insert {step : Fin m → V} {S : Finset (Fin m)}
    (hs : LinearIndepOn (ZMod 2) step (S : Set (Fin m))) (i : Fin m)
    (hi : step i ∉ selectedSpan step S) :
    LinearIndepOn (ZMod 2) step ((insert i S : Finset (Fin m)) : Set (Fin m)) := by
  simpa only [Finset.coe_insert] using hs.insert hi

private theorem ScanState.skip {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (hs : ScanState step Good n S)
    (i : Fin m) (hi : i.val = n) (hsigned : SignedMember step S (step i)) :
    ScanState step Good (n + 1) S := by
  refine ⟨fun r hr => by have := hs.before r hr; omega, hs.good, hs.independent, ?_⟩
  intro j hj
  by_cases hbefore : j.val < n
  · exact hs.covered j hbefore
  · have hji : j = i := Fin.ext (by omega)
    subst j
    obtain ⟨r, hr, heq⟩ := hsigned
    exact ⟨r, hr, by have := hs.before r hr; omega, heq⟩

theorem ScanState.append {step : Fin m → V} {Good : Finset (Fin m) → Prop}
    {n : ℕ} {S : Finset (Fin m)} (hs : ScanState step Good n S)
    (i : Fin m) (hi : i.val = n) (hout : step i ∉ selectedSpan step S)
    (hgood : Good (insert i S)) : ScanState step Good (n + 1) (insert i S) := by
  refine ⟨?_, hgood, independent_insert hs.independent i hout, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with hri | hrS
    · subst r; omega
    · have := hs.before r hrS
      omega
  · intro j hj
    by_cases hbefore : j.val < n
    · obtain ⟨r, hr, hle, heq⟩ := hs.covered j hbefore
      exact ⟨r, Finset.mem_insert_of_mem hr, hle, heq⟩
    · have hji : j = i := Fin.ext (by omega)
      subst j
      exact ⟨i, Finset.mem_insert_self i S, le_rfl, Or.inl rfl⟩

/-- Either a new relation appears, or an independent append first violates
the chosen cutoff. In both cases S consists of genuinely earlier step indices. -/
def Stopped (step : Fin m → V) (Good : Finset (Fin m) → Prop) : Prop :=
  ∃ (i : Fin m) (S : Finset (Fin m)),
    ScanState step Good i.val S ∧ ¬ SignedMember step S (step i) ∧
      (step i ∈ selectedSpan step S ∨
        (step i ∉ selectedSpan step S ∧
          LinearIndepOn (ZMod 2) step ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
          ¬ Good (insert i S)))

/-- The stopping alternative is constructed by scanning a finite prefix.
No scan trace or final selected family is an input to this theorem. -/
theorem scan_prefix (step : Fin m → V) (Good : Finset (Fin m) → Prop)
    (hgood : Good ∅) (n : ℕ) (hn : n ≤ m) :
    Stopped step Good ∨ ∃ S, ScanState step Good n S := by
  classical
  induction n with
  | zero =>
    right
    refine ⟨∅, ?_, hgood, ?_, ?_⟩
    · intro r hr
      simp at hr
    · simp
    · intro j hj
      omega
  | succ n ih =>
    rcases ih (by omega) with hstop | ⟨S, hs⟩
    · exact Or.inl hstop
    · let i : Fin m := ⟨n, by omega⟩
      by_cases hsigned : SignedMember step S (step i)
      · exact Or.inr ⟨S, hs.skip i rfl hsigned⟩
      · by_cases hspan : step i ∈ selectedSpan step S
        · exact Or.inl ⟨i, S, hs, hsigned, Or.inl hspan⟩
        · have hind := independent_insert hs.independent i hspan
          by_cases hnewgood : Good (insert i S)
          · exact Or.inr ⟨insert i S, hs.append i rfl hspan hnewgood⟩
          · exact Or.inl ⟨i, S, hs, hsigned, Or.inr ⟨hspan, hind, hnewgood⟩⟩

/-- An odd closed walk must trigger one of the two actual scan stopping cases. -/
theorem odd_closed_walk_stops (p : Fin (m + 1) → V)
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    Stopped (walkStep p) Good := by
  classical
  rcases scan_prefix (walkStep p) Good hgood m le_rfl with hstop | ⟨S, hs⟩
  · exact hstop
  · let label : Fin m → S := fun j =>
      ⟨Classical.choose (hs.covered j j.isLt),
        (Classical.choose_spec (hs.covered j j.isLt)).1⟩
    have hsteps : ∀ j : Fin m,
        p j.succ - p j.castSucc = walkStep p (label j).val ∨
        p j.succ - p j.castSucc = -walkStep p (label j).val :=
      fun j => (Classical.choose_spec (hs.covered j j.isLt)).2.2
    exact False.elim (BinaryClosedWalk.not_odd_signed_independent_closed_walk
      (fun r : S => walkStep p r.val) hs.independent p label hclosed hsteps hodd)

/-- A coordinate unchanged by all earlier actual steps has its starting value. -/
theorem coordinate_unchanged_before {H : Type*} (p : Fin (m + 1) → H → (ZMod 2))
    (n : ℕ) (hn : n ≤ m) (h : H)
    (hzero : ∀ j : Fin m, j.val < n → walkStep p j h = 0) :
    p ⟨n, by omega⟩ h = p 0 h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (by omega) (fun j hj => hzero j (by omega))
    let j : Fin m := ⟨n, by omega⟩
    have hstep := hzero j (by dsimp [j]; omega)
    change p ⟨n + 1, by omega⟩ h - p ⟨n, by omega⟩ h = 0 at hstep
    exact (sub_eq_zero.mp hstep).trans hprev


end DeletionGraph.WalkScan
namespace DeletionGraph.GeneratingScan
open DeletionHash.MixedEdit WalkScan
universe u
variable {α : Type u} {L m : ℕ}

def Boolean (p : Spectrum α L) : Prop := ∀ g, p g=0 ∨ p g=1

theorem parity_step (p : Fin (m+1) → Spectrum α L) (i : Fin m) :
    parity (walkStep p i)=walkStep (fun j => parity (p j)) i := by
  funext g
  simp [walkStep,parity,Pi.sub_apply]

theorem negative_source (p q : Spectrum α L) (hp : Boolean p) (hq : Boolean q)
    (g : Gram α L) (hneg : (q-p) g= -1) : p g=1 := by
  have hp' := hp g
  have hq' := hq g
  change q g-p g= -1 at hneg
  omega

def GeneratingSelected (p : Fin (m+1) → Spectrum α L) (S : Finset (Fin m)) : Prop :=
  ∀ i ∈ S, ∀ g, walkStep p i g= -1 →
    p 0 g ≠ 0 ∨ ∃ r ∈ S, r.val < i.val ∧ walkStep p r g ≠ 0

theorem generating {p : Fin (m+1) → Spectrum α L}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep (fun j => parity (p j))) Good n S)
    (hp : ∀ j, Boolean (p j)) : GeneratingSelected p S := by
  classical
  intro i hi g hneg
  by_cases hbase : p 0 g=0
  · right
    by_contra hnone
    have hselected : ∀ r ∈ S, r.val < i.val → walkStep p r g=0 := by
      intro r hr hri
      by_contra hzero
      exact hnone ⟨r,hr,hri,hzero⟩
    have hzero : ∀ j : Fin m, j.val < i.val →
        walkStep (fun j => parity (p j)) j g=0 := by
      intro j hji
      obtain ⟨r,hr,hrj,heq⟩ := hs.covered j (by have h:=hs.before i hi;omega)
      have hrzero := hselected r hr (by omega)
      have hz : walkStep (fun j => parity (p j)) r g=0 := by
        rw [←parity_step]
        simp only [parity,hrzero,Int.cast_zero]
      rcases heq with heq | heq
      · exact (congrFun heq g).trans hz
      · have h := congrFun heq g
        simpa only [Pi.neg_apply,hz,neg_zero] using h
    have hsame := coordinate_unchanged_before (fun j => parity (p j)) i.val
      (Nat.le_of_lt i.isLt) g hzero
    change parity (p i.castSucc) g=parity (p 0) g at hsame
    have hone := negative_source (p i.castSucc) (p i.succ) (hp i.castSucc) (hp i.succ) g hneg
    simp only [parity,hone,hbase,Int.cast_one,Int.cast_zero] at hsame
    exact one_ne_zero hsame
  · exact Or.inl hbase

theorem generating_append {p : Fin (m+1) → Spectrum α L}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep (fun j => parity (p j))) Good n S)
    (hp : ∀ j, Boolean (p j)) (i : Fin m) (hi : i.val=n)
    (hout : walkStep (fun j => parity (p j)) i ∉ selectedSpan (walkStep (fun j => parity (p j))) S) :
    GeneratingSelected p (insert i S) := by
  have htrue : ScanState (walkStep (fun j => parity (p j))) (fun _ => True) n S :=
    ⟨hs.before,trivial,hs.independent,hs.covered⟩
  exact generating (htrue.append i hi hout trivial) hp

theorem odd_boolean_closed_walk_stops (p : Fin (m+1) → Spectrum α L)
    (hp : ∀ j, Boolean (p j)) (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0=p (Fin.last m)) (hodd : Odd m) :
    ∃ (i : Fin m) (S : Finset (Fin m)),
      ScanState (walkStep (fun j => parity (p j))) Good i.val S ∧ GeneratingSelected p S ∧
      ¬ SignedMember (walkStep (fun j => parity (p j))) S (walkStep (fun j => parity (p j)) i) ∧
      (walkStep (fun j => parity (p j)) i ∈ selectedSpan (walkStep (fun j => parity (p j))) S ∨
        (walkStep (fun j => parity (p j)) i ∉ selectedSpan (walkStep (fun j => parity (p j))) S ∧
          LinearIndepOn (ZMod 2) (walkStep (fun j => parity (p j))) ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
          ¬Good (insert i S) ∧ GeneratingSelected p (insert i S))) := by
  obtain ⟨i,S,hs,hnew,hstop⟩ := odd_closed_walk_stops (fun j => parity (p j)) Good hgood
    (congrArg parity hclosed) hodd
  refine ⟨i,S,hs,generating hs hp,hnew,?_⟩
  rcases hstop with hrel | ⟨hout,hind,hbad⟩
  · exact Or.inl hrel
  · exact Or.inr ⟨hout,hind,hbad,generating_append hs hp i rfl hout⟩

end DeletionGraph.GeneratingScan
namespace DeletionGraph.SelectedRules
open DeletionHash.MixedEdit WalkScan GeneratingSets GeneratingScan
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

variable {L m : ℕ}

def step (p : Fin (m + 1) → Gram α L → ℤ) (i : Fin m) :
    Gram α L → ℤ := p i.succ - p i.castSucc

def parityPath (p : Fin (m + 1) → Gram α L → ℤ) :
    Fin (m + 1) → Gram α L → (ZMod 2) := fun j => parity (p j)

noncomputable def selectedRules
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m)) :
    Finset (Spectrum α L) := by
  classical
  exact S.image (step p)

@[simp] theorem parity_step
    (p : Fin (m + 1) → Gram α L → ℤ) (i : Fin m) :
    parity (step p i) = walkStep (parityPath p) i := by
  funext g
  simp [parity, step, walkStep, parityPath]

@[simp] theorem mem_selectedRules
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (u : Gram α L → ℤ) :
    u ∈ selectedRules p S ↔ ∃ i ∈ S, step p i = u := by
  classical
  exact Finset.mem_image

theorem step_mem_selectedRules
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (i : Fin m) (hi : i ∈ S) : step p i ∈ selectedRules p S :=
  (mem_selectedRules p S _).mpr ⟨i, hi, rfl⟩

@[simp] theorem selectedRules_empty
    (p : Fin (m + 1) → Gram α L → ℤ) :
    selectedRules p ∅ = ∅ := by
  classical
  simp [selectedRules]

@[simp] theorem selectedRules_insert
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (i : Fin m) : selectedRules p (insert i S) = insert (step p i) (selectedRules p S) := by
  classical
  simp [selectedRules]

theorem selected_step_injOn
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn (ZMod 2) (walkStep (parityPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (step p) (↑S : Set (Fin m)) := by
  intro i hi j hj hij
  have heq : walkStep (parityPath p) i = walkStep (parityPath p) j := by
    simpa only [parity_step] using congrArg parity hij
  have hs : (⟨i, hi⟩ : S) = ⟨j, hj⟩ := hind.injective heq
  exact congrArg Subtype.val hs

private theorem selectedIndex_exists
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : ∃ i : S, step p i.val = u.val := by
  obtain ⟨i, hi, heq⟩ := (mem_selectedRules p S u.val).mp u.property
  exact ⟨⟨i, hi⟩, heq⟩

noncomputable def selectedIndex
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : S := Classical.choose (selectedIndex_exists p S u)

theorem selectedIndex_spec
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (u : selectedRules p S) : step p (selectedIndex p S u).val = u.val :=
  Classical.choose_spec (selectedIndex_exists p S u)

theorem selectedIndex_injective
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m)) :
    Function.Injective (selectedIndex p S) := by
  intro u v huv
  apply Subtype.ext
  calc
    u.val = step p (selectedIndex p S u).val := (selectedIndex_spec p S u).symm
    _ = step p (selectedIndex p S v).val := by rw [huv]
    _ = v.val := selectedIndex_spec p S v

theorem selectedIndex_step
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn (ZMod 2) (walkStep (parityPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) :
    (selectedIndex p S ⟨step p i, step_mem_selectedRules p S i hi⟩).val = i :=
  selected_step_injOn p S hind (selectedIndex p S _).property hi
    (selectedIndex_spec p S _)

theorem selected_independent
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn (ZMod 2) (walkStep (parityPath p)) (↑S : Set (Fin m))) :
    Independent (selectedRules p S) := by
  have h := hind.comp (selectedIndex p S) (selectedIndex_injective p S)
  change LinearIndependent (ZMod 2) (fun u : selectedRules p S => parity u.val)
  convert h using 1
  funext u
  change parity u.val = walkStep (parityPath p) (selectedIndex p S u).val
  rw [← parity_step, selectedIndex_spec]

noncomputable def selectedRank
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (u : Gram α L → ℤ) : ℕ := by
  classical
  exact if hu : u ∈ selectedRules p S then (selectedIndex p S ⟨u, hu⟩).val.val else 0

theorem selectedRank_step
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn (ZMod 2) (walkStep (parityPath p)) (↑S : Set (Fin m)))
    (i : Fin m) (hi : i ∈ S) : selectedRank p S (step p i) = i.val := by
  classical
  simp only [selectedRank, dif_pos (step_mem_selectedRules p S i hi)]
  rw [selectedIndex_step p S hind i hi]

theorem selectedRank_injOn
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn (ZMod 2) (walkStep (parityPath p)) (↑S : Set (Fin m))) :
    Set.InjOn (selectedRank p S) (↑(selectedRules p S) : Set _) := by
  intro u hu v hv heq
  obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
  obtain ⟨j, hj, rfl⟩ := (mem_selectedRules p S v).mp hv
  rw [selectedRank_step p S hind i hi, selectedRank_step p S hind j hj] at heq
  exact congrArg (step p) (Fin.ext heq)

theorem selected_generatingAt
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m))
    (hind : LinearIndepOn (ZMod 2) (walkStep (parityPath p)) (↑S : Set (Fin m)))
    (hgen : GeneratingSelected p S) :
    GeneratingAt (p 0) (selectedRules p S) := by
  classical
  refine ⟨selected_independent p S hind, selectedRank p S,
    selectedRank_injOn p S hind, ?_⟩
  intro u hu g hneg
  obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
  rcases hgen i hi g hneg with hbase | ⟨r,hr,hri,hrg⟩
  · exact Or.inl hbase
  · right
    refine ⟨step p r,step_mem_selectedRules p S r hr,?_,hrg⟩
    simpa only [selectedRank_step p S hind r hr,selectedRank_step p S hind i hi] using hri

theorem parity_image_selectedRules
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m)) :
    parity '' (↑(selectedRules p S) : Set _) =
      walkStep (parityPath p) '' (↑S : Set (Fin m)) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (mem_selectedRules p S u).mp hu
    exact ⟨i, hi, (parity_step p i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨step p i, step_mem_selectedRules p S i hi, parity_step p i⟩

theorem selectedSpan_eq
    (p : Fin (m + 1) → Gram α L → ℤ) (S : Finset (Fin m)) :
    selectedSpan (walkStep (parityPath p)) S =
      Submodule.span (ZMod 2) (parity '' (↑(selectedRules p S) : Set _)) := by
  rw [parity_image_selectedRules]
  rfl

theorem novelty_transfer
    (p : Fin (m+1) → Spectrum α L) (S : Finset (Fin m)) (i : Fin m)
    (hnew : ¬SignedMember (walkStep (parityPath p)) S (walkStep (parityPath p) i)) :
    ∀ u ∈ selectedRules p S, parity (step p i) ≠ parity u := by
  intro u hu heq
  obtain ⟨r,hr,rfl⟩ := (mem_selectedRules p S u).mp hu
  apply hnew
  exact ⟨r,hr,Or.inl (by simpa only [parity_step] using heq)⟩

end DeletionGraph.SelectedRules
namespace DeletionGraph.WitnessWalk
open DeletionHash.MixedEdit WitnessBlocks WitnessCases GeneratingScan SelectedRules WalkScan
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem extract (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    {m : ℕ} (p : Fin (m+1) → Spectrum α L) (K : Set (Spectrum α L))
    (hp : ∀ j, Boolean (p j)) (hclosed : p 0=p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, step p i ∈ Catalogue k L t b) (hK : ∀ i, step p i ∈ K) :
    ∃ U : Finset (Spectrum α L), Witness k L t b (p 0) K U := by
  classical
  let Good : Finset (Fin m) → Prop := fun S => ∀ B ∈ blocks (selectedRules p S), B.card ≤ L
  have hgood : Good ∅ := by simp [Good,blocks]
  obtain ⟨i,S,hs,hgen,hnew,hstop⟩ :=
    GeneratingScan.odd_boolean_closed_walk_stops p hp Good hgood hclosed hodd
  have hcatS (T : Finset (Fin m)) : ∀ u ∈ selectedRules p T, u ∈ Catalogue k L t b := by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hcat j
  have hKS (T : Finset (Fin m)) : ∀ u ∈ selectedRules p T, u ∈ K := by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := (mem_selectedRules p T u).mp hu
    exact hK j
  rcases hstop with hrel | ⟨hout,hind,hbad,hgen'⟩
  · have hspan : parity (step p i) ∈ Submodule.span (ZMod 2)
        (parity '' (selectedRules p S : Set (Spectrum α L))) := by
      rw [←selectedSpan_eq, SelectedRules.parity_step]
      exact hrel
    exact relation_of_span n t b k L hreg (p 0) K (selectedRules p S)
      (selected_generatingAt p S hs.independent hgen) (hcatS S) (hKS S)
      hs.good (step p i) (hcat i) (novelty_transfer p S i hnew) hspan
  · have hgenI : GeneratingSets.GeneratingAt (p 0) (insert (step p i) (selectedRules p S)) := by
      simpa only [selectedRules_insert] using selected_generatingAt p (insert i S) hind hgen'
    have hKI : ∀ u ∈ insert (step p i) (selectedRules p S), u ∈ K := by
      simpa only [selectedRules_insert] using hKS (insert i S)
    have hbadI : ¬∀ B ∈ blocks (insert (step p i) (selectedRules p S)), B.card ≤ L := by
      simpa only [Good,selectedRules_insert] using hbad
    exact ⟨_,large_case n t b k L hreg (p 0) K (selectedRules p S) (step p i)
      hgenI (hcat i) (hcatS S) hKI hs.good hbadI⟩

end DeletionGraph.WitnessWalk
namespace DeletionGraph.ExceptionalProbability
open DeletionHash.MixedEdit
universe u
theorem hash_sub {α : Type u} [Fintype α] {L r : ℕ}
    (ξ : HashSample α L r) (p q : Spectrum α L) :
    DeletionHash.MixedEdit.hash ξ (p-q) =
      DeletionHash.MixedEdit.hash ξ p - DeletionHash.MixedEdit.hash ξ q := by
  simp [DeletionHash.MixedEdit.hash, parity, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem unique_mono {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {n k m : ℕ} (x : Word α n) (hk : k ≤ m) (hx : IsUnique k (letters x)) :
    IsUnique m (letters x) := by
  apply (UniqueBridge.unique_iff x).mpr
  intro a b ha hb hab
  apply (UniqueBridge.unique_iff x).mp hx a b (by omega) (by omega)
  intro i hi
  exact hab i (by omega)


end DeletionGraph.ExceptionalProbability
namespace DeletionGraph.ConflictRules
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem edge_rule (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (ξ : HashSample α L r)
    (x y : {x : Word α n // Good n k t b ξ x})
    (hedge : (conflictGraph n k t b ξ).Adj x y) :
    Survives k t b ξ (spectrum L (letters y.val)-spectrum L (letters x.val)) := by
  have hne : letters x.val ≠ letters y.val := by
    intro h
    apply hedge.1
    apply Subtype.ext
    exact List.ofFn_injective h
  obtain ⟨record,hrlen,hvalid,htarget⟩ := DeletionHash.MixedEdit.confusable_record t b hreg.2.1 hreg.2.2.1 hreg.1
    (letters x.val) (letters y.val) hne hedge.2.1
  have hnobad : ¬ (record.length<2*t ∨ ¬Separated n t b L record) := by
    intro hbad
    apply x.property.2
    refine ⟨x.property.1,record,hrlen,hvalid,?_,?_,?_,hbad⟩
    · rw [htarget];simp [letters]
    · rw [htarget];exact hne.symm
    · rw [htarget];exact hedge.2.2.symm
  have hlen : record.length=2*t := by
    by_contra h
    exact hnobad (Or.inl (by omega))
  have hsep : Separated n t b L record := by
    by_contra h
    exact hnobad (Or.inr h)
  constructor
  · have h := DeletionHash.MixedEdit.separated_coverage n t b k L hreg x.val x.property.1 record hvalid hlen hsep (by rw [htarget]; simp [letters])
    simpa only [htarget] using h
  · rw [ExceptionalProbability.hash_sub,sub_eq_zero]
    exact hedge.2.2.symm

end DeletionGraph.ConflictRules
namespace DeletionGraph.BoundedWitness
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem bad_not_colorable (n k t b L r : ℕ) (ξ : HashSample α L r)
    (x : Word α n) (hx : Good n k t b ξ x)
    (hbad : ¬∃ color : {y : Word α n // Good n k t b ξ y} → Fin 2,
      ∀ y z, (conflictGraph n k t b ξ).Reachable ⟨x,hx⟩ y →
        (conflictGraph n k t b ξ).Reachable ⟨x,hx⟩ z →
        (conflictGraph n k t b ξ).Adj y z → color y ≠ color z) :
    ¬((conflictGraph n k t b ξ).connectedComponentMk ⟨x,hx⟩).toSimpleGraph.Colorable 2 := by
  classical
  let G := conflictGraph n k t b ξ
  let C := G.connectedComponentMk ⟨x,hx⟩
  rintro ⟨color⟩
  let full : {y : Word α n // Good n k t b ξ y} → Fin 2 :=
    fun y => if hy : y ∈ C then color ⟨y,hy⟩ else 0
  apply hbad
  refine ⟨full,?_⟩
  intro y z hy hz hadj
  have hyC : y ∈ C := SimpleGraph.ConnectedComponent.sound hy.symm
  have hzC : z ∈ C := SimpleGraph.ConnectedComponent.sound hz.symm
  have hne := color.valid (show C.toSimpleGraph.Adj ⟨y,hyC⟩ ⟨z,hzC⟩ from hadj)
  simpa only [full,dif_pos hyC,dif_pos hzC] using hne

theorem bounded (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (hr : 1 ≤ r) (ξ : HashSample α L r) (x : Word α n)
    (hbad : BadComponent n k t b ξ x) :
    ∃ R : ℕ, ∃ G : Fin R → Spectrum α L,
      GeneratingSequence k t b (spectrum L (letters x)) G ∧
      (∀ j, Survives k t b ξ (G j)) ∧
      2 ≤ R ∧ R ≤ witnessBound t b L ∧ componentCount (ruleSet G) ≤ (2*t-1)*R+1 ∧
      (R ≤ L → componentCount (ruleSet G) ≤ (2*t-1)*R) := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  letI : Nonempty α := Fintype.card_pos_iff.mp (by have h:=hreg.1;omega)
  obtain ⟨hx,hbad⟩ := hbad
  have hn := bad_not_colorable n k t b L r ξ x hx hbad
  obtain ⟨m,hodd,verts,hstart,hend,hadj⟩ := OddGraphWalk.component_odd_walk
    (G := conflictGraph n k t b ξ) ⟨x,hx⟩ hn
  let p : Fin (m+1) → Spectrum α L := fun j => spectrum L (letters (verts j).val)
  let K : Set (Spectrum α L) := {w | Survives k t b ξ w}
  have hp : ∀ j, GeneratingScan.Boolean (p j) := by
    intro j
    have huniq : IsUnique (L-1) (letters (verts j).val) :=
      ExceptionalProbability.unique_mono (k := k) (verts j).val
        (by have h:=hreg.2.2.2.2.1; omega) (verts j).property.1
    exact (DeletionHash.MixedEdit.spectrum_simple_path n L hreg.1
      (by have hk:=hreg.2.2.2.1; have hL:=hreg.2.2.2.2.1; omega)
      hreg.2.2.2.2.2.2 (verts j).val huniq).1
  have hclosed : p 0=p (Fin.last m) := by simp only [p,hstart,hend]
  have hsurv : ∀ i : Fin m, Survives k t b ξ (SelectedRules.step p i) := by
    intro i
    exact ConflictRules.edge_rule n t b k L r hreg ξ (verts i.castSucc) (verts i.succ) (hadj i)
  obtain ⟨U,hU⟩ := WitnessWalk.extract n t b k L hreg p K hp hclosed hodd
    (fun i => (hsurv i).1) hsurv
  have hbase : p 0=spectrum L (letters x) := by simp only [p,hstart]
  rw [hbase] at hU
  obtain ⟨G,hgen,hset⟩ := GeneratingOrder.mission_enumeration (spectrum L (letters x)) U
    hU.generating hU.catalogue
  refine ⟨U.card,G,hgen,?_,hU.size_lower,hU.size_upper,?_,?_⟩
  · intro j
    have hmem : G j ∈ U := by
      rw [←hset]
      unfold ruleSet
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    exact hU.surviving (G j) hmem
  · rw [hset]
    exact hU.components
  · rw [hset]
    exact hU.small_components

end DeletionGraph.BoundedWitness
open DeletionHash.MixedEdit

universe u

/-- Lemma 4.6: survival, generation, both component bounds, and the exact size bound. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L) (hr : 1 ≤ r)
    (ξ : HashSample α L r) (x : Word α n) (hbad : BadComponent n k t b ξ x) :
    ∃ R : ℕ, ∃ G : Fin R → Spectrum α L,
      GeneratingSequence k t b (spectrum L (letters x)) G ∧ (∀ j, Survives k t b ξ (G j)) ∧
      2 ≤ R ∧ R ≤ witnessBound t b L ∧ componentCount (ruleSet G) ≤ (2*t-1)*R+1 ∧
      (R ≤ L → componentCount (ruleSet G) ≤ (2*t-1)*R) := by exact DeletionGraph.BoundedWitness.bounded n t b k L r hreg hr ξ x hbad



#print axioms solution
