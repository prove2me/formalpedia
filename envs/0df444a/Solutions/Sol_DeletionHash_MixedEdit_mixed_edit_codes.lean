-- Prove2me | solution 1 for DeletionHash.MixedEdit.mixed_edit_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:33:48.003791+00:00
-- url     : https://prove2.me/submissions/51cdabd2-bbb1-4263-b0d5-d9f9a48a7772

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_Channel
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
import Definitions.Def_DeletionHash_MixedEdit_Edits
import Definitions.Def_DeletionHash_MixedEdit_Generation
import Definitions.Def_DeletionHash_MixedEdit_Labels
import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_Rules
import Definitions.Def_DeletionHash_MixedEdit_SourceTrace
import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum


/-!
The deterministic selection at the end of the manuscript. The vertices in
bipartite connected components admit a coherent two-coloring, constructed
by choosing a coloring for each component. One global color class contains
at least half those vertices and is independent. A separate finite-fiber
argument retains at least a 1/Q fraction in one label class.
-/
namespace DeletionGeneralization.BipartiteSelection

open SimpleGraph
open scoped BigOperators

/-- The finite pigeonhole bound in multiplication form, without rounding.
The selected label exists even when I is empty. -/
theorem exists_large_label_fiber {V : Type*} {Q : ℕ} (I : Finset V)
    (label : V → Fin Q) (hQ : 1 ≤ Q) :
    ∃ a : Fin Q, I.card ≤ Q * (I.filter (fun v => label v = a)).card := by
  classical
  have hne : (Finset.univ : Finset (Fin Q)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin Q))
    (fun b => (I.filter (fun v => label v = b)).card) hne
  refine ⟨a, ?_⟩
  calc
    I.card = ∑ b : Fin Q, (I.filter (fun v => label v = b)).card := by
      symm
      simpa only [Finset.mem_univ, Finset.filter_true] using
        Finset.sum_card_fiberwise_eq_card_filter I (Finset.univ : Finset (Fin Q)) label
    _ ≤ ∑ _b : Fin Q, (I.filter (fun v => label v = a)).card :=
      Finset.sum_le_sum (fun b hb => ha b hb)
    _ = _ := by simp

variable {V : Type*} (G : SimpleGraph V)

/-- A vertex is retained at this stage exactly when its whole component is bipartite. -/
def Good (v : V) : Prop := (G.connectedComponentMk v).toSimpleGraph.Colorable 2

/-- Choose one coloring per bipartite component. The fallback value on other
components is unused by the independent-set construction. -/
noncomputable def componentColor (C : G.ConnectedComponent) : C → Fin 2 := by
  classical
  exact if h : C.toSimpleGraph.Colorable 2 then fun v => h.some v else fun _ => 0

theorem componentColor_valid (C : G.ConnectedComponent) (hC : C.toSimpleGraph.Colorable 2)
    {v w : C} (hvw : C.toSimpleGraph.Adj v w) :
    componentColor G C v ≠ componentColor G C w := by
  classical
  simpa only [componentColor, dif_pos hC] using hC.some.valid hvw

/-- The same component choice is used at every vertex in that component. -/
noncomputable def color (v : V) : Fin 2 :=
  componentColor G (G.connectedComponentMk v) ⟨v, rfl⟩

theorem color_eq_component (C : G.ConnectedComponent) (v : V) (hv : v ∈ C) :
    color G v = componentColor G C ⟨v, hv⟩ := by
  change G.connectedComponentMk v = C at hv
  subst C
  rfl

/-- Adjacent retained vertices receive different colors; no coloring of
the nonbipartite components is assumed. -/
theorem good_color_valid {v w : V} (hv : Good G v) (hvw : G.Adj v w) :
    color G v ≠ color G w := by
  let C := G.connectedComponentMk v
  have hvC : v ∈ C := rfl
  have hwC : w ∈ C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hvw).symm
  rw [color_eq_component G C v hvC, color_eq_component G C w hwC]
  exact componentColor_valid G C hv (show C.toSimpleGraph.Adj ⟨v, hvC⟩ ⟨w, hwC⟩ from hvw)

/-- The induced graph on all retained components is two-colorable. -/
theorem good_graph_colorable : (G.induce {v | Good G v}).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => color G v.val) ?_⟩
  intro v w hvw
  exact good_color_valid G v.property hvw

variable [Fintype V]

noncomputable def goodVertices : Finset V := by
  classical
  exact Finset.univ.filter (Good G)

@[simp] theorem mem_goodVertices (v : V) : v ∈ goodVertices G ↔ Good G v := by
  classical
  simp only [goodVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- At least half of all vertices in bipartite components can be selected
as one independent set. Component colorings and the large fiber are derived. -/
theorem exists_independent_good :
    ∃ I : Finset V, (∀ v ∈ I, Good G v) ∧ G.IsIndepSet (I : Set V) ∧
      (goodVertices G).card ≤ 2 * I.card := by
  classical
  obtain ⟨a, ha⟩ := exists_large_label_fiber (goodVertices G) (color G) (by decide)
  refine ⟨(goodVertices G).filter (fun v => color G v = a), ?_, ?_, ha⟩
  · intro v hv
    exact (mem_goodVertices G v).mp (Finset.mem_filter.mp hv).1
  · intro v hv w hw _ hvw
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    exact good_color_valid G ((mem_goodVertices G v).mp hv'.1) hvw
      (hv'.2.trans hw'.2.symm)


end DeletionGeneralization.BipartiteSelection
namespace DeletionGeneralization.CodeSelection
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] {n k L t b r : ℕ}

noncomputable def retained (ξ : HashSample α L r) : Finset (Word α n) := by
  classical
  exact Finset.univ.filter (fun x => IsUnique k (letters x) ∧
    ¬ (Exceptional n k t b ξ x ∨ BadComponent n k t b ξ x))

theorem component_good (ξ : HashSample α L r)
    (x : {x : Word α n // Good n k t b ξ x})
    (hx : ¬ BadComponent n k t b ξ x.val) :
    BipartiteSelection.Good (conflictGraph n k t b ξ) x := by
  classical
  have hc : ∃ color : {y : Word α n // Good n k t b ξ y} → Fin 2,
      ∀ y z, (conflictGraph n k t b ξ).Reachable x y →
        (conflictGraph n k t b ξ).Reachable x z →
        (conflictGraph n k t b ξ).Adj y z → color y ≠ color z := by
    by_contra hn
    exact hx ⟨x.property, hn⟩
  obtain ⟨color,hcolor⟩ := hc
  let C := (conflictGraph n k t b ξ).connectedComponentMk x
  refine ⟨SimpleGraph.Coloring.mk (fun y : C => color y.val) ?_⟩
  intro y z hyz
  exact hcolor y.val z.val (C.reachable_of_mem_supp rfl y.property)
    (C.reachable_of_mem_supp rfl z.property) hyz

theorem exists_code (ξ : HashSample α L r) :
    ∃ code : Finset (Word α n), Corrects b t code ∧
      (retained (n:=n) (k:=k) (t:=t) (b:=b) ξ).card ≤ 2 * 2^r * code.card := by
  classical
  let V := {x : Word α n // Good n k t b ξ x}
  letI : Fintype V := Fintype.ofFinite V
  let G := conflictGraph n k t b ξ
  have hret : (retained (n:=n) (k:=k) (t:=t) (b:=b) ξ).card ≤
      (BipartiteSelection.goodVertices G).card := by
    let S := retained (n:=n) (k:=k) (t:=t) (b:=b) ξ
    let f : {x // x ∈ S} → V := fun x =>
      ⟨x.val, (Finset.mem_filter.mp x.property).2.1,
        fun he => (Finset.mem_filter.mp x.property).2.2 (Or.inl he)⟩
    have hmap : ∀ x : {x // x ∈ S}, f x ∈ BipartiteSelection.goodVertices G := by
      intro x
      apply (BipartiteSelection.mem_goodVertices G _).mpr
      exact component_good ξ _ (fun hb => (Finset.mem_filter.mp x.property).2.2 (Or.inr hb))
    have hi : Function.Injective f := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : V => z.val) he)
    calc
      S.card = S.attach.card := (Finset.card_attach (s:=S)).symm
      _ ≤ (BipartiteSelection.goodVertices G).card :=
        Finset.card_le_card_of_injOn f (fun x _ => hmap x) (hi.injOn)
  obtain ⟨I,_,hind,hhalf⟩ := BipartiteSelection.exists_independent_good G
  have hcardLabel : Fintype.card (Label r) = 2^r := by simp [Label, ZMod.card]
  let e : Label r ≃ Fin (2^r) := (Fintype.equivFin (Label r)).trans (finCongr hcardLabel)
  let label : V → Fin (2^r) := fun v => e (hash ξ (spectrum L (letters v.val)))
  obtain ⟨a,ha⟩ := BipartiteSelection.exists_large_label_fiber I label (Nat.succ_le_of_lt (pow_pos (by decide : 0<(2:ℕ)) r))
  let J := I.filter (fun v => label v = a)
  let code := J.image Subtype.val
  have hcard : code.card = J.card := Finset.card_image_of_injective _ Subtype.val_injective
  refine ⟨code, ?_, ?_⟩
  · intro x hx y hy hxy hconf
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hv' := Finset.mem_filter.mp hv
    have hw' := Finset.mem_filter.mp hw
    have hne : v ≠ w := fun he => hxy (congrArg Subtype.val he)
    apply hind hv'.1 hw'.1 hne
    exact ⟨hne,hconf,e.injective (hv'.2.trans hw'.2.symm)⟩
  · rw [hcard, Nat.mul_assoc]
    exact hret.trans (hhalf.trans (Nat.mul_le_mul_left 2 ha))

end DeletionGeneralization.CodeSelection
namespace DeletionGeneralization.FiniteAverage
open DeletionHash.MixedEdit
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem probability_sum {Ω : Type u} [Fintype Ω] (P : Ω → Prop) :
    uniformProbability P = (∑ ω : Ω, if P ω then (1:ℝ) else 0) / Fintype.card Ω := by
  classical
  simp [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem half_retained {Ω : Type u} [Fintype Ω] [Nonempty Ω]
    {V : Type v} (s : Finset V) (E : V → Ω → Prop)
    (hE : ∀ v ∈ s, uniformProbability (E v) ≤ (1:ℝ)/3) :
    ∃ ω, s.card ≤ 2 * (s.filter (fun v => ¬ E v ω)).card := by
  classical
  have hΩ : (0:ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hupper : (∑ ω : Ω, ((s.filter (fun v => E v ω)).card : ℝ)) ≤
      (s.card:ℝ) * Fintype.card Ω / 3 := by
    calc
      _ = ∑ v ∈ s, ∑ ω : Ω, if E v ω then (1:ℝ) else 0 := by
        simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        rw [Finset.sum_comm]
      _ ≤ ∑ _v ∈ s, (Fintype.card Ω:ℝ)/3 := by
        apply Finset.sum_le_sum
        intro v hv
        have h := hE v hv
        rw [probability_sum, div_le_iff₀ hΩ] at h
        linarith
      _ = _ := by simp; ring
  by_contra hnone
  have hpoint (ω : Ω) : (s.card:ℝ) < 2 * (s.filter (fun v => E v ω)).card := by
    have hn : ¬ s.card ≤ 2 * (s.filter (fun v => ¬ E v ω)).card := fun h => hnone ⟨ω,h⟩
    have hp := Finset.card_filter_add_card_filter_not (s := s) (fun v => E v ω)
    have h : s.card < 2 * (s.filter (fun v => E v ω)).card := by omega
    exact_mod_cast h
  have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset Ω))
    Finset.univ_nonempty (fun ω _ => hpoint ω)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hs : (0:ℝ) ≤ s.card := Nat.cast_nonneg _
  nlinarith

end DeletionGeneralization.FiniteAverage
/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGeneralization.OverlapCollision
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

end DeletionGeneralization.OverlapCollision

/-!
A finite union bound over actual pairs of distinct ordered positions a < b.
Their number is derived by an explicit equivalence with a triangular sigma
type; no pair-count or union-cardinality inequality is assumed.
-/
namespace DeletionGeneralization.FinitePairUnion

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

end DeletionGeneralization.FinitePairUnion
namespace DeletionGeneralization.UniqueWordCount
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

end DeletionGeneralization.UniqueWordCount
namespace DeletionGeneralization.UniqueBridge
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

end DeletionGeneralization.UniqueBridge
namespace DeletionGeneralization.UniqueMass
open DeletionHash.MixedEdit
universe u

private theorem length_eq_clog (q n : ℕ) : uniqueLength q n = 2 * Nat.clog q n + 2 := by
  change 2 * ⌈Real.logb (q : ℝ) (n : ℝ)⌉₊ + 2 = _
  rw [Real.natCeil_logb_natCast]

private theorem eight_choose_le (q n : ℕ) (hq : 2 ≤ q) :
    8 * n.choose 2 ≤ q ^ uniqueLength q n := by
  have hn := Nat.le_pow_clog (show 1<q by omega) n
  have hsq := Nat.mul_le_mul hn hn
  have hchoose : 2 * n.choose 2 ≤ n^2 := by
    rw [Nat.choose_two_right]
    have hdiv := Nat.div_mul_le_self (n * (n-1)) 2
    have hmul := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    nlinarith
  have hq2 : 4 ≤ q^2 := by nlinarith
  have hpow : q ^ uniqueLength q n = (q ^ Nat.clog q n)^2 * q^2 := by
    rw [length_eq_clog, pow_add, show 2 * Nat.clog q n = Nat.clog q n * 2 by omega, pow_mul]
  calc
    8 * n.choose 2 ≤ 4 * n^2 := by omega
    _ ≤ 4 * (q ^ Nat.clog q n)^2 := by nlinarith
    _ ≤ (q ^ Nat.clog q n)^2 * q^2 := by nlinarith
    _ = q ^ uniqueLength q n := hpow.symm

theorem mass {α : Type u} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ Fintype.card α) :
    let q := Fintype.card α
    let k := uniqueLength q n
    let B := (1 - (n.choose 2 : ℝ) / (q : ℝ)^k) * (q : ℝ)^n
    (B ≤ ((uniqueFamily α n k).card : ℝ)) ∧
    ((7:ℝ)/8 * (q : ℝ)^n ≤ B) ∧ ((q : ℝ)^n/2 ≤ (7:ℝ)/8 * (q : ℝ)^n) := by
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  dsimp
  have hk : 1 ≤ uniqueLength (Fintype.card α) n := by unfold uniqueLength; omega
  have hqpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast (show 0 < Fintype.card α by omega)
  have hp : (0 : ℝ) < (Fintype.card α : ℝ)^uniqueLength (Fintype.card α) n := pow_pos hqpos _
  have hscaled : (8 : ℝ) * n.choose 2 ≤ (Fintype.card α : ℝ)^uniqueLength (Fintype.card α) n := by
    exact_mod_cast eight_choose_le (Fintype.card α) n hq
  have hf : (n.choose 2 : ℝ) / (Fintype.card α : ℝ)^uniqueLength (Fintype.card α) n ≤ 1/8 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [DeletionGeneralization.UniqueBridge.family_eq]
    exact DeletionGeneralization.UniqueWordCount.card_unique_lower_bound_real α n _ hk
  · apply mul_le_mul_of_nonneg_right _ (le_of_lt (pow_pos hqpos n))
    linarith
  · have hnonneg := le_of_lt (pow_pos hqpos n)
    nlinarith

end DeletionGeneralization.UniqueMass
namespace DeletionGeneralization.HashUniform
open DeletionHash.MixedEdit
universe u v
variable {ι : Type u} [Fintype ι] {R r : ℕ}

noncomputable def evaluation (v : Fin R → (ι → ZMod 2)) :
    (ι → Label r) →ₗ[ZMod 2] (Fin R → Label r) :=
  LinearMap.pi (fun i => ∑ g, v i g • LinearMap.proj g)

theorem evaluation_apply (v : Fin R → (ι → ZMod 2)) (ξ : ι → Label r) (i : Fin R) :
    evaluation v ξ i = ∑ g, v i g • ξ g := by
  simp [evaluation]

theorem evaluation_surjective (v : Fin R → (ι → ZMod 2))
    (hv : LinearIndependent (ZMod 2) v) : Function.Surjective (evaluation (r := r) v) := by
  classical
  let f := Fintype.linearCombination (ZMod 2) v
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
  intro a
  let h : (ι → ZMod 2) →ₗ[ZMod 2] Label r :=
    (Fintype.linearCombination (ZMod 2) a).comp g
  have hvh : ∀ i, h (v i) = a i := by
    intro i
    have he := LinearMap.congr_fun hg (Pi.single i 1)
    have hi : f (Pi.single i 1) = v i := by
      simp [f, Fintype.linearCombination_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hi] at he
    simp [h, he, Fintype.linearCombination_apply]
  refine ⟨fun j => h (Pi.single j 1), ?_⟩
  funext i
  rw [evaluation_apply, ← hvh i]
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply, mul_ite]

theorem uniform_fiber {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (hf : Function.Surjective f) (a : W) :
    uniformProbability (fun x => f x = a) = 1 / (Fintype.card W : ℝ) := by
  classical
  have heq : ∀ y : W, Fintype.card {x : V // f x = y} = Fintype.card {x : V // f x = a} := by
    intro y
    simpa only [Fintype.card_subtype] using
      (AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf a))
  have hc : Fintype.card V = Fintype.card W * Fintype.card {x : V // f x = a} := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    simpa only [Fintype.card_sigma, heq, Finset.sum_const, Finset.card_univ, smul_eq_mul] using h.symm
  have hn : 0 < Fintype.card {x : V // f x = a} := by
    obtain ⟨x,hx⟩ := hf a
    exact Fintype.card_pos_iff.mpr ⟨⟨x,hx⟩⟩
  unfold uniformProbability
  rw [Nat.card_eq_fintype_card, hc, Nat.cast_mul]
  have hne : (Fintype.card {x : V // f x = a} : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp


theorem joint {α : Type u} [Fintype α] [DecidableEq α] {L r R : ℕ}
    (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) (a : Fin R → Label r) :
    uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      1 / ((2 : ℝ)^r)^R := by
  classical
  have he : (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      (fun ξ => evaluation (fun i => parity (w i)) ξ = a) := by
    funext ξ
    simp only [funext_iff, evaluation_apply, DeletionHash.MixedEdit.hash]
  rw [he]
  have h := uniform_fiber (evaluation (r := r) (fun i => parity (w i))).toAddMonoidHom
    (evaluation_surjective _ hw) a
  simpa [Label, Fintype.card_fun, ZMod.card] using h

theorem single {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (v : Spectrum α L) (hv : parity v ≠ 0) :
    uniformProbability (fun ξ : HashSample α L r => hash ξ v = 0) = 1 / (2 : ℝ)^r := by
  have hi : LinearIndependent (ZMod 2) (fun _ : Fin 1 => parity v) := by
    rw [linearIndependent_unique_iff]
    exact hv
  simpa using joint (r := r) (fun _ : Fin 1 => v) hi (fun _ => 0)

end DeletionGeneralization.HashUniform
namespace DeletionGeneralization.WordPaths
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

end DeletionGeneralization.WordPaths
namespace DeletionGeneralization.SpectrumPath
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

end DeletionGeneralization.SpectrumPath

namespace DeletionGeneralization.Parity
open DeletionHash.MixedEdit SpectrumPath UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem distinguishes {n L : ℕ} (x z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hx : IsUnique (L-1) (letters x)) (hne : z ≠ x) :
    parity (spectrum L (letters z) - spectrum L (letters x)) ≠ 0 := by
  intro hp
  have hlarge : IsUnique L (letters x) := (unique_iff x).mpr (by
    have hsmall := (unique_iff x).mp hx
    intro a b ha hb hab
    apply hsmall a b (by omega) (by omega)
    intro i hi
    exact hab i (by omega))
  have hsupp : ∀ g : Gram α L, List.ofFn g ∈ windows L (letters x) →
      List.ofFn g ∈ windows L (letters z) := by
    intro g hg
    have hx0 := (nonzero_iff_mem L (letters x) g).mpr hg
    have hx1 : spectrum L (letters x) g = 1 := (spectrum_boolean x hx g).resolve_left hx0
    apply (nonzero_iff_mem L (letters z) g).mp
    intro hz0
    have h := congrFun hp g
    change ((spectrum L (letters z) g - spectrum L (letters x) g : ℤ) : ZMod 2) = 0 at h
    rw [hz0, hx1] at h
    norm_num at h
  have hsub : windows L (letters x) ⊆ windows L (letters z) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    have hab : a+L ≤ n := by
      simp only [starts, letters, List.length_ofFn, List.mem_range, if_pos hn] at ha
      omega
    rw [window_as_ofFn x hab]
    apply hsupp
    exact (windows_mem_iff x _).mpr ⟨a, hab, window_as_ofFn x hab⟩
  have hperm := (List.Nodup.subperm hlarge hsub).perm_of_length_le (by
    simp only [windows, starts, letters, List.length_map, List.length_range, List.length_ofFn, le_refl])
  apply hne
  apply recovers x z hL hn hx
  funext g
  unfold DeletionHash.MixedEdit.spectrum
  exact_mod_cast (hperm.count_eq (List.ofFn g)).symm

end DeletionGeneralization.Parity

/-!
Counting tuples with an anchor near an endpoint or another anchor. The count
removes one coordinate, records the remaining tuple, and reconstructs the
omitted entry. Each distance constraint allows at most `2 * B` entries.
The right endpoint test is distance to `m`, so no bound on the anchors by `m`
is required. All cardinalities count actual tuples, including repeated anchors.
-/

namespace DeletionGeneralization.ClosePositions

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An endpoint-near or mutually close tuple of anchors. -/
def Bad {r n : ℕ} (m B : ℕ) (a : Fin r → Fin n) : Prop :=
  (∃ i, (a i).val < B) ∨
  (∃ i, Nat.dist (a i).val m < B) ∨
  (∃ i j, i ≠ j ∧ Nat.dist (a i).val (a j).val < B)

/-- A natural-number ball, intersected with `Fin n`, contains at most `2 * B` points. -/
theorem near_card_le (n c B : ℕ) :
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤ 2 * B := by
  calc
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤
        (range (2 * B)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin n => x.val + B - c)
      · intro x hx
        have hd := (mem_filter.mp hx).2
        change x.val + B - c ∈ range (2 * B)
        rw [mem_range]
        unfold Nat.dist at hd
        omega
      · intro x hx y hy heq
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        change x.val + B - c = y.val + B - c at heq
        unfold Nat.dist at hx' hy'
        apply Fin.ext
        omega
    _ = 2 * B := card_range _

/-- Omitting one coordinate leaves exactly `n^r` possible records; each record
admits at most `M` values of the omitted coordinate. -/
theorem coordinate_constraint_card_le {r n : ℕ} (i : Fin (r + 1))
    (P : (Fin r → Fin n) → Fin n → Prop) (M : ℕ)
    (hM : ∀ b, (univ.filter (P b)).card ≤ M) :
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
      M * n ^ r := by
  let fibers : (Fin r → Fin n) → Finset (Fin (r + 1) → Fin n) :=
    fun b => (univ.filter (P b)).image (fun x => i.insertNth x b)
  have hcover :
      univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i)) ⊆
        (univ : Finset (Fin r → Fin n)).biUnion fibers := by
    intro a ha
    apply mem_biUnion.mpr
    refine ⟨i.removeNth a, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨a i, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩, ?_⟩
    exact Fin.insertNth_self_removeNth i a
  calc
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
        ((univ : Finset (Fin r → Fin n)).biUnion fibers).card := card_le_card hcover
    _ ≤ (univ : Finset (Fin r → Fin n)).card * M :=
      card_biUnion_le_card_mul _ fibers M (fun b _ => (card_image_le).trans (hM b))
    _ = M * n ^ r := by simp [Nat.mul_comm]

/-- The reference point may depend on every coordinate except the constrained one. -/
theorem coordinate_near_card_le {r n : ℕ} (i : Fin (r + 1))
    (c : (Fin r → Fin n) → ℕ) (B : ℕ) :
    (univ.filter (fun a : Fin (r + 1) → Fin n =>
      Nat.dist (a i).val (c (i.removeNth a)) < B)).card ≤ (2 * B) * n ^ r := by
  have h := coordinate_constraint_card_le i (fun b x => Nat.dist x.val (c b) < B) (2 * B)
    (fun b => by
      apply le_of_eq_of_le ?_ (near_card_le n (c b) B)
      apply congrArg Finset.card
      ext x
      simp only [mem_filter, mem_univ, true_and])
  apply le_of_eq_of_le ?_ h
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and]

private abbrev EventIndex (r : ℕ) := Fin r × (Fin r ⊕ Bool)

private def Event {r n : ℕ} (m B : ℕ) (q : EventIndex r) (a : Fin r → Fin n) : Prop :=
  match q.2 with
  | .inl j => q.1 ≠ j ∧ Nat.dist (a q.1).val (a j).val < B
  | .inr false => (a q.1).val < B
  | .inr true => Nat.dist (a q.1).val m < B

private theorem event_card_le {r n : ℕ} (m B : ℕ) (q : EventIndex (r + 1)) :
    (univ.filter (Event (n := n) m B q)).card ≤ (2 * B) * n ^ r := by
  rcases q with ⟨i, s⟩
  cases s with
  | inl j =>
      by_cases hij : i = j
      · have hempty : univ.filter (Event (n := n) m B (i, .inl j)) = ∅ := by
          ext a
          simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty]
          change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔ False
          simp [hij]
        rw [hempty, card_empty]
        exact Nat.zero_le _
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
        apply le_of_eq_of_le ?_
          (coordinate_near_card_le (n := n) i (fun b => (b j').val) B)
        apply congrArg Finset.card
        ext a
        simp only [mem_filter, mem_univ, true_and]
        change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔
          Nat.dist (a i).val (a (i.succAbove j')).val < B
        rw [hj']
        exact ⟨And.right, fun h => ⟨hij, h⟩⟩
  | inr b =>
      cases b with
      | false =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => 0) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          change (a i).val < B ↔ Nat.dist (a i).val 0 < B
          rw [Nat.dist_zero_right]
      | true =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => m) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          rfl

/-- A union bound over all actual endpoint and pair constraints. The exponent
is `r - 1`, and the theorem also covers `r = 0`, `n = 0`, and `B = 0`. -/
theorem bad_card_le (r n m B : ℕ) :
    (univ.filter (Bad (r := r) (n := n) m B)).card ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) := by
  cases r with
  | zero => simp [Bad]
  | succ r =>
      let events : EventIndex (r + 1) → Finset (Fin (r + 1) → Fin n) :=
        fun q => univ.filter (Event m B q)
      have hcover : univ.filter (Bad (r := r + 1) (n := n) m B) =
          (univ : Finset (EventIndex (r + 1))).biUnion events := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_biUnion, events]
        constructor
        · rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hd⟩)
          · exact ⟨(i, .inr false), hi⟩
          · exact ⟨(i, .inr true), hi⟩
          · exact ⟨(i, .inl j), hij, hd⟩
        · rintro ⟨⟨i, s⟩, h⟩
          cases s with
          | inl j => exact Or.inr (Or.inr ⟨i, j, h⟩)
          | inr b =>
              cases b with
              | false => exact Or.inl ⟨i, h⟩
              | true => exact Or.inr (Or.inl ⟨i, h⟩)
      rw [hcover]
      calc
        ((univ : Finset (EventIndex (r + 1))).biUnion events).card ≤
            (univ : Finset (EventIndex (r + 1))).card * ((2 * B) * n ^ r) :=
          card_biUnion_le_card_mul _ events _ (fun q _ => event_card_le m B q)
        _ = (r + 1) * (r + 1 + 2) * (2 * B) * n ^ (r + 1 - 1) := by
          simp [EventIndex, Fintype.card_prod, Fintype.card_sum, Nat.mul_assoc]


end

end DeletionGeneralization.ClosePositions
namespace DeletionGeneralization.RecordCount
open DeletionHash.MixedEdit
universe u
variable (α : Type u) [Fintype α] [DecidableEq α]

abbrev Tag (b : ℕ) := Fin (b+1) × (Σ l : Fin (b+1), Fin l.val → α)
abbrev Record (b N r : ℕ) := (Fin r → Fin N) × (Fin r → Tag α b)

def decode {b N r : ℕ} (rec : Record α b N r) : List (Edit α) :=
  List.ofFn fun i => ⟨(rec.1 i).val, (rec.2 i).1.val, List.ofFn (rec.2 i).2.2⟩

theorem tag_card_le (b : ℕ) (hq : 1 ≤ Fintype.card α) :
    Fintype.card (Tag α b) ≤ (b+1)^2 * (Fintype.card α)^b := by
  classical
  simp only [Tag, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma, Fintype.card_fun]
  calc
    (b+1) * (∑ l : Fin (b+1), (Fintype.card α)^l.val) ≤
      (b+1) * (∑ _l : Fin (b+1), (Fintype.card α)^b) := by
        gcongr with l
        omega
    _ = (b+1)^2 * (Fintype.card α)^b := by simp; ring

theorem record_card (b N r : ℕ) :
    Fintype.card (Record α b N r) = N^r * (Fintype.card (Tag α b))^r := by
  simp [Record, Fintype.card_fun]

theorem bad_record_card_le (b N r n B : ℕ) :
    Nat.card {rec : Record α b N r // ClosePositions.Bad n B rec.1} ≤
      r*(r+2)*(2*B)*N^(r-1)*(Fintype.card (Tag α b))^r := by
  classical
  let e : {rec : Record α b N r // ClosePositions.Bad n B rec.1} ≃
      {a : Fin r → Fin N // ClosePositions.Bad n B a} × (Fin r → Tag α b) :=
    { toFun := fun rec => (⟨rec.val.1,rec.property⟩,rec.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin]
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_subtype] using ClosePositions.bad_card_le r N n B

theorem edited_length_le (b : ℕ) (x : List α) (e : Edit α) (he : ValidEdit b x e) :
    (applyEdit e x).length ≤ x.length+b := by
  have h1 := he.1
  have h2 := he.2.2.1
  simp only [applyEdit, List.length_append, List.length_take, List.length_drop]
  omega

theorem record_bounds (b : ℕ) (x : List α) (es : List (Edit α)) (he : ValidRecord b x es) :
    ∀ e ∈ es, e.position ≤ x.length+es.length*b ∧
      e.removed ≤ b ∧ e.replacement.length ≤ b := by
  induction es generalizing x with
  | nil => simp
  | cons e es ih =>
    obtain ⟨he,hes⟩ := he
    have hlen := edited_length_le α b x e he
    have hpos := he.1
    have htail := ih (applyEdit e x) hes
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by simp only [List.length_cons]; omega, he.2.1, he.2.2.1⟩
    · obtain ⟨hp,hr,hl⟩ := htail f hf
      refine ⟨?_,hr,hl⟩
      simp only [List.length_cons]
      nlinarith

theorem encode_exists (b N : ℕ) (es : List (Edit α))
    (he : ∀ e ∈ es, e.position < N ∧ e.removed ≤ b ∧ e.replacement.length ≤ b) :
    ∃ rec : Record α b N es.length, decode α rec = es := by
  let positions : Fin es.length → Fin N := fun i =>
    ⟨(es.get i).position, (he (es.get i) (List.get_mem es i)).1⟩
  let tags : Fin es.length → Tag α b := fun i =>
    (⟨(es.get i).removed, by have h := (he (es.get i) (List.get_mem es i)).2.1; omega⟩,
     ⟨⟨(es.get i).replacement.length, by have h := (he (es.get i) (List.get_mem es i)).2.2; omega⟩,
      fun j => (es.get i).replacement.get j⟩)
  refine ⟨(positions,tags), ?_⟩
  unfold decode
  conv_rhs => rw [← List.ofFn_get es]
  congr 1
  funext i
  simp [positions, tags]


theorem not_separated_bad (n t b L r : ℕ)
    (rec : Record α b (n+2*t*b+1) r) (hnot : ¬ Separated n t b L (decode α rec)) :
    ClosePositions.Bad n (8*(L+t*b)+2*t*b+1) rec.1 := by
  by_contra hbad
  apply hnot
  simp only [ClosePositions.Bad, not_or, not_exists, not_and, not_lt] at hbad
  constructor
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    change 8*(L+t*b) ≤ (rec.1 i).val ∧ (rec.1 i).val+8*(L+t*b) ≤ n
    have hl := hbad.1 i
    have hr := hbad.2.1 i
    have hb := (rec.1 i).isLt
    unfold Nat.dist at hr
    constructor <;> omega
  · intro i j hij
    let i' : Fin r := ⟨i.val, by simpa [decode] using i.isLt⟩
    let j' : Fin r := ⟨j.val, by simpa [decode] using j.isLt⟩
    have hne : i' ≠ j' := by
      intro h
      apply hij
      apply Fin.ext
      simpa only [i', j'] using congrArg (fun z : Fin r => z.val) h
    have h := hbad.2.2 i' j' hne
    have hh : 8*(L+t*b) ≤ Nat.dist (rec.1 i').val (rec.1 j').val := by omega
    change 8*(L+t*b) ≤ Nat.dist ((decode α rec).get i).position ((decode α rec).get j).position
    dsimp only [decode]
    erw [List.get_ofFn, List.get_ofFn]
    exact hh

def decodeWord {b N r n : ℕ} (x : Word α n) (rec : Record α b N r) : Word α n :=
  fun i => (target (letters x) (decode α rec)).getD i.val (x i)

theorem decodeWord_eq {b N r n : ℕ} (x z : Word α n) (rec : Record α b N r)
    (he : target (letters x) (decode α rec) = letters z) : decodeWord α x rec = z := by
  funext i
  change (target (letters x) (decode α rec)).getD i.val (x i) = z i
  rw [he]
  simp [letters, List.getD, i.isLt]

noncomputable def shortPartners {n : ℕ} (t b : ℕ) (x : Word α n) : Finset (Word α n) := by
  classical
  exact (Finset.range (2*t)).biUnion fun r =>
    (Finset.univ : Finset (Record α b (n+2*t*b+1) r)).image (decodeWord α x)

noncomputable def fullPartners {n : ℕ} (t b L : ℕ) (x : Word α n) : Finset (Word α n) := by
  classical
  exact ((Finset.univ : Finset (Record α b (n+2*t*b+1) (2*t))).filter
    (fun rec => ClosePositions.Bad n (8*(L+t*b)+2*t*b+1) rec.1)).image (decodeWord α x)

theorem shortPartners_card_le {n : ℕ} (t b : ℕ) (x : Word α n) :
    (shortPartners α t b x).card ≤
      ∑ r ∈ Finset.range (2*t), (n+2*t*b+1)^r * (Fintype.card (Tag α b))^r := by
  classical
  unfold shortPartners
  apply le_trans Finset.card_biUnion_le
  apply Finset.sum_le_sum
  intro r hr
  exact Finset.card_image_le.trans (by simp [record_card])

theorem fullPartners_card_le {n : ℕ} (t b L : ℕ) (x : Word α n) :
    (fullPartners α t b L x).card ≤
      (2*t)*(2*t+2)*(2*(8*(L+t*b)+2*t*b+1))*(n+2*t*b+1)^(2*t-1)*
        (Fintype.card (Tag α b))^(2*t) := by
  classical
  unfold fullPartners
  apply Finset.card_image_le.trans
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    bad_record_card_le α b (n+2*t*b+1) (2*t) n (8*(L+t*b)+2*t*b+1)

theorem partners_cover {n : ℕ} (t b L : ℕ) (x z : Word α n) (es : List (Edit α))
    (hlen : es.length ≤ 2*t) (he : ValidRecord b (letters x) es)
    (hz : target (letters x) es = letters z)
    (hbad : es.length < 2*t ∨ ¬ Separated n t b L es) :
    z ∈ shortPartners α t b x ∪ fullPartners α t b L x := by
  classical
  have hb := record_bounds α b (letters x) es he
  obtain ⟨rec, hrec⟩ := encode_exists α b (n+2*t*b+1) es (by
    intro e he
    obtain ⟨hp,hr,hl⟩ := hb e he
    simp only [letters, List.length_ofFn] at hp
    have hmul := Nat.mul_le_mul_right b hlen
    exact ⟨by omega,hr,hl⟩)
  have hd := decodeWord_eq α x z rec (by rwa [hrec])
  by_cases hshort : es.length < 2*t
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨es.length, Finset.mem_range.mpr hshort, Finset.mem_image.mpr ⟨rec, Finset.mem_univ _, hd⟩⟩
  · have heq : es.length = 2*t := by omega
    obtain ⟨rec', hrec'⟩ : ∃ rec' : Record α b (n+2*t*b+1) (2*t), decode α rec'=es := by
      have aux : ∀ (r : ℕ), es.length=r → ∃ rec' : Record α b (n+2*t*b+1) r, decode α rec'=es := by
        intro r h
        subst r
        exact ⟨rec,hrec⟩
      exact aux (2*t) heq
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨rec', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, decodeWord_eq α x z rec' (by rwa [hrec'])⟩
    apply not_separated_bad α n t b L (2*t) rec'
    simpa only [hrec'] using hbad.resolve_left hshort


end DeletionGeneralization.RecordCount

namespace DeletionGeneralization.RecordArithmetic
open DeletionHash.MixedEdit RecordCount
universe u

def countConstant (t b : ℕ) : ℕ :=
  (2*t+(2*t)*(2*t+2)*(2*(9+10*t*b))) * (2*t*b+2)^(2*t-1) * (b+1)^(4*t)

theorem countConstant_pos (t b : ℕ) (ht : 1 ≤ t) : 0 < countConstant t b := by
  unfold countConstant
  positivity

theorem short_bound (N T R : ℕ) (hN : 1 ≤ N) (hT : 1 ≤ T) :
    (∑ r ∈ Finset.range R, N^r*T^r) ≤ R*T^R*N^(R-1) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range R, T^R*N^(R-1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr := Finset.mem_range.mp hr
      calc
        N^r*T^r ≤ N^(R-1)*T^R := by gcongr <;> omega
        _ = T^R*N^(R-1) := Nat.mul_comm _ _
    _ = R*T^R*N^(R-1) := by simp [Nat.mul_assoc]

theorem combined_bound (n t b L T q : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (htag : T ≤ (b+1)^2*q^b) :
    (∑ r ∈ Finset.range (2*t), (n+2*t*b+1)^r*T^r) +
      (2*t)*(2*t+2)*(2*(8*(L+t*b)+2*t*b+1))*(n+2*t*b+1)^(2*t-1)*T^(2*t) ≤
      countConstant t b * L * n^(2*t-1) * q^(2*b*t) := by
  let N := n+2*t*b+1
  let B := 8*(L+t*b)+2*t*b+1
  let K := 9+10*t*b
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hB : B ≤ K*L := by
    dsimp [B,K]
    have h := Nat.mul_le_mul_left (10*t*b) hL
    nlinarith
  have hN' : N ≤ (2*t*b+2)*n := by
    dsimp [N]
    have h := Nat.mul_le_mul_left (2*t*b+1) hn
    nlinarith
  have htag' : T^(2*t) ≤ (b+1)^(4*t)*q^(2*b*t) := by
    calc
      T^(2*t) ≤ ((b+1)^2*q^b)^(2*t) := Nat.pow_le_pow_left htag _
      _ = (b+1)^(4*t)*q^(2*b*t) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> ring
  have hs := short_bound N T (2*t) hN hT
  change (∑ r ∈ Finset.range (2*t), N^r*T^r) +
    (2*t)*(2*t+2)*(2*B)*N^(2*t-1)*T^(2*t) ≤ _
  calc
    _ ≤ (2*t)*T^(2*t)*N^(2*t-1) +
      (2*t)*(2*t+2)*(2*B)*N^(2*t-1)*T^(2*t) := Nat.add_le_add_right hs _
    _ ≤ (2*t)*L*T^(2*t)*N^(2*t-1) +
      (2*t)*(2*t+2)*(2*(K*L))*N^(2*t-1)*T^(2*t) := by
        apply Nat.add_le_add
        · have hR : 2*t ≤ 2*t*L := by simpa using Nat.mul_le_mul_left (2*t) hL
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR)
        · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left ((2*t)*(2*t+2)) (Nat.mul_le_mul_left 2 hB)))
    _ = (2*t+(2*t)*(2*t+2)*(2*K))*L*N^(2*t-1)*T^(2*t) := by ring
    _ ≤ (2*t+(2*t)*(2*t+2)*(2*K))*L*((2*t*b+2)*n)^(2*t-1)*
      ((b+1)^(4*t)*q^(2*b*t)) := by gcongr
    _ = countConstant t b * L * n^(2*t-1) * q^(2*b*t) := by
      rw [mul_pow]
      unfold countConstant K
      ring

theorem partners_card_le {α : Type u} [Fintype α] [DecidableEq α]
    {n : ℕ} (t b L : ℕ) (x : Word α n) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hq : 1 ≤ Fintype.card α) :
    (shortPartners α t b x ∪ fullPartners α t b L x).card ≤
      countConstant t b * L * n^(2*t-1) * (Fintype.card α)^(2*b*t) := by
  classical
  have ht : 1 ≤ Fintype.card (Tag α b) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(0, ⟨0, Fin.elim0⟩)⟩
  calc
    _ ≤ (shortPartners α t b x).card + (fullPartners α t b L x).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add (shortPartners_card_le α t b x) (fullPartners_card_le α t b L x)
    _ ≤ _ := combined_bound n t b L (Fintype.card (Tag α b)) (Fintype.card α)
      hn hL ht (tag_card_le α b hq)

end DeletionGeneralization.RecordArithmetic
namespace DeletionGeneralization.ExceptionalProbability
open DeletionHash.MixedEdit
universe u v

theorem probability_mono {Ω : Type u} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ x, P x → Q x) : uniformProbability P ≤ uniformProbability Q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_le_of_injective
    (fun x : {x // P x} => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
    (fun x y he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))

theorem probability_union {Ω : Type u} [Fintype Ω] {β : Type v}
    (S : Finset β) (P : β → Ω → Prop) :
    uniformProbability (fun x => ∃ z ∈ S, P z x) ≤ ∑ z ∈ S, uniformProbability (P z) := by
  classical
  let E : β → Finset Ω := fun z => Finset.univ.filter (P z)
  have he : Finset.univ.filter (fun x => ∃ z ∈ S, P z x) = S.biUnion E := by
    ext x
    simp [E]
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he]
  have hc : (S.biUnion E).card ≤ ∑ z ∈ S, (E z).card := Finset.card_biUnion_le
  calc
    ((S.biUnion E).card : ℝ) / Fintype.card Ω ≤
        ((∑ z ∈ S, (E z).card : ℕ) : ℝ) / Fintype.card Ω := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hc
    _ = _ := by simp only [Nat.cast_sum, Finset.sum_div, E]

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

theorem collision_bound {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {n L r : ℕ} (x z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hx : IsUnique (L-1) (letters x)) :
    uniformProbability (fun ξ : HashSample α L r =>
      z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) ≤
      1 / (2 : ℝ)^r := by
  classical
  by_cases hne : z=x
  · subst z
    simp [uniformProbability]
  · have hp := Parity.distinguishes x z hL hn hx hne
    have h := HashUniform.single (r := r) (spectrum L (letters z)-spectrum L (letters x)) hp
    simp only [hash_sub, sub_eq_zero] at h
    simpa [hne] using h.le


theorem exceptional_bound {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) :
    uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
      (RecordArithmetic.countConstant t b : ℝ) * (Fintype.card α : ℝ)^(2*b*t) *
        (L : ℝ) * (n : ℝ)^(2*t-1) / (2 : ℝ)^r := by
  classical
  obtain ⟨hq, ht, hb, hk, hL, hbk, hn⟩ := hreg
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hLpos : 1 ≤ L := by omega
  have hnx : 1 ≤ n := by omega
  have hxm : IsUnique (L-1) (letters x) := unique_mono x (by omega) hx
  let S := RecordCount.shortPartners α t b x ∪ RecordCount.fullPartners α t b L x
  have hcover : ∀ ξ : HashSample α L r, Exceptional n k t b ξ x →
      ∃ z ∈ S, z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x)) := by
    intro ξ hex
    obtain ⟨_, es, hlen, hvalid, hword, hne, hhash, hbad⟩ := hex
    let y := target (letters x) es
    let z : Word α n := fun i => y.getD i.val (x i)
    have hz : letters z = y := by
      apply List.ext_getElem
      · simp only [letters, List.length_ofFn]
        exact hword.symm
      · intro i hi hj
        simp only [letters, List.getElem_ofFn, z, List.getD,
          List.getElem?_eq_getElem hj, Option.getD_some]
    have hz' : target (letters x) es = letters z := hz.symm
    refine ⟨z, RecordCount.partners_cover α t b L x z es hlen hvalid hz' hbad, ?_, ?_⟩
    · intro heq
      apply hne
      rw [hz', heq]
    · simpa only [hz] using hhash
  have hcard : (S.card : ℝ) ≤
      (RecordArithmetic.countConstant t b : ℝ) * L * (n : ℝ)^(2*t-1) *
        (Fintype.card α : ℝ)^(2*b*t) := by
    exact_mod_cast RecordArithmetic.partners_card_le t b L x hnx hLpos (by omega)
  calc
    _ ≤ uniformProbability (fun ξ : HashSample α L r =>
      ∃ z ∈ S, z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) :=
        probability_mono hcover
    _ ≤ ∑ z ∈ S, uniformProbability (fun ξ : HashSample α L r =>
      z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) := probability_union _ _
    _ ≤ ∑ _z ∈ S, 1 / (2 : ℝ)^r := by
      apply Finset.sum_le_sum
      intro z hz
      exact collision_bound x z hLpos hn hxm
    _ = (S.card : ℝ) / (2 : ℝ)^r := by simp [div_eq_mul_inv]
    _ ≤ ((RecordArithmetic.countConstant t b : ℝ) * L * (n : ℝ)^(2*t-1) *
        (Fintype.card α : ℝ)^(2*b*t)) / (2 : ℝ)^r :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by ring


end DeletionGeneralization.ExceptionalProbability
namespace DeletionGeneralization.RecoveryTransfer
universe u
variable {α : Type u}

/-- The positive path obtained by replacing a known block of the negative path. -/
def splice (p : ℕ → α) (ell removed inserted : ℕ) (v : Fin inserted → α) (i : ℕ) : α :=
  if hleft : i < ell then p i
  else if h : i < ell+inserted then v ⟨i-ell, by omega⟩
  else p (i+removed-inserted)

/-- Move a positive k-seed to a negative k-seed; a crossing seed starts before the edit. -/
def seedOffset (ell removed inserted a k : ℕ) : ℕ :=
  if a+k ≤ ell then a
  else if ell+inserted ≤ a then a+removed-inserted
  else min a ell

theorem coverage (ell removed inserted a k b j : ℕ)
    (hv : inserted ≤ b) (hb : b ≤ k) (hj : j < k) :
    let d := seedOffset ell removed inserted a k
    let z := d+j
    (z < ell ∧ a ≤ z ∧ z < a+k) ∨
    (ell ≤ z ∧ z < ell+removed) ∨
    (ell+removed ≤ z ∧ a ≤ z+inserted-removed ∧ z+inserted-removed < a+k) ∨
    (d+k-b ≤ z ∧ z < d+k) := by
  dsimp only
  unfold seedOffset
  split_ifs with hbefore hafter
  · left
    omega
  · right; right; left
    omega
  · have hmin1 := min_le_left a ell
    have hmin2 := min_le_right a ell
    have hmin : min a ell=a ∨ min a ell=ell := min_choice a ell
    omega

theorem seed_in_bounds (ell removed inserted right a k : ℕ)
    (hright : k ≤ right) (ha : a+k ≤ ell+inserted+right) :
    seedOffset ell removed inserted a k+k ≤ ell+removed+right := by
  unfold seedOffset
  split_ifs with hbefore hafter
  · omega
  · omega
  · have h := min_le_right a ell
    omega

theorem transfer_agreement (p p' : ℕ → α) (ell removed inserted a k b : ℕ)
    (v : Fin inserted → α) (hv : inserted ≤ b) (hb : b ≤ k)
    (hremoved : ∀ i, i < removed → p (ell+i)=p' (ell+i))
    (hpositive : ∀ i, i < k →
      splice p ell removed inserted v (a+i)=splice p' ell removed inserted v (a+i))
    (hextra : ∀ i, i < b →
      p (seedOffset ell removed inserted a k+k-b+i)=
      p' (seedOffset ell removed inserted a k+k-b+i)) :
    ∀ i, i < k → p (seedOffset ell removed inserted a k+i)=
      p' (seedOffset ell removed inserted a k+i) := by
  intro i hi
  let d := seedOffset ell removed inserted a k
  change p (d+i)=p' (d+i)
  rcases coverage ell removed inserted a k b i hv hb hi with hpre | hmid | hpost | hend
  · have hz : a+(d+i-a)=d+i := by omega
    have h := hpositive (d+i-a) (by omega)
    rw [hz] at h
    simpa only [splice,dif_pos (show d+i < ell from hpre.1)] using h
  · have hz : ell+(d+i-ell)=d+i := by omega
    simpa only [hz] using hremoved (d+i-ell) (by omega)
  · let z := d+i+inserted-removed
    have hz : a+(z-a)=z := by dsimp [z];omega
    have h := hpositive (z-a) (by dsimp [z];omega)
    rw [hz] at h
    have hz1 : ¬z < ell := by dsimp [z];omega
    have hz2 : ¬z < ell+inserted := by dsimp [z];omega
    have hz3 : z+removed-inserted=d+i := by dsimp [z];omega
    simpa only [splice,dif_neg hz1,dif_neg hz2,hz3] using h
  · have hz : d+k-b+(d+i-(d+k-b))=d+i := by omega
    have h := hextra (d+i-(d+k-b)) (by omega)
    change p (d+k-b+(d+i-(d+k-b)))=p' (d+k-b+(d+i-(d+k-b))) at h
    simpa only [hz] using h

end DeletionGeneralization.RecoveryTransfer
namespace DeletionGeneralization.RecoverySeed
open RecoveryTransfer
universe u
variable {α : Type u}

/-- A finite seed decoder. Its inputs are only the recorded header, positive seed,
and b extension letters; it does not receive the unknown negative word. -/
def decode (ell removed inserted a k b : ℕ) (hv : inserted ≤ b) (hb : b ≤ k)
    (old : Fin removed → α) (bits : Fin k → α) (extra : Fin b → α) : Fin k → α :=
  fun i =>
    let d := seedOffset ell removed inserted a k
    let z := d+i.val
    if hpre : z < ell ∧ a ≤ z ∧ z < a+k then bits ⟨z-a,by omega⟩
    else if hmid : ell ≤ z ∧ z < ell+removed then old ⟨z-ell,by omega⟩
    else if hpost : ell+removed ≤ z ∧ a ≤ z+inserted-removed ∧ z+inserted-removed < a+k
      then bits ⟨z+inserted-removed-a,by omega⟩
    else extra ⟨z-(d+k-b),by
      have h := coverage ell removed inserted a k b i.val hv hb i.isLt
      dsimp only at h
      change (z < ell ∧ a ≤ z ∧ z < a+k) ∨
        (ell ≤ z ∧ z < ell+removed) ∨
        (ell+removed ≤ z ∧ a ≤ z+inserted-removed ∧ z+inserted-removed < a+k) ∨
        (d+k-b ≤ z ∧ z < d+k) at h
      omega⟩

theorem decode_correct (p : ℕ → α) (ell removed inserted a k b : ℕ)
    (v : Fin inserted → α) (hv : inserted ≤ b) (hb : b ≤ k)
    (old : Fin removed → α) (bits : Fin k → α) (extra : Fin b → α)
    (hold : ∀ i, old i=p (ell+i.val))
    (hbits : ∀ i, bits i=splice p ell removed inserted v (a+i.val))
    (hextra : ∀ i, extra i=p (seedOffset ell removed inserted a k+k-b+i.val)) :
    ∀ i, decode ell removed inserted a k b hv hb old bits extra i=
      p (seedOffset ell removed inserted a k+i.val) := by
  intro i
  unfold decode
  dsimp only
  split_ifs with hpre hmid hpost
  · rw [hbits]
    have ha : a+(seedOffset ell removed inserted a k+i.val-a)=
        seedOffset ell removed inserted a k+i.val := by omega
    rw [ha]
    exact dif_pos hpre.1
  · rw [hold]
    congr 1
    try dsimp only
    omega
  · rw [hbits]
    have ha : a+(seedOffset ell removed inserted a k+i.val+inserted-removed-a)=
        seedOffset ell removed inserted a k+i.val+inserted-removed := by omega
    rw [ha]
    have h1 : ¬seedOffset ell removed inserted a k+i.val+inserted-removed < ell := by omega
    have h2 : ¬seedOffset ell removed inserted a k+i.val+inserted-removed < ell+inserted := by omega
    simp only [splice,dif_neg h1,dif_neg h2]
    congr 1
    try dsimp only
    omega
  · rw [hextra]
    congr 1
    try dsimp only
    have h := coverage ell removed inserted a k b i.val hv hb i.isLt
    dsimp only at h
    omega

theorem exists_extension (p : ℕ → α) (ell removed inserted right a k b : ℕ)
    (v : Fin inserted → α) (hv : inserted ≤ b) (hb : b ≤ k)
    (hright : k ≤ right) (ha : a+k ≤ ell+inserted+right)
    (old : Fin removed → α) (bits : Fin k → α)
    (hold : ∀ i, old i=p (ell+i.val))
    (hbits : ∀ i, bits i=splice p ell removed inserted v (a+i.val)) :
    ∃ extra : Fin b → α,
      seedOffset ell removed inserted a k+k ≤ ell+removed+right ∧
      ∀ i, decode ell removed inserted a k b hv hb old bits extra i=
        p (seedOffset ell removed inserted a k+i.val) := by
  refine ⟨fun i => p (seedOffset ell removed inserted a k+k-b+i.val),
    seed_in_bounds ell removed inserted right a k hright ha,?_⟩
  exact decode_correct p ell removed inserted a k b v hv hb old bits _ hold hbits (fun _ => rfl)

end DeletionGeneralization.RecoverySeed

/-!
Executable partial-word storage for the concrete recovery decoder.
Reads require every requested bit to be known. Writes check the finite word
bound and reject disagreements with previously known bits. Neither operation
receives the unknown target word; it appears only in their correctness proofs.
-/
namespace DeletionGeneralization.RecoveryMemory

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

abbrev Memory (α : Type u) := ℕ → Option α
abbrev Bits (α : Type u) (len : ℕ) := Fin len → α

def empty : (Memory α) := fun _ => none

def Sound (s : (Memory α)) (p : (ℕ → α)) (m : ℕ) : Prop :=
  ∀ j, j < m → ∀ b, s j = some b → b = p j

def Extends (s t : (Memory α)) : Prop :=
  ∀ j b, s j = some b → t j = some b

def Matches {len : ℕ} (bits : Bits α len) (p : (ℕ → α)) (start : ℕ) : Prop :=
  ∀ i, bits i = p (start + i.val)

/-- Read finite data without a choice oracle or access to the target word. -/
def readBits (s : (Memory α)) (start len : ℕ) : Option (Bits α len) :=
  if ∀ i : Fin len, s (start + i.val) = some ((s (start + i.val)).getD default)
  then some (fun i => (s (start + i.val)).getD default)
  else none

def Compatible (s : (Memory α)) (start : ℕ) {len : ℕ} (bits : Bits α len) : Prop :=
  ∀ i, s (start + i.val) = none ∨ s (start + i.val) = some (bits i)

instance (s : (Memory α)) (start : ℕ) {len : ℕ} (bits : Bits α len) :
    Decidable (Compatible s start bits) := by
  unfold Compatible
  infer_instance

def putBits (s : (Memory α)) (start : ℕ) {len : ℕ} (bits : Bits α len) : (Memory α) :=
  fun j => if h : start ≤ j ∧ j < start + len
    then some (bits ⟨j - start, by omega⟩)
    else s j

/-- Checked write: reject out-of-bounds blocks and inconsistent known letters. -/
def writeBits (s : (Memory α)) (m start : ℕ) {len : ℕ} (bits : Bits α len) : Option (Memory α) :=
  if start + len ≤ m ∧ Compatible s start bits
  then some (putBits s start bits)
  else none

theorem empty_sound (p : (ℕ → α)) (m : ℕ) : Sound empty p m := by
  intro j hj b hb
  simp [empty] at hb

theorem readBits_eq_some_iff (s : (Memory α)) (start len : ℕ) (bits : Bits α len) :
    readBits s start len = some bits ↔
      ∀ i, s (start + i.val) = some (bits i) := by
  unfold readBits
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro i
      rw [← heq']
      exact h i
    · intro hb
      congr 1
      funext i
      simp [hb i]
  · rename_i h
    constructor
    · simp
    · intro hb
      apply False.elim
      apply h
      intro i
      simp [hb i]

theorem readBits_sound (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hread : readBits s start len = some bits) :
    Matches bits p start := by
  intro i
  exact hs (start + i.val) (by have := i.isLt; omega) (bits i)
    ((readBits_eq_some_iff s start len bits).mp hread i)

theorem compatible_of_sound (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hbits : Matches bits p start) :
    Compatible s start bits := by
  intro i
  cases h : s (start + i.val) with
  | none => exact Or.inl rfl
  | some b =>
    have hb := hs (start + i.val) (by have := i.isLt; omega) b h
    exact Or.inr (congrArg some (hb.trans (hbits i).symm))

theorem putBits_at (s : (Memory α)) (start len : ℕ) (bits : Bits α len) (i : Fin len) :
    putBits s start bits (start + i.val) = some (bits i) := by
  simp [putBits, i.isLt]

theorem putBits_extends (s : (Memory α)) (start len : ℕ) (bits : Bits α len)
    (hc : Compatible s start bits) : Extends s (putBits s start bits) := by
  intro j b hb
  unfold putBits
  split
  · rename_i h
    let i : Fin len := ⟨j - start, by omega⟩
    have hi : start + i.val = j := by dsimp [i]; omega
    have hc' := hc i
    rw [hi, hb] at hc'
    rcases hc' with hn | heq
    · contradiction
    · simpa [i] using heq.symm
  · exact hb

theorem putBits_sound (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (bits : Bits α len) (hbits : Matches bits p start) :
    Sound (putBits s start bits) p m := by
  intro j hj b hb
  unfold putBits at hb
  split at hb
  · rename_i h
    have heq := Option.some.inj hb
    have hbit := hbits ⟨j - start, by omega⟩
    have hidx : start + (j - start) = j := by omega
    simpa [hidx, heq] using hbit
  · exact hs j hj b hb

theorem readBits_putBits (s : (Memory α)) (start len : ℕ) (bits : Bits α len) :
    readBits (putBits s start bits) start len = some bits := by
  apply (readBits_eq_some_iff _ _ _ _).mpr
  exact putBits_at s start len bits

theorem writeBits_success (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hbits : Matches bits p start) :
    writeBits s m start bits = some (putBits s start bits) := by
  simp [writeBits, hbound, compatible_of_sound s p m start len hs hbound bits hbits]

/-- Every successful checked write preserves all previously known bits. -/
theorem writeBits_extends (s t : (Memory α)) (m start len : ℕ) (bits : Bits α len)
    (hwrite : writeBits s m start bits = some t) : Extends s t := by
  unfold writeBits at hwrite
  split at hwrite
  · rename_i h
    cases Option.some.inj hwrite
    exact putBits_extends s start len bits h.2
  · contradiction

/-- Correct data written to correct memory remains correct and can be read back. -/
theorem writeBits_correct (s : (Memory α)) (p : (ℕ → α)) (m start len : ℕ)
    (hs : Sound s p m) (hbound : start + len ≤ m)
    (bits : Bits α len) (hbits : Matches bits p start) :
    ∃ t, writeBits s m start bits = some t ∧ Sound t p m ∧
      Extends s t ∧ readBits t start len = some bits := by
  refine ⟨putBits s start bits,
    writeBits_success s p m start len hs hbound bits hbits,
    putBits_sound s p m start len hs bits hbits, ?_, readBits_putBits s start len bits⟩
  exact putBits_extends s start len bits
    (compatible_of_sound s p m start len hs hbound bits hbits)


end DeletionGeneralization.RecoveryMemory

/-!
Abstract recovery scheduling — partial formalization.
This models a combinatorial subproblem of `lem:resolve`, not that lemma.
There are no words, de Bruijn edges or signed rules in this module.
ConcreteProgress and ConcreteRecovery realize this scheduling on stored letters;
GeneratingRecovery derives the needed data from generating edited-word families.
The existence of a complete recovery trace is proved, not assumed as an
input hypothesis. Checked with Lean 4.34.0; ManuscriptCounting completes the
catalogue generating-set bound using this scheduling argument.
-/
namespace DeletionGeneralization.Recovery

abbrev Slot := Fin 3

def AdjSlot (a b : Slot) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

inductive Reach {B : Type*} (adj : B → B → Prop) : B → B → Prop
  | refl (b : B) : Reach adj b b
  | tail {a b c : B} : Reach adj a b → adj b c → Reach adj a c

/-- `none` denotes x; `some a` denotes an earlier supplying bubble. -/
structure Data (B : Type*) where
  rank : B → ℕ
  source : B → Slot → Option B
  earlier : ∀ b w a, source b w = some a → rank a < rank b
  adjacent : B → B → Prop
  root : B → Prop
  rooted : ∀ b, ∃ r, root r ∧ Reach adjacent r b

structure State (B : Type*) where
  seed : B → Option Slot
  filled : Finset (B × Slot)

variable {B : Type*} [DecidableEq B]
namespace State

def Started (s : State B) (b : B) : Prop := s.seed b ≠ none

def Done (s : State B) (b : B) (w : Slot) : Prop := (b, w) ∈ s.filled

def Complete (s : State B) (b : B) : Prop := ∀ w, s.Done b w

def Ready (s : State B) (b : B) (w : Slot) : Prop :=
  s.seed b = some w ∨ ∃ v, s.Done b v ∧ AdjSlot v w

def start (s : State B) (b : B) (w : Slot) : State B :=
  ⟨Function.update s.seed b (some w), s.filled⟩

def fill (s : State B) (b : B) (w : Slot) : State B :=
  ⟨s.seed, insert (b, w) s.filled⟩

def WellFormed (M : Data B) (s : State B) : Prop :=
  (∀ b w, s.Done b w → s.Started b) ∧
  (∀ b, M.root b → s.Complete b)

theorem started_start (s : State B) (b : B) (w : Slot) :
    (s.start b w).Started b := by simp [Started, start]

theorem started_start_mono (s : State B) (b a : B) (w : Slot)
    (h : s.Started a) : (s.start b w).Started a := by
  by_cases hab : a = b
  · subst a
    exact started_start s b w
  · have hba : b ≠ a := Ne.symm hab
    simpa [Started, start, hab, hba] using h

theorem complete_start (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.start b w).Complete a := h

theorem complete_fill (s : State B) (b a : B) (w : Slot)
    (h : s.Complete a) : (s.fill b w).Complete a := by
  intro v
  exact Finset.mem_insert_of_mem (h v)

theorem ready_started (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (h : s.Ready b w) :
    s.Started b := by
  rcases h with hseed | ⟨v, hv, _⟩
  · simp [Started, hseed]
  · exact hs.1 b v hv

theorem start_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) :
    WellFormed M (s.start b w) := by
  constructor
  · intro a v hav
    exact started_start_mono s b a w (hs.1 a v hav)
  · intro a ha
    exact complete_start s b a w (hs.2 a ha)

theorem fill_wellFormed (M : Data B) (s : State B)
    (hs : WellFormed M s) (b : B) (w : Slot) (hb : s.Started b) :
    WellFormed M (s.fill b w) := by
  constructor
  · intro a v hav
    have hmem : (a, v) ∈ insert (b, w) s.filled := hav
    rcases Finset.mem_insert.mp hmem with heq | hold
    · have hab : a = b := congrArg Prod.fst heq
      subst a
      exact hb
    · exact hs.1 a v hold
  · intro a ha
    exact complete_fill s b a w (hs.2 a ha)

/-- An incomplete started bubble has a ready unfilled window. -/
theorem frontier (s : State B) (b : B)
    (hb : s.Started b) (hi : ¬ s.Complete b) :
    ∃ w, s.Ready b w ∧ ¬ s.Done b w := by
  classical
  by_contra hn
  have hclosed : ∀ w, s.Ready b w → s.Done b w := by
    intro w hw
    by_contra hnot
    exact hn ⟨w, hw, hnot⟩
  cases hseed : s.seed b with
  | none => exact hb hseed
  | some v =>
    have hv : s.Done b v := hclosed v (Or.inl hseed)
    apply hi
    fin_cases v
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨0, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      have h2 : s.Done b 2 :=
        hclosed 2 (Or.inr ⟨1, hv, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
    · have h1 : s.Done b 1 :=
        hclosed 1 (Or.inr ⟨2, hv, by norm_num [AdjSlot]⟩)
      have h0 : s.Done b 0 :=
        hclosed 0 (Or.inr ⟨1, h1, by norm_num [AdjSlot]⟩)
      intro w
      fin_cases w <;> assumption
end State

open State

/--
Abstract transitions. Any seed-window index is permitted in this model.
A concrete realization must choose one containing a REAL transferred
stretch, so an abstract trace is not automatically a valid decoding.
-/
inductive Step (M : Data B) : State B → State B → Prop
  | startAdjacent (s : State B) (a b : B) (w : Slot)
      (ha : s.Complete a) (hab : M.adjacent a b) (hb : ¬ s.Started b) :
      Step M s (s.start b w)
  | startSupplier (s : State B) (b a : B) (w v : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : ¬ s.Started a) :
      Step M s (s.start a v)
  | fillBase (s : State B) (b : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = none) : Step M s (s.fill b w)
  | fillSupplier (s : State B) (b a : B) (w : Slot)
      (hr : s.Ready b w) (hn : ¬ s.Done b w)
      (hsrc : M.source b w = some a) (ha : s.Complete a) :
      Step M s (s.fill b w)

theorem step_preserves (M : Data B) {s s' : State B}
    (h : Step M s s') (hs : s.WellFormed M) : s'.WellFormed M := by
  cases h with
  | startAdjacent a b w ha hab hb =>
      exact State.start_wellFormed M s hs b w
  | startSupplier b a w v hr hn hsrc ha =>
      exact State.start_wellFormed M s hs a v
  | fillBase b w hr hn hsrc =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)
  | fillSupplier b a w hr hn hsrc ha =>
      exact State.fill_wellFormed M s hs b w
        (State.ready_started M s hs b w hr)

/-- Rank induction rules out incomplete started bubbles in a terminal state. -/
theorem terminal_started_complete (M : Data B) (s : State B)
    (hstop : ∀ s', ¬ Step M s s') : ∀ b, s.Started b → s.Complete b := by
  classical
  have aux : ∀ r : ℕ, ∀ b, M.rank b = r → s.Started b → s.Complete b := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro b hr hb
      by_contra hnot
      obtain ⟨w, hw, hmissing⟩ := State.frontier s b hb hnot
      cases hsrc : M.source b w with
      | none => exact hstop _ (Step.fillBase s b w hw hmissing hsrc)
      | some a =>
        by_cases ha : s.Started a
        · have hsmall : M.rank a < r := by
            have he := M.earlier b w a hsrc
            omega
          have hac : s.Complete a := ih (M.rank a) hsmall a rfl ha
          exact hstop _ (Step.fillSupplier s b a w hw hmissing hsrc hac)
        · exact hstop _ (Step.startSupplier s b a w 0 hw hmissing hsrc ha)
  intro b hb
  exact aux (M.rank b) b rfl hb

theorem terminal_complete (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hstop : ∀ s', ¬ Step M s s') :
    ∀ b, s.Complete b := by
  classical
  have hstarted := terminal_started_complete M s hstop
  have along : ∀ {a b}, Reach M.adjacent a b →
      s.Complete a → s.Complete b := by
    intro a b hpath
    induction hpath with
    | refl => exact fun h => h
    | @tail b c hpath hadj ih =>
      intro ha
      have hb : s.Complete b := ih ha
      by_cases hc : s.Started c
      · exact hstarted c hc
      · exact False.elim (hstop _ (Step.startAdjacent s b c 0 hb hadj hc))
  intro b
  obtain ⟨r, hr, hpath⟩ := M.rooted b
  exact along hpath (hs.2 r hr)

theorem progress (M : Data B) (s : State B)
    (hs : s.WellFormed M) (hincomplete : ¬ ∀ b, s.Complete b) :
    ∃ s', Step M s s' := by
  classical
  by_contra hn
  have hstop : ∀ s', ¬ Step M s s' := by
    intro s' hstep
    exact hn ⟨s', hstep⟩
  exact hincomplete (terminal_complete M s hs hstop)

section Finite
variable [Fintype B]
namespace State

def startedSet (s : State B) : Finset B :=
  Finset.univ.filter (fun b => s.seed b ≠ none)

def score (s : State B) : ℕ := s.startedSet.card + s.filled.card

theorem score_le (s : State B) : s.score ≤ 4 * Fintype.card B := by
  have h1 : s.startedSet.card ≤ Fintype.card B := Finset.card_le_univ _
  have h2 : s.filled.card ≤ Fintype.card (B × Slot) := Finset.card_le_univ _
  have h3 : s.filled.card ≤ 3 * Fintype.card B := by
    simpa [Slot, Fintype.card_prod, Nat.mul_comm] using h2
  unfold score
  omega

theorem score_start (s : State B) (b : B) (w : Slot)
    (hb : ¬ s.Started b) : (s.start b w).score = s.score + 1 := by
  classical
  have heq : (s.start b w).startedSet = insert b s.startedSet := by
    apply Finset.ext
    intro a
    change (a ∈ Finset.univ.filter
      (fun x => Function.update s.seed b (some w) x ≠ none)) ↔
      a ∈ insert b (Finset.univ.filter (fun x => s.seed x ≠ none))
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    by_cases hab : a = b
    · subst a
      simp
    · have hba : b ≠ a := Ne.symm hab
      simp [hab, hba]
  have hnot : b ∉ s.startedSet := by
    simpa [startedSet, Started] using hb
  change (s.start b w).startedSet.card + s.filled.card = s.score + 1
  rw [heq, Finset.card_insert_of_notMem hnot]
  unfold score
  omega

theorem score_fill (s : State B) (b : B) (w : Slot)
    (hn : ¬ s.Done b w) : (s.fill b w).score = s.score + 1 := by
  have hnot : (b, w) ∉ s.filled := hn
  change s.startedSet.card + (insert (b, w) s.filled).card = s.score + 1
  rw [Finset.card_insert_of_notMem hnot]
  unfold score
  omega
end State

theorem step_score (M : Data B) {s s' : State B}
    (h : Step M s s') : s'.score = s.score + 1 := by
  cases h with
  | startAdjacent a b w ha hab hb => exact State.score_start s b w hb
  | startSupplier b a w v hr hn hsrc ha => exact State.score_start s a v ha
  | fillBase b w hr hn hsrc => exact State.score_fill s b w hn
  | fillSupplier b a w hr hn hsrc ha => exact State.score_fill s b w hn

inductive Trace (M : Data B) : ℕ → State B → State B → Prop
  | nil (s : State B) : Trace M 0 s s
  | cons {m : ℕ} {s s' s'' : State B} :
      Step M s s' → Trace M m s' s'' → Trace M (m + 1) s s''

/-- Abstract recovery, NOT the manuscript's counting lemma. -/
theorem bounded_recovery (M : Data B) (s : State B)
    (hs : s.WellFormed M) :
    ∃ m s', Trace M m s s' ∧ (∀ b, s'.Complete b) ∧
      m + s.score ≤ 4 * Fintype.card B := by
  classical
  let N := 4 * Fintype.card B
  have aux : ∀ d : ℕ, ∀ q : State B, N - q.score = d → q.WellFormed M →
      ∃ m q', Trace M m q q' ∧ (∀ b, q'.Complete b) ∧ m + q.score ≤ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd hq
      by_cases hdone : ∀ b, q.Complete b
      · exact ⟨0, q, Trace.nil q, hdone, by
          have hbound := State.score_le q
          dsimp [N]
          omega⟩
      · obtain ⟨q', hstep⟩ := progress M q hq hdone
        have hq' : q'.WellFormed M := step_preserves M hstep hq
        have hscore : q'.score = q.score + 1 := step_score M hstep
        have hbound : q'.score ≤ N := State.score_le q'
        have hlt : N - q'.score < d := by omega
        obtain ⟨m, q'', htrace, hcomplete, hcost⟩ :=
          ih (N - q'.score) hlt q' rfl hq'
        exact ⟨m + 1, q'', Trace.cons hstep htrace, hcomplete, by omega⟩
  exact aux (N - s.score) s rfl hs

noncomputable def initial (M : Data B) : State B := by
  classical
  exact ⟨fun b => if M.root b then some 0 else none,
    Finset.univ.filter (fun p : B × Slot => M.root p.1)⟩

theorem initial_wellFormed (M : Data B) : (initial M).WellFormed M := by
  classical
  constructor
  · intro b w h
    have hr : M.root b := by simpa [State.Done, initial] using h
    simp [State.Started, initial, hr]
  · intro b hr w
    simp [State.Done, initial, hr]

/-- Starts with just the roots, not an assumed completely recovered state. -/
theorem recover_from_roots (M : Data B) :
    ∃ m s', Trace M m (initial M) s' ∧ (∀ b, s'.Complete b) ∧
      m ≤ 4 * Fintype.card B := by
  obtain ⟨m, s', ht, hc, hm⟩ :=
    bounded_recovery M (initial M) (initial_wellFormed M)
  exact ⟨m, s', ht, hc, by omega⟩
end Finite

end DeletionGeneralization.Recovery
namespace DeletionGeneralization.RecoveryWindows
open RecoveryMemory Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

def windowStart (D : ℕ) (w : Slot) : ℕ :=
  if w.val=0 then 0 else if w.val=1 then D/2 else D

theorem start_le (D : ℕ) (w : Slot) : windowStart D w ≤ D := by
  fin_cases w <;> simp [windowStart, Nat.div_le_self]

theorem overlap (D L k : ℕ) (v w : Slot) (hD : D+2*k ≤ 2*L)
    (hadj : AdjSlot v w) :
    max (windowStart D v) (windowStart D w)+k ≤ windowStart D v+L ∧
    max (windowStart D v) (windowStart D w)+k ≤ windowStart D w+L := by
  fin_cases v <;> fin_cases w <;> simp [AdjSlot,windowStart] at hadj ⊢ <;> omega

theorem cover_seed (D L k a : ℕ) (hD : D+2*k ≤ 2*L)
    (ha : a+k ≤ L+D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a+k ≤ windowStart D w+L := by
  by_cases hfirst : a+k ≤ L
  · exact ⟨0,by simp [windowStart];omega⟩
  by_cases hmiddle : a+k ≤ D/2+L
  · exact ⟨1,by simp [windowStart];omega⟩
  · exact ⟨2,by simp [windowStart];omega⟩

theorem cover_letter (D L a : ℕ) (hD : D ≤ 2*L) (ha : a < L+D) :
    ∃ w : Slot, windowStart D w ≤ a ∧ a < windowStart D w+L := by
  by_cases hfirst : a < L
  · exact ⟨0,by simp [windowStart];omega⟩
  by_cases hmiddle : a < D/2+L
  · exact ⟨1,by simp [windowStart];omega⟩
  · exact ⟨2,by simp [windowStart];omega⟩

def WindowKnown (s : Memory α) (start len : ℕ) : Prop :=
  ∃ bits, readBits s start len=some bits

def SeedKnown (s : Memory α) (start L k : ℕ) : Prop :=
  ∃ r bits, r+k ≤ L ∧ readBits s (start+r) k=some bits

theorem known_iff (s : Memory α) (start len : ℕ) :
    WindowKnown s start len ↔ ∀ i, i<len → ∃ b, s (start+i)=some b := by
  constructor
  · rintro ⟨bits,hread⟩ i hi
    exact ⟨bits ⟨i,hi⟩,(readBits_eq_some_iff s start len bits).mp hread ⟨i,hi⟩⟩
  · intro h
    refine ⟨fun i => (s (start+i.val)).getD default,?_⟩
    apply (readBits_eq_some_iff _ _ _ _).mpr
    intro i
    obtain ⟨b,hb⟩ := h i.val i.isLt
    simp [hb]

theorem subblock (s : Memory α) (a m b len : ℕ) (h : WindowKnown s a m)
    (hab : a ≤ b) (hbound : b+len ≤ a+m) : WindowKnown s b len := by
  apply (known_iff _ _ _).mpr
  intro i hi
  have hread := (known_iff _ _ _).mp h (b+i-a) (by omega)
  simpa [show a+(b+i-a)=b+i by omega] using hread

theorem known_mono (s t : Memory α) (start len : ℕ)
    (hext : Extends s t) (h : WindowKnown s start len) : WindowKnown t start len := by
  apply (known_iff _ _ _).mpr
  intro i hi
  obtain ⟨b,hb⟩ := (known_iff _ _ _).mp h i hi
  exact ⟨b,hext (start+i) b hb⟩

theorem seed_mono (s t : Memory α) (start L k : ℕ)
    (hext : Extends s t) (h : SeedKnown s start L k) : SeedKnown t start L k := by
  obtain ⟨r,bits,hr,hread⟩ := h
  obtain ⟨bits',hread'⟩ := known_mono s t (start+r) k hext ⟨bits,hread⟩
  exact ⟨r,bits',hr,hread'⟩

theorem adjacent_seed (s : Memory α) (D L k : ℕ) (v w : Slot)
    (hD : D+2*k ≤ 2*L) (hadj : AdjSlot v w)
    (hknown : WindowKnown s (windowStart D v) L) :
    SeedKnown s (windowStart D w) L k := by
  obtain ⟨ha,hb⟩ := overlap D L k v w hD hadj
  let a := max (windowStart D v) (windowStart D w)
  have hma : windowStart D v ≤ a := le_max_left _ _
  have hmb : windowStart D w ≤ a := le_max_right _ _
  obtain ⟨bits,hread⟩ := subblock s (windowStart D v) L a k hknown hma ha
  refine ⟨a-windowStart D w,bits,by dsimp [a];omega,?_⟩
  simpa [show windowStart D w+(a-windowStart D w)=a by omega] using hread

theorem seed_selects (s : Memory α) (D L k a : ℕ) (hD : D+2*k ≤ 2*L)
    (ha : a+k ≤ L+D) (hknown : WindowKnown s a k) :
    ∃ w : Slot, SeedKnown s (windowStart D w) L k := by
  obtain ⟨w,hwa,haw⟩ := cover_seed D L k a hD ha
  obtain ⟨bits,hread⟩ := hknown
  refine ⟨w,a-windowStart D w,bits,by omega,?_⟩
  simpa [show windowStart D w+(a-windowStart D w)=a by omega] using hread

theorem all_known (s : Memory α) (D L : ℕ) (hD : D ≤ 2*L)
    (hknown : ∀ w : Slot, WindowKnown s (windowStart D w) L) :
    WindowKnown s 0 (L+D) := by
  apply (known_iff _ _ _).mpr
  intro i hi
  obtain ⟨w,ha,hb⟩ := cover_letter D L i hD hi
  have h := (known_iff _ _ _).mp (hknown w) (i-windowStart D w) (by omega)
  simpa [show windowStart D w+(i-windowStart D w)=i by omega] using h

variable {B : Type*}

structure Realizes (s : State B) (mem : B → Memory α) (D : B → ℕ) (L k : ℕ) : Prop where
  seed_known : ∀ b w, s.seed b=some w → SeedKnown (mem b) (windowStart (D b) w) L k
  done_known : ∀ b w, s.Done b w → WindowKnown (mem b) (windowStart (D b) w) L

theorem Realizes.ready (s : State B) (mem : B → Memory α) (D : B → ℕ)
    (L k : ℕ) (hreal : Realizes s mem D L k) (b : B) (w : Slot)
    (hD : D b+2*k ≤ 2*L) (hr : s.Ready b w) :
    SeedKnown (mem b) (windowStart (D b) w) L k := by
  rcases hr with hseed | ⟨v,hv,hadj⟩
  · exact hreal.seed_known b w hseed
  · exact adjacent_seed (mem b) (D b) L k v w hD hadj (hreal.done_known b v hv)

theorem Realizes.complete (s : State B) (mem : B → Memory α) (D : B → ℕ)
    (L k : ℕ) (hreal : Realizes s mem D L k) (b : B)
    (hD : D b ≤ 2*L) (hc : s.Complete b) : WindowKnown (mem b) 0 (L+D b) :=
  all_known (mem b) (D b) L hD (fun w => hreal.done_known b w (hc w))

theorem Realizes.mono (s : State B) (mem mem' : B → Memory α) (D : B → ℕ) (L k : ℕ)
    (hreal : Realizes s mem D L k) (hext : ∀ b, Extends (mem b) (mem' b)) :
    Realizes s mem' D L k where
  seed_known b w h := seed_mono _ _ _ _ _ (hext b) (hreal.seed_known b w h)
  done_known b w h := known_mono _ _ _ _ (hext b) (hreal.done_known b w h)

theorem Realizes.start [DecidableEq B] (s : State B) (mem : B → Memory α)
    (D : B → ℕ) (L k : ℕ) (hreal : Realizes s mem D L k) (b : B) (w : Slot)
    (hseed : SeedKnown (mem b) (windowStart (D b) w) L k) :
    Realizes (s.start b w) mem D L k where
  seed_known a v h := by
    by_cases hab : a=b
    · subst a
      have hwv : w=v := by simpa [State.start] using h
      simpa [hwv] using hseed
    · have hba : b≠a := Ne.symm hab
      exact hreal.seed_known a v (by simpa [State.start,hab,hba] using h)
  done_known a v h := hreal.done_known a v h

theorem Realizes.fill [DecidableEq B] (s : State B) (mem : B → Memory α)
    (D : B → ℕ) (L k : ℕ) (hreal : Realizes s mem D L k) (b : B) (w : Slot)
    (hknown : WindowKnown (mem b) (windowStart (D b) w) L) :
    Realizes (s.fill b w) mem D L k where
  seed_known a v h := hreal.seed_known a v h
  done_known a v h := by
    rcases Finset.mem_insert.mp h with heq | hold
    · have hab : a=b := congrArg Prod.fst heq
      have hvw : v=w := congrArg Prod.snd heq
      subst a
      subst v
      exact hknown
    · exact hreal.done_known a v hold

end DeletionGeneralization.RecoveryWindows
namespace DeletionGeneralization.RecoveryHeader
open RecoveryMemory RecoveryWindows RecoveryTransfer
universe u

structure Header (α : Type u) (L b : ℕ) where
  left : Fin L
  right : Fin L
  removed : Fin (b+1)
  inserted : Fin (b+1)
  old : Fin b → α
  new : Fin b → α
  deriving DecidableEq

instance {α : Type u} [Fintype α] {L b : ℕ} : Fintype (Header α L b) :=
  Fintype.ofEquiv (Fin L × Fin L × Fin (b+1) × Fin (b+1) × (Fin b → α) × (Fin b → α))
    { toFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩
      invFun := fun h => (h.left,h.right,h.removed,h.inserted,h.old,h.new)
      left_inv := by rintro ⟨a,c,d,e,f,g⟩;rfl
      right_inv := by intro h;cases h;rfl }

variable {α : Type u} [DecidableEq α] [Inhabited α] {L b : ℕ}

def oldLetters (h : Header α L b) : Fin h.removed.val → α :=
  fun i => h.old ⟨i.val,by have := h.removed.isLt;omega⟩

def newLetters (h : Header α L b) : Fin h.inserted.val → α :=
  fun i => h.new ⟨i.val,by have := h.inserted.isLt;omega⟩

def negativeLength (h : Header α L b) : ℕ := h.left.val+h.removed.val+h.right.val
def positiveLength (h : Header α L b) : ℕ := h.left.val+h.inserted.val+h.right.val
def extraLength (h : Header α L b) : ℕ := negativeLength h-L

def positive (h : Header α L b) (p : ℕ → α) : ℕ → α :=
  splice p h.left.val h.removed.val h.inserted.val (newLetters h)

def path (h : Header α L b) (p : ℕ → α) (side : Bool) : ℕ → α :=
  if side then positive h p else p

def pathLength (h : Header α L b) (side : Bool) : ℕ :=
  if side then positiveLength h else negativeLength h

def Valid (h : Header α L b) (k : ℕ) : Prop :=
  k ≤ h.right.val ∧ L ≤ negativeLength h ∧ extraLength h+2*k ≤ 2*L

def Correct (h : Header α L b) (p : ℕ → α) : Prop :=
  ∀ i, oldLetters h i=p (h.left.val+i.val)

def pad {len : ℕ} (bits : Fin len → α) : ℕ → α :=
  fun j => if hj : j < len then bits ⟨j,hj⟩ else default

theorem positive_congr (h : Header α L b) (p q : ℕ → α)
    (heq : ∀ i, i < negativeLength h → p i=q i) :
    ∀ i, i < positiveLength h → positive h p i=positive h q i := by
  intro i hi
  unfold positive splice
  split_ifs with hleft hmid
  · apply heq
    dsimp [negativeLength,positiveLength] at *
    omega
  · rfl
  · apply heq
    dsimp [negativeLength,positiveLength] at *
    omega

def readPath (h : Header α L b) (mem : Memory α) (side : Bool) (a len : ℕ) :
    Option (Fin len → α) :=
  if a+len ≤ pathLength h side then
    if side then
      (readBits mem 0 (negativeLength h)).map (fun bits i => positive h (pad bits) (a+i.val))
    else readBits mem a len
  else none

theorem readPath_complete (h : Header α L b) (p : ℕ → α) (mem : Memory α)
    (side : Bool) (a len : ℕ) (hs : Sound mem p (negativeLength h))
    (hknown : WindowKnown mem 0 (negativeLength h))
    (ha : a+len ≤ pathLength h side) :
    ∃ bits, readPath h mem side a len=some bits ∧
      ∀ i, bits i=path h p side (a+i.val) := by
  cases side with
  | false =>
    obtain ⟨bits,hread⟩ := subblock mem 0 (negativeLength h) a len hknown (by omega)
      (by simpa [pathLength] using ha)
    refine ⟨bits,by simpa [readPath,ha] using hread,?_⟩
    intro i
    exact readBits_sound mem p (negativeLength h) a len hs
      (by simpa [pathLength] using ha) bits hread i
  | true =>
    obtain ⟨neg,hread⟩ := hknown
    have heq : ∀ j, j < negativeLength h → pad neg j=p j := by
      intro j hj
      have hr := readBits_sound mem p (negativeLength h) 0 (negativeLength h) hs
        (by omega) neg hread ⟨j,hj⟩
      simpa [pad,hj] using hr
    refine ⟨fun i => positive h (pad neg) (a+i.val),?_,?_⟩
    · simp only [readPath,if_pos ha,Bool.true_eq,ite_true,hread,Option.map_some]
    · intro i
      exact positive_congr h (pad neg) p heq (a+i.val)
        (by have := i.isLt;simpa [pathLength] using (show a+i.val < positiveLength h by
          simp [pathLength] at ha;omega))

def transfer (h : Header α L b) (k a : ℕ) (hb : b ≤ k)
    (bits : Fin k → α) (extra : Fin b → α) : ℕ × (Fin k → α) :=
  (seedOffset h.left.val h.removed.val h.inserted.val a k,
   RecoverySeed.decode h.left.val h.removed.val h.inserted.val a k b
     (by have := h.inserted.isLt;omega) hb (oldLetters h) bits extra)

theorem transfer_correct (h : Header α L b) (k a : ℕ) (hb : b ≤ k)
    (p : ℕ → α) (hv : Valid h k) (hc : Correct h p)
    (bits : Fin k → α) (ha : a+k ≤ positiveLength h)
    (hbits : ∀ i, bits i=positive h p (a+i.val)) :
    ∃ extra : Fin b → α,
      (transfer h k a hb bits extra).1+k ≤ negativeLength h ∧
      ∀ i, (transfer h k a hb bits extra).2 i=p ((transfer h k a hb bits extra).1+i.val) := by
  exact RecoverySeed.exists_extension p h.left.val h.removed.val h.inserted.val h.right.val
    a k b (newLetters h) (by have := h.inserted.isLt;omega) hb hv.1 ha
    (oldLetters h) bits hc hbits

theorem geometry (h : Header α L b) (k : ℕ)
    (hL : L=3*(k+b+1))
    (hleft : L-1-k-b ≤ h.left.val) (hright : L-1-k-b ≤ h.right.val)
    (hlen : L ≤ negativeLength h) : Valid h k := by
  have hru := h.removed.isLt
  have hlu := h.left.isLt
  have hrr := h.right.isLt
  dsimp [Valid,extraLength,negativeLength] at *
  omega

end DeletionGeneralization.RecoveryHeader

/-!
Local word-recovery lemmas — partial formalization.
Target: Section 5, `lem:resolve`, of binary_existence_2t_minus_1.tex.
Checked with Lean 4.34.0; this file alone does not verify the counting lemma.
Finite words are represented by total letter functions with explicit bounds.
-/
namespace DeletionGeneralization.RecoveryWords

universe u
variable {α : Type u}
abbrev Letters (α : Type u) := ℕ → α

def Agree (x : Letters α) (a : ℕ) (y : Letters α) (b k : ℕ) : Prop :=
  ∀ i, i < k → x (a + i) = y (b + i)

def KUnique (x : Letters α) (n k : ℕ) : Prop :=
  ∀ a b, a + k ≤ n → b + k ≤ n → Agree x a x b k → a = b

/-- A known k-stretch at a fixed offset determines a window in x. -/
theorem unique_window_lookup
    (x : Letters α) (n k L a b r : ℕ)
    (hx : KUnique x n k) (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hr : r + k ≤ L) (h : Agree x (a + r) x (b + r) k) : a = b := by
  have heq : a + r = b + r :=
    hx (a + r) (b + r) (by omega) (by omega) h
  omega


end DeletionGeneralization.RecoveryWords

/-!
Executable lookup of a window in the fixed word from a finite seed.
The algorithm receives only the fixed word, bounds, and the seed bits.
The unknown target word occurs only in the correctness theorems.
-/
namespace DeletionGeneralization.RecoveryLookup

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords

/-- A candidate is in bounds and has the supplied seed at the requested offset. -/
def Matches (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) (a : ℕ) : Prop :=
  r + k ≤ L ∧ a + L ≤ n ∧ ∀ i : Fin k, x (a + r + i.val) = seed i

instance (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) (a : ℕ) :
    Decidable (Matches x n k L r seed a) := by
  unfold Matches
  infer_instance

/-- Search the finitely many candidate window starts; no witness is an input. -/
def lookup (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) : Option ℕ :=
  (List.range (n + 1)).find? (fun a => decide (Matches x n k L r seed a))

theorem lookup_sound (x : Letters α) (n k L r a : ℕ) (seed : Fin k → α)
    (h : lookup x n k L r seed = some a) : Matches x n k L r seed a := by
  have hp : decide (Matches x n k L r seed a) = true :=
    List.find?_some (p := fun b => decide (Matches x n k L r seed b)) h
  exact of_decide_eq_true hp

theorem lookup_exists (x : Letters α) (n k L r : ℕ) (seed : Fin k → α)
    (h : ∃ a, Matches x n k L r seed a) :
    ∃ a, lookup x n k L r seed = some a := by
  rcases h with ⟨a, ha⟩
  cases heq : lookup x n k L r seed with
  | some b => exact ⟨b, rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp heq
    have hamem : a ∈ List.range (n + 1) := by
      simp only [List.mem_range]
      have := ha.2.1
      omega
    have hfalse := hnone a hamem
    exact False.elim (hfalse (decide_eq_true ha))

theorem matches_unique (x : Letters α) (n k L r a b : ℕ) (seed : Fin k → α)
    (hx : KUnique x n k) (ha : Matches x n k L r seed a)
    (hb : Matches x n k L r seed b) : a = b := by
  apply unique_window_lookup x n k L a b r hx ha.2.1 hb.2.1 ha.1
  intro i hi
  exact (ha.2.2 ⟨i, hi⟩).trans (hb.2.2 ⟨i, hi⟩).symm

/-- Under k-uniqueness the bounded search returns exactly the matching start. -/
theorem lookup_eq_some_iff (x : Letters α) (n k L r a : ℕ) (seed : Fin k → α)
    (hx : KUnique x n k) :
    lookup x n k L r seed = some a ↔ Matches x n k L r seed a := by
  constructor
  · exact lookup_sound x n k L r a seed
  · intro ha
    obtain ⟨b, hb⟩ := lookup_exists x n k L r seed ⟨a, ha⟩
    have hab := matches_unique x n k L r a b seed hx ha
      (lookup_sound x n k L r b seed hb)
    simpa [hab] using hb

/-- Copy the entire located window as finite data. -/
def recoverWindow (x : Letters α) (n k L r : ℕ) (seed : Fin k → α) :
    Option (Fin L → α) :=
  (lookup x n k L r seed).map (fun a i => x (a + i.val))

/-- Any returned window really is an in-bounds window of the fixed word. -/
theorem recoverWindow_sound (x : Letters α) (n k L r : ℕ) (seed : Fin k → α)
    (bits : Fin L → α) (h : recoverWindow x n k L r seed = some bits) :
    ∃ a, Matches x n k L r seed a ∧ bits = fun i => x (a + i.val) := by
  unfold recoverWindow at h
  cases heq : lookup x n k L r seed with
  | none => simp [heq] at h
  | some a =>
    simp only [heq, Option.map_some, Option.some.injEq] at h
    exact ⟨a, lookup_sound x n k L r a seed heq, h.symm⟩

/-- A target window occurring in x is recovered exactly from its seed. -/
theorem recoverWindow_of_occurrence
    (x target : Letters α) (n k L r a w : ℕ) (seed : Fin k → α)
    (hx : KUnique x n k) (hr : r + k ≤ L) (ha : a + L ≤ n)
    (hocc : Agree x a target w L)
    (hseed : ∀ i : Fin k, seed i = target (w + r + i.val)) :
    recoverWindow x n k L r seed = some (fun i : Fin L => target (w + i.val)) := by
  have hmatch : Matches x n k L r seed a := by
    refine ⟨hr, ha, ?_⟩
    intro i
    have hi : r + i.val < L := by omega
    calc
      x (a + r + i.val) = target (w + r + i.val) := by
        simpa [Nat.add_assoc] using hocc (r + i.val) hi
      _ = seed i := (hseed i).symm
  have hlookup := (lookup_eq_some_iff x n k L r a seed hx).mpr hmatch
  unfold recoverWindow
  rw [hlookup]
  simp only [Option.map_some, Option.some.injEq]
  funext i
  exact hocc i.val i.isLt


end DeletionGeneralization.RecoveryLookup

/-!
Executable letter-level fill operations. Base-word fills discover the window
position from stored seed bits. Supplier fills copy stored bits at a recorded
offset. The target words and occurrence witnesses are proof parameters only.
These primitives are used by the bounded decoder proof in ConcreteRecovery.
-/
namespace DeletionGeneralization.RecoveryFill

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords RecoveryMemory

/-- Fill a destination window by locating its known seed in the fixed word. -/
def fillFromBase (x : Letters α) (n k L : ℕ) (s : (Memory α)) (m start r : ℕ) :
    Option (Memory α) :=
  (readBits s (start + r) k).bind fun seed =>
    (RecoveryLookup.recoverWindow x n k L r seed).bind fun bits =>
      writeBits s m start bits

/-- Copy a bounded block of actual stored supplier data into checked memory. -/
def copyFromMemory (source : (Memory α)) (sourceLength sourceStart len : ℕ)
    (s : (Memory α)) (m start : ℕ) : Option (Memory α) :=
  if sourceStart + len ≤ sourceLength then
    (readBits source sourceStart len).bind fun bits => writeBits s m start bits
  else none

/-- Root records contain a position in x, so their whole negative path can be read. -/
def loadRoot (x : Letters α) (n a len : ℕ) (s : (Memory α)) (m : ℕ) : Option (Memory α) :=
  if a + len ≤ n then writeBits s m 0 (fun i : Fin len => x (a + i.val))
  else none

def Recovered (s t : (Memory α)) (p : Letters α) (m start len : ℕ) : Prop :=
  Sound t p m ∧ Extends s t ∧
    readBits t start len = some (fun i : Fin len => p (start + i.val))

/-- A valid base occurrence is filled exactly, using only its stored seed. -/
theorem fillFromBase_correct (x p : Letters α) (n k L : ℕ)
    (s : (Memory α)) (m start r : ℕ) (seed : Bits α k)
    (hx : KUnique x n k) (hs : Sound s p m)
    (hbound : start + L ≤ m) (hr : r + k ≤ L)
    (hread : readBits s (start + r) k = some seed)
    (hocc : ∃ a, a + L ≤ n ∧ Agree x a p start L) :
    ∃ t, fillFromBase x n k L s m start r = some t ∧
      Recovered s t p m start L := by
  obtain ⟨a, ha, hagree⟩ := hocc
  have hseed : RecoveryMemory.Matches seed p (start + r) :=
    readBits_sound s p m (start + r) k hs (by omega) seed hread
  have hlookup := RecoveryLookup.recoverWindow_of_occurrence
    x p n k L r a start seed hx hr ha hagree hseed
  let bits : Bits α L := fun i => p (start + i.val)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start L hs hbound bits (fun _ => rfl)
  refine ⟨t, ?_, hsound, hext, hknown⟩
  simp only [fillFromBase, hread, Option.bind_some, hlookup]
  exact ht

/-- Supplier copying preserves truth when the recorded blocks really agree. -/
theorem copyFromMemory_correct (source s : (Memory α)) (q p : Letters α)
    (sourceLength sourceStart len m start : ℕ) (bits : Bits α len)
    (hsource : Sound source q sourceLength) (hs : Sound s p m)
    (hsourceBound : sourceStart + len ≤ sourceLength) (hbound : start + len ≤ m)
    (hread : readBits source sourceStart len = some bits)
    (hagree : Agree q sourceStart p start len) :
    ∃ t, copyFromMemory source sourceLength sourceStart len s m start = some t ∧
      Recovered s t p m start len := by
  have hbits : RecoveryMemory.Matches bits p start := by
    intro i
    exact (readBits_sound source q sourceLength sourceStart len hsource
      hsourceBound bits hread i).trans (hagree i.val i.isLt)
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m start len hs hbound bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simp only [copyFromMemory, if_pos hsourceBound, hread, Option.bind_some]
    exact ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i

theorem loadRoot_correct (x p : Letters α) (n a len : ℕ) (s : (Memory α)) (m : ℕ)
    (hs : Sound s p m) (ha : a + len ≤ n) (hbound : len ≤ m)
    (hocc : Agree x a p 0 len) :
    ∃ t, loadRoot x n a len s m = some t ∧ Recovered s t p m 0 len := by
  let bits : Bits α len := fun i => x (a + i.val)
  have hbits : RecoveryMemory.Matches bits p 0 := fun i => hocc i.val i.isLt
  obtain ⟨t, ht, hsound, hext, hknown⟩ :=
    writeBits_correct s p m 0 len hs (by omega) bits hbits
  refine ⟨t, ?_, hsound, hext, ?_⟩
  · simpa only [loadRoot, if_pos ha] using ht
  · rw [hknown]
    congr 1
    funext i
    exact hbits i

/-- Even arbitrary base-fill inputs cannot overwrite an already recorded bit. -/
theorem fillFromBase_extends (x : Letters α) (n k L : ℕ)
    (s t : (Memory α)) (m start r : ℕ)
    (h : fillFromBase x n k L s m start r = some t) : Extends s t := by
  unfold fillFromBase at h
  cases hseed : readBits s (start + r) k with
  | none => simp [hseed] at h
  | some seed =>
    simp only [hseed, Option.bind_some] at h
    cases hbits : RecoveryLookup.recoverWindow x n k L r seed with
    | none => simp [hbits] at h
    | some bits =>
      simp only [hbits, Option.bind_some] at h
      exact writeBits_extends s t m start L bits h


end DeletionGeneralization.RecoveryFill
namespace DeletionGeneralization.RecoveryDecoder
open RecoveryMemory RecoveryWindows RecoveryHeader
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α] {B : Type*} [DecidableEq B] {L b : ℕ}

inductive Instruction (B : Type*) (α : Type u) (b : ℕ) where
  | start (source : B) (sourceSide : Bool) (sourceOffset : ℕ)
      (dest : B) (destSide : Bool) (destOffset : ℕ) (extra : Fin b → α)
  | fillBase (dest : B) (window : Recovery.Slot) (seedOffset : ℕ)
  | fillSupplier (source : B) (side : Bool) (sourceOffset : ℕ)
      (dest : B) (window : Recovery.Slot)

def start (h : Header α L b) (k : ℕ) (hbk : b ≤ k) (mem : Memory α)
    (side : Bool) (a : ℕ) (bits : Fin k → α) (extra : Fin b → α) : Option (Memory α) :=
  if side then
    let out := transfer h k a hbk bits extra
    writeBits mem (negativeLength h) out.1 out.2
  else writeBits mem (negativeLength h) a bits

def execute {L b : ℕ} (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k)
    (header : B → Header α L b) (mem : B → Memory α) :
    Instruction B α b → Option (B → Memory α)
  | .start source ss so dest ds d extra =>
    (readPath (header source) (mem source) ss so k).bind fun bits =>
      (start (header dest) k hbk (mem dest) ds d bits extra).map (Function.update mem dest)
  | .fillBase dest w r =>
    (RecoveryFill.fillFromBase x n k L (mem dest) (negativeLength (header dest))
      (windowStart (extraLength (header dest)) w) r).map (Function.update mem dest)
  | .fillSupplier source side a dest w =>
    (readPath (header source) (mem source) side a L).bind fun bits =>
      (writeBits (mem dest) (negativeLength (header dest))
        (windowStart (extraLength (header dest)) w) bits).map (Function.update mem dest)

def run {L b : ℕ} (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k)
    (header : B → Header α L b) : (B → Memory α) → List (Instruction B α b) → Option (B → Memory α)
  | mem, [] => some mem
  | mem, instr::rest => (execute x n k hbk header mem instr).bind fun next => run x n k hbk header next rest

def loadRoots {L b : ℕ} (x : ℕ → α) (n : ℕ) (header : B → Header α L b) :
    (B → Memory α) → List (B × ℕ) → Option (B → Memory α)
  | mem, [] => some mem
  | mem, (dest,a)::rest =>
    (RecoveryFill.loadRoot x n a (negativeLength (header dest))
      (mem dest) (negativeLength (header dest))).bind fun next =>
        loadRoots x n header (Function.update mem dest next) rest

def isStart {b : ℕ} : Instruction B α b → ℕ
  | .start .. => 1
  | _ => 0

def starts {b : ℕ} (ins : List (Instruction B α b)) : ℕ := (ins.map isStart).sum

def Bounded {b : ℕ} (L : ℕ) : Instruction B α b → Prop
  | .start _ _ a _ _ c _ => a < 3*L ∧ c < 3*L
  | .fillBase _ _ r => r < 3*L
  | .fillSupplier _ _ a _ _ => a < 3*L

end DeletionGeneralization.RecoveryDecoder

/-!
Concrete contiguity of a word whose L-windows occur in a k-unique word.

This is the word-level step used to place a component's root negative path
inside x. It does not assume that the occurrence positions are consecutive:
that fact is proved from k-uniqueness and the overlaps of consecutive windows.
Finite lengths are explicit bounds on total letter functions, as in RecoveryWords.
-/

namespace DeletionGeneralization.RecoveryPaths

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords

/-- A length-L window has a valid occurrence in the finite prefix of x. -/
def Occurs (x : Letters α) (n : ℕ) (p : Letters α) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree x a p i L

/-- Two consecutive L-windows must occur consecutively in a k-unique x. -/
theorem consecutive_occurrences
    (x p : Letters α) (n k L i a b : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree x a p i L) (hright : Agree x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree x (a + 1) x b k := by
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
    (x p : Letters α) (n k L D : ℕ)
    (hx : KUnique x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences x p n k L i (a + i) b
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
    (x p : Letters α) (n k m a b : ℕ)
    (hx : KUnique x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree x a p 0 m) (hright : Agree x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm


end DeletionGeneralization.RecoveryPaths

/-!
Concrete selection of a root in every component of a family of word paths.

The paths carry actual letters and finite lengths. Generating means that each
negative L-window occurs in x or on an earlier family's path. Adjacency is
defined by equal, in-bounds (L-1)-letter stretches, not an assumed supplier
closure. Least rank therefore supplies a member whose whole negative path
occurs in a k-unique x. This does not yet define manuscript rules or a decoder.
-/

namespace DeletionGeneralization.RecoveryRoots

universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

open RecoveryWords

/-- Side false is negative; side true is positive. Each side has length L+extra. -/
structure Family (α : Type u) (B : Type*) where
  rank : B → ℕ
  path : B → Bool → Letters α
  extra : B → Bool → ℕ

namespace Family

/-- Every negative window occurs in x or in an earlier path of the family. -/
def Generating {B : Type*} (F : Family α B) (x : Letters α) (n L : ℕ) : Prop :=
  ∀ b i, i ≤ F.extra b false →
    RecoveryPaths.Occurs x n (F.path b false) i L ∨
      ∃ a side j, F.rank a < F.rank b ∧ j ≤ F.extra a side ∧
        Agree (F.path b false) i (F.path a side) j L

/-- Actual common vertices, with valid offsets on the two finite word paths. -/
def Adjacent {B : Type*} (F : Family α B) (L : ℕ) (a b : B) : Prop :=
  ∃ sideA sideB i j,
    i ≤ F.extra a sideA + 1 ∧ j ≤ F.extra b sideB + 1 ∧
    i + (L - 1) ≤ L + F.extra a sideA ∧
    j + (L - 1) ≤ L + F.extra b sideB ∧
    Agree (F.path a sideA) i (F.path b sideB) j (L - 1)

/-- Undirected connectedness of the actual common-vertex relation. -/
def Connected {B : Type*} (F : Family α B) (L : ℕ) : B → B → Prop :=
  Relation.EqvGen (F.Adjacent L)

/-- Sharing an entire valid gram also gives a common de Bruijn vertex. -/
theorem supplier_adjacent {B : Type*} (F : Family α B) (L : ℕ)
    (b a : B) (side : Bool) (i j : ℕ)
    (hi : i ≤ F.extra b false) (hj : j ≤ F.extra a side)
    (hgram : Agree (F.path b false) i (F.path a side) j L) :
    F.Adjacent L b a := by
  refine ⟨false, side, i, j, by omega, by omega, by omega, by omega, ?_⟩
  intro q hq
  exact hgram q (by omega)

/-- Natural-number rank has a least value in every nonempty component. -/
theorem exists_minimal_in_component {B : Type*} (F : Family α B) (L : ℕ) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ a, F.Connected L a b → F.rank r ≤ F.rank a := by
  classical
  let P : ℕ → Prop := fun k => ∃ a, F.Connected L a b ∧ F.rank a = k
  have hex : ∃ k, P k := ⟨F.rank b, b, Relation.EqvGen.refl b, rfl⟩
  obtain ⟨r, hr, hrank⟩ := Nat.find_spec hex
  refine ⟨r, hr, ?_⟩
  intro a ha
  have hle : Nat.find hex ≤ F.rank a := Nat.find_min' hex ⟨a, ha, rfl⟩
  omega

/-- Every component has a member whose negative windows all occur in x.
No rootedness or supplier-closure hypothesis is assumed. -/
theorem component_root_windows {B : Type*} (F : Family α B)
    (x : Letters α) (n L : ℕ) (hgen : F.Generating x n L) (b : B) :
    ∃ r, F.Connected L r b ∧
      ∀ i, i ≤ F.extra r false → RecoveryPaths.Occurs x n (F.path r false) i L := by
  obtain ⟨r, hr, hmin⟩ := F.exists_minimal_in_component L b
  refine ⟨r, hr, ?_⟩
  intro i hi
  rcases hgen r i hi with hx | ⟨a, side, j, hearlier, hj, hgram⟩
  · exact hx
  · have hadj : F.Adjacent L r a := F.supplier_adjacent L r a side i j hi hj hgram
    have haconn : F.Connected L a b :=
      Relation.EqvGen.trans a r b
        (Relation.EqvGen.symm r a (Relation.EqvGen.rel r a hadj)) hr
    have hle := hmin a haconn
    omega

/-- A component root's entire negative word is a genuine contiguous subword of x. -/
theorem component_root_subword {B : Type*} (F : Family α B)
    (x : Letters α) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hgen : F.Generating x n L) (b : B) :
    ∃ r a, F.Connected L r b ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by
  obtain ⟨r, hr, hwindows⟩ := F.component_root_windows x n L hgen b
  obtain ⟨a, ha, hagree⟩ := RecoveryPaths.all_windows_occur_implies_subword
    x (F.path r false) n k L (F.extra r false) hx hk hwindows
  exact ⟨r, a, hr, ha, hagree⟩


end Family

end DeletionGeneralization.RecoveryRoots
namespace DeletionGeneralization.RecoveryModel
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α] {B : Type*}

structure Model (B : Type*) (α : Type u) (x : ℕ → α) (n k L b : ℕ) where
  header : B → Header α L b
  negative : B → ℕ → α
  schedule : Recovery.Data B
  bk : b ≤ k
  valid : ∀ a, Valid (header a) k
  correct : ∀ a, Correct (header a) (negative a)
  base_occurrence : ∀ a w, schedule.source a w=none →
    ∃ j, j+L ≤ n ∧ Agree x j (negative a) (windowStart (extraLength (header a)) w) L
  supplier_occurrence : ∀ a w s, schedule.source a w=some s →
    ∃ side j, j+L ≤ pathLength (header s) side ∧
      Agree (negative a) (windowStart (extraLength (header a)) w)
        (path (header s) (negative s) side) j L
  adjacent_seed : ∀ a c, schedule.adjacent a c →
    ∃ sa sc i j, i+k ≤ pathLength (header a) sa ∧ j+k ≤ pathLength (header c) sc ∧
      Agree (path (header a) (negative a) sa) i (path (header c) (negative c) sc) j k
  root_occurrence : ∀ a, schedule.root a →
    ∃ j, j+negativeLength (header a) ≤ n ∧ Agree x j (negative a) 0 (negativeLength (header a))

variable {x : ℕ → α} {n k L b : ℕ}

def Model.Sound (M : Model B α x n k L b) (mem : B → Memory α) : Prop :=
  ∀ a, RecoveryMemory.Sound (mem a) (M.negative a) (negativeLength (M.header a))

def Model.Realizes (M : Model B α x n k L b) (s : Recovery.State B) (mem : B → Memory α) : Prop :=
  RecoveryWindows.Realizes s mem (fun a => extraLength (M.header a)) L k

structure Model.Invariant [DecidableEq B] (M : Model B α x n k L b)
    (s : Recovery.State B) (mem : B → Memory α) : Prop where
  wellFormed : s.WellFormed M.schedule
  sound : M.Sound mem
  realizes : M.Realizes s mem

theorem Model.length_eq (M : Model B α x n k L b) (a : B) :
    L+extraLength (M.header a)=negativeLength (M.header a) := by
  have h := (M.valid a).2.1
  unfold extraLength
  omega

theorem Model.window_bound (M : Model B α x n k L b) (a : B) (w : Recovery.Slot) :
    windowStart (extraLength (M.header a)) w+L ≤ negativeLength (M.header a) := by
  have h := start_le (extraLength (M.header a)) w
  have heq := M.length_eq a
  omega

theorem Model.complete_known (M : Model B α x n k L b) (s : Recovery.State B)
    (mem : B → Memory α) (hr : M.Realizes s mem) (a : B) (hc : s.Complete a) :
    WindowKnown (mem a) 0 (negativeLength (M.header a)) := by
  rw [←M.length_eq a]
  exact hr.complete s mem _ L k a (by have h := (M.valid a).2.2;omega) hc

theorem Model.sound_update [DecidableEq B] (M : Model B α x n k L b)
    (mem : B → Memory α) (hs : M.Sound mem) (a : B) (next : Memory α)
    (hn : RecoveryMemory.Sound next (M.negative a) (negativeLength (M.header a))) :
    M.Sound (Function.update mem a next) := by
  intro c
  by_cases hca : c=a
  · subst c
    simpa using hn
  · simpa [Function.update,hca] using hs c

theorem Model.path_lt (M : Model B α x n k L b) (a : B) (side : Bool) :
    pathLength (M.header a) side < 3*L := by
  have hleft := (M.header a).left.isLt
  have hright := (M.header a).right.isLt
  have hu := (M.header a).removed.isLt
  have hv := (M.header a).inserted.isLt
  have hk := (M.valid a).2.2
  have hb := M.bk
  cases side <;> simp only [pathLength,Bool.false_eq_true,ite_false,ite_true,
    negativeLength,positiveLength] <;> omega

theorem Model.offset_lt (M : Model B α x n k L b) (a : B) (side : Bool)
    (i len : ℕ) (h : i+len ≤ pathLength (M.header a) side) : i < 3*L := by
  have hh := M.path_lt a side
  omega

end DeletionGeneralization.RecoveryModel
namespace DeletionGeneralization.RecoveryProgress
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder RecoveryModel Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [DecidableEq B] {x : ℕ → α} {n k L b : ℕ}

theorem start_correct (h : Header α L b) (p : ℕ → α) (mem : Memory α)
    (k : ℕ) (hbk : b ≤ k) (hv : Valid h k) (hc : Correct h p)
    (hs : Sound mem p (negativeLength h)) (side : Bool) (a : ℕ)
    (bits : Fin k → α) (ha : a+k ≤ pathLength h side)
    (hbits : ∀ i, bits i=path h p side (a+i.val)) :
    ∃ w extra next, start h k hbk mem side a bits extra=some next ∧
      Sound next p (negativeLength h) ∧ Extends mem next ∧
      SeedKnown next (windowStart (extraLength h) w) L k := by
  have hlen : L+extraLength h=negativeLength h := by
    have h := hv.2.1
    unfold extraLength
    omega
  cases side with
  | false =>
    obtain ⟨next,hn,hsound,hext,hread⟩ := writeBits_correct mem p (negativeLength h) a k
      hs ha bits hbits
    obtain ⟨w,hw⟩ := seed_selects next (extraLength h) L k a hv.2.2
      (by simpa [hlen,pathLength] using ha) ⟨bits,hread⟩
    exact ⟨w,fun _ => default,next,by simpa [start] using hn,hsound,hext,hw⟩
  | true =>
    obtain ⟨extra,hbound,hmatch⟩ := transfer_correct h k a hbk p hv hc bits ha hbits
    let out := transfer h k a hbk bits extra
    obtain ⟨next,hn,hsound,hext,hread⟩ := writeBits_correct mem p (negativeLength h) out.1 k
      hs hbound out.2 hmatch
    obtain ⟨w,hw⟩ := seed_selects next (extraLength h) L k out.1 hv.2.2
      (by simpa only [hlen] using hbound) ⟨out.2,hread⟩
    exact ⟨w,extra,next,by simpa only [start,ite_true] using hn,hsound,hext,hw⟩

theorem execute_start (M : Model B α x n k L b) (s : State B) (mem : B → Memory α)
    (hi : M.Invariant s mem) (source : B) (ss : Bool) (so : ℕ)
    (dest : B) (ds : Bool) (d : ℕ) (bits : Fin k → α)
    (hread : readPath (M.header source) (mem source) ss so k=some bits)
    (hbound : d+k ≤ pathLength (M.header dest) ds)
    (hmatch : ∀ i, bits i=path (M.header dest) (M.negative dest) ds (d+i.val)) :
    ∃ w extra mem',
      execute x n k M.bk M.header mem (.start source ss so dest ds d extra)=some mem' ∧
      M.Invariant (s.start dest w) mem' := by
  obtain ⟨w,extra,next,hn,hsound,hext,hseed⟩ := start_correct (M.header dest) (M.negative dest)
    (mem dest) k M.bk (M.valid dest) (M.correct dest) (hi.sound dest) ds d bits hbound hmatch
  have hext' : ∀ a, Extends (mem a) (Function.update mem dest next a) := by
    intro a
    by_cases ha : a=dest
    · subst a;simpa using hext
    · simpa [Function.update,ha] using (show Extends (mem a) (mem a) from fun _ _ h => h)
  have hreal := hi.realizes.mono s mem (Function.update mem dest next) _ L k hext'
  refine ⟨w,extra,Function.update mem dest next,?_,?_⟩
  · simp only [execute,hread,Option.bind_some,hn,Option.map_some]
  · refine ⟨State.start_wellFormed M.schedule s hi.wellFormed dest w,
      M.sound_update mem hi.sound dest next hsound,?_⟩
    apply hreal.start s _ _ L k dest w
    simpa using hseed

theorem fill_invariant (M : Model B α x n k L b) (s : State B) (mem : B → Memory α)
    (hi : M.Invariant s mem) (dest : B) (w : Slot) (next : Memory α)
    (hstep : Step M.schedule s (s.fill dest w))
    (hs : Sound next (M.negative dest) (negativeLength (M.header dest)))
    (hext : Extends (mem dest) next)
    (hknown : WindowKnown next (windowStart (extraLength (M.header dest)) w) L) :
    M.Invariant (s.fill dest w) (Function.update mem dest next) := by
  have hext' : ∀ a, Extends (mem a) (Function.update mem dest next a) := by
    intro a
    by_cases ha : a=dest
    · subst a;simpa using hext
    · simpa [Function.update,ha] using (show Extends (mem a) (mem a) from fun _ _ h => h)
  have hreal := hi.realizes.mono s mem (Function.update mem dest next) _ L k hext'
  refine ⟨step_preserves M.schedule hstep hi.wellFormed,
    M.sound_update mem hi.sound dest next hs,?_⟩
  apply hreal.fill s _ _ L k dest w
  simpa using hknown

theorem lift_step [Fintype B] (M : Model B α x n k L b) (hx : KUnique x n k)
    (s : State B) (mem : B → Memory α) (hi : M.Invariant s mem)
    {q : State B} (step : Step M.schedule s q) :
    ∃ q' mem' instruction,
      Step M.schedule s q' ∧ execute x n k M.bk M.header mem instruction=some mem' ∧
      M.Invariant q' mem' ∧
      q'.startedSet.card=s.startedSet.card+isStart instruction ∧ Bounded L instruction := by
  cases step with
  | startAdjacent a c w ha hac hc =>
    obtain ⟨sa,sc,i,j,hib,hjb,hagree⟩ := M.adjacent_seed a c hac
    obtain ⟨bits,hread,hmatch⟩ := readPath_complete (M.header a) (M.negative a) (mem a) sa i k
      (hi.sound a) (M.complete_known s mem hi.realizes a ha) hib
    have htarget : ∀ z, bits z=path (M.header c) (M.negative c) sc (j+z.val) :=
      fun z => (hmatch z).trans (hagree z.val z.isLt)
    obtain ⟨v,extra,mem',hex,hinv⟩ := execute_start M s mem hi a sa i c sc j bits hread hjb htarget
    refine ⟨s.start c v,mem',.start a sa i c sc j extra,
      Step.startAdjacent s a c v ha hac hc,hex,hinv,?_,?_⟩
    · have hscore := State.score_start s c v hc
      change (s.start c v).startedSet.card=s.startedSet.card+1
      change (s.start c v).startedSet.card+s.filled.card=s.startedSet.card+s.filled.card+1 at hscore
      omega
    · exact ⟨M.offset_lt a sa i k hib,M.offset_lt c sc j k hjb⟩
  | startSupplier c a w v hr hn hsrc ha =>
    obtain ⟨r,seed,hrb,hrd⟩ := hi.realizes.ready s mem _ L k c w (M.valid c).2.2 hr
    obtain ⟨side,j,hjb,hagree⟩ := M.supplier_occurrence c w a hsrc
    have hwindow := M.window_bound c w
    have hsource : windowStart (extraLength (M.header c)) w+r+k ≤ negativeLength (M.header c) := by omega
    have htarget : j+r+k ≤ pathLength (M.header a) side := by omega
    have hmatch := readBits_sound (mem c) (M.negative c) (negativeLength (M.header c))
      (windowStart (extraLength (M.header c)) w+r) k (hi.sound c) hsource seed hrd
    have hm : ∀ z, seed z=path (M.header a) (M.negative a) side (j+r+z.val) := by
      intro z
      have hz : r+z.val < L := by have := z.isLt;omega
      exact (hmatch z).trans (by simpa only [Nat.add_assoc] using hagree (r+z.val) hz)
    have hread : readPath (M.header c) (mem c) false
        (windowStart (extraLength (M.header c)) w+r) k=some seed := by
      simpa [readPath,pathLength,hsource] using hrd
    obtain ⟨v',extra,mem',hex,hinv⟩ := execute_start M s mem hi c false
      (windowStart (extraLength (M.header c)) w+r) a side (j+r) seed hread htarget hm
    refine ⟨s.start a v',mem',.start c false (windowStart (extraLength (M.header c)) w+r)
      a side (j+r) extra,Step.startSupplier s c a w v' hr hn hsrc ha,hex,hinv,?_,?_⟩
    · have hscore := State.score_start s a v' ha
      change (s.start a v').startedSet.card=s.startedSet.card+1
      change (s.start a v').startedSet.card+s.filled.card=s.startedSet.card+s.filled.card+1 at hscore
      omega
    · exact ⟨M.offset_lt c false _ k hsource,M.offset_lt a side _ k htarget⟩
  | fillBase c w hr hn hsrc =>
    obtain ⟨r,seed,hrb,hrd⟩ := hi.realizes.ready s mem _ L k c w (M.valid c).2.2 hr
    obtain ⟨next,hex,hsound,hext,hknown⟩ := RecoveryFill.fillFromBase_correct x (M.negative c)
      n k L (mem c) (negativeLength (M.header c)) (windowStart (extraLength (M.header c)) w)
      r seed hx (hi.sound c) (M.window_bound c w) hrb hrd (M.base_occurrence c w hsrc)
    have hstep := Step.fillBase s c w hr hn hsrc
    refine ⟨s.fill c w,Function.update mem c next,.fillBase c w r,hstep,?_,?_,?_,?_⟩
    · simp only [execute,hex,Option.map_some]
    · exact fill_invariant M s mem hi c w next hstep hsound hext ⟨_,hknown⟩
    · rfl
    · change r < 3*L
      have hL := (M.header c).left.isLt
      omega
  | fillSupplier c a w hr hn hsrc ha =>
    obtain ⟨side,j,hjb,hagree⟩ := M.supplier_occurrence c w a hsrc
    obtain ⟨bits,hread,hmatch⟩ := readPath_complete (M.header a) (M.negative a) (mem a)
      side j L (hi.sound a) (M.complete_known s mem hi.realizes a ha) hjb
    have hm : Matches bits (M.negative c) (windowStart (extraLength (M.header c)) w) :=
      fun z => (hmatch z).trans (hagree z.val z.isLt).symm
    obtain ⟨next,hex,hsound,hext,hknown⟩ := writeBits_correct (mem c) (M.negative c)
      (negativeLength (M.header c)) (windowStart (extraLength (M.header c)) w) L
      (hi.sound c) (M.window_bound c w) bits hm
    have hstep := Step.fillSupplier s c a w hr hn hsrc ha
    refine ⟨s.fill c w,Function.update mem c next,.fillSupplier a side j c w,hstep,?_,?_,?_,?_⟩
    · simp only [execute,hread,Option.bind_some,hex,Option.map_some]
    · exact fill_invariant M s mem hi c w next hstep hsound hext ⟨_,hknown⟩
    · rfl
    · exact M.offset_lt a side j L hjb

end DeletionGeneralization.RecoveryProgress
namespace DeletionGeneralization.RecoveryInitialization
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder RecoveryModel Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [DecidableEq B] {x : ℕ → α} {n k L b : ℕ}

def ValidRoots (M : Model B α x n k L b) (records : List (B × ℕ)) : Prop :=
  ∀ a j, (a,j) ∈ records → j+negativeLength (M.header a) ≤ n ∧
    Agree x j (M.negative a) 0 (negativeLength (M.header a))

theorem load_correct (M : Model B α x n k L b) (records : List (B × ℕ))
    (mem : B → Memory α) (hs : M.Sound mem) (hv : ValidRoots M records) :
    ∃ result, loadRoots x n M.header mem records=some result ∧ M.Sound result ∧
      (∀ a, Extends (mem a) (result a)) ∧
      ∀ a j, (a,j) ∈ records → WindowKnown (result a) 0 (negativeLength (M.header a)) := by
  induction records generalizing mem with
  | nil =>
    exact ⟨mem,rfl,hs,fun _ _ _ h => h,by simp⟩
  | cons record rest ih =>
    rcases record with ⟨a,j⟩
    have ho := hv a j (by simp)
    obtain ⟨next,hn,hsound,hext,hread⟩ := RecoveryFill.loadRoot_correct x (M.negative a) n j
      (negativeLength (M.header a)) (mem a) (negativeLength (M.header a))
      (hs a) ho.1 le_rfl ho.2
    have hnext := M.sound_update mem hs a next hsound
    have htail : ValidRoots M rest := fun c z hz => hv c z (by simp [hz])
    obtain ⟨result,hresult,hrsound,hrext,hrknown⟩ := ih (Function.update mem a next) hnext htail
    have hstep : ∀ c, Extends (mem c) (Function.update mem a next c) := by
      intro c
      by_cases hca : c=a
      · subst c;simpa using hext
      · simpa [Function.update,hca] using (show Extends (mem c) (mem c) from fun _ _ h => h)
    refine ⟨result,?_,hrsound,fun c z v hz => hrext c z v (hstep c z v hz),?_⟩
    · simpa only [loadRoots,hn,Option.bind_some] using hresult
    · intro c z hz
      rcases List.mem_cons.mp hz with heq | hrest
      · cases heq
        apply known_mono (Function.update mem a next a) (result a) 0
          (negativeLength (M.header a)) (hrext a)
        simpa using (show WindowKnown next 0 (negativeLength (M.header a)) from ⟨_,hread⟩)
      · exact hrknown c z hrest

noncomputable def rootCount [Fintype B] (M : Model B α x n k L b) : ℕ := by
  classical
  exact (Finset.univ.filter M.schedule.root).card

theorem roots_exist [Fintype B] (M : Model B α x n k L b) :
    ∃ records : List (B × ℕ), records.length=rootCount M ∧ ValidRoots M records ∧
      ∀ a, M.schedule.root a → ∃ j, (a,j) ∈ records := by
  classical
  let roots := Finset.univ.filter M.schedule.root
  let pos : B → ℕ := fun a => if hr : M.schedule.root a then Classical.choose (M.root_occurrence a hr) else 0
  let records := roots.toList.map (fun a => (a,pos a))
  have hpos : ∀ a, M.schedule.root a →
      pos a+negativeLength (M.header a) ≤ n ∧
      Agree x (pos a) (M.negative a) 0 (negativeLength (M.header a)) := by
    intro a ha
    dsimp [pos]
    rw [dif_pos ha]
    exact Classical.choose_spec (M.root_occurrence a ha)
  refine ⟨records,by simp [records,roots,rootCount],?_,?_⟩
  · intro a j hmem
    obtain ⟨c,hc,heq⟩ := List.mem_map.mp hmem
    have hroot : M.schedule.root c := by simpa [roots] using hc
    have hh := hpos c hroot
    cases heq
    exact hh
  · intro a ha
    exact ⟨pos a,List.mem_map.mpr ⟨a,by simpa [roots] using ha,rfl⟩⟩

theorem initialization [Fintype B] (M : Model B α x n k L b) :
    ∃ records mem, records.length=rootCount M ∧
      loadRoots x n M.header (fun _ => empty) records=some mem ∧ ValidRoots M records ∧
      M.Invariant (initial M.schedule) mem := by
  classical
  obtain ⟨records,hlen,hvalid,hroots⟩ := roots_exist M
  have hempty : M.Sound (fun _ => empty) := fun a =>
    empty_sound (M.negative a) (negativeLength (M.header a))
  obtain ⟨mem,hload,hsound,_,hknown⟩ := load_correct M records (fun _ => empty) hempty hvalid
  have hroot : ∀ a, M.schedule.root a → WindowKnown (mem a) 0 (negativeLength (M.header a)) := by
    intro a ha
    obtain ⟨j,hj⟩ := hroots a ha
    exact hknown a j hj
  refine ⟨records,mem,hlen,hload,hvalid,initial_wellFormed M.schedule,hsound,?_,?_⟩
  · intro a w hseed
    by_cases ha : M.schedule.root a
    · have hw : w=0 := by simpa [initial,ha] using hseed.symm
      subst w
      have hkL : k ≤ L := by have h := (M.valid a).2.2;omega
      have hk : k ≤ negativeLength (M.header a) := by have h := (M.valid a).2.1;omega
      obtain ⟨bits,hread⟩ := subblock (mem a) 0 (negativeLength (M.header a)) 0 k
        (hroot a ha) le_rfl (by omega)
      exact ⟨0,bits,by omega,by simpa [windowStart] using hread⟩
    · simp [initial,ha] at hseed
  · intro a w hdone
    have ha : M.schedule.root a := by simpa [State.Done,initial] using hdone
    exact subblock (mem a) 0 (negativeLength (M.header a)) (windowStart (extraLength (M.header a)) w)
      L (hroot a ha) (by omega) (by simpa using M.window_bound a w)

end DeletionGeneralization.RecoveryInitialization
namespace DeletionGeneralization.RecoveryRun
open RecoveryWords RecoveryMemory RecoveryWindows RecoveryHeader RecoveryDecoder RecoveryModel Recovery
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [Fintype B] [DecidableEq B] {x : ℕ → α} {n k L b : ℕ}

theorem bounded (M : Model B α x n k L b) (hx : KUnique x n k)
    (s : State B) (mem : B → Memory α) (hi : M.Invariant s mem) :
    ∃ ins mem' q, run x n k M.bk M.header mem ins=some mem' ∧
      M.Invariant q mem' ∧ (∀ a, q.Complete a) ∧
      ins.length+s.score ≤ 4*Fintype.card B ∧
      starts ins+s.startedSet.card=q.startedSet.card ∧ (∀ i ∈ ins, Bounded L i) := by
  classical
  let N := 4*Fintype.card B
  have aux : ∀ d : ℕ, ∀ s : State B, ∀ mem : B → Memory α,
      N-s.score=d → M.Invariant s mem →
      ∃ ins mem' q, run x n k M.bk M.header mem ins=some mem' ∧
        M.Invariant q mem' ∧ (∀ a, q.Complete a) ∧
        ins.length+s.score ≤ N ∧ starts ins+s.startedSet.card=q.startedSet.card ∧ (∀ i ∈ ins, Bounded L i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s mem hd hi
      by_cases hdone : ∀ a, s.Complete a
      · refine ⟨[],mem,s,rfl,hi,hdone,?_,?_,by simp⟩
        · simpa [N] using State.score_le s
        · simp [starts]
      · obtain ⟨q,hstep⟩ := progress M.schedule s hi.wellFormed hdone
        obtain ⟨q',mem',instr,hstep',hex,hinv,hstarts,hinsBound⟩ := RecoveryProgress.lift_step M hx s mem hi hstep
        have hscore := step_score M.schedule hstep'
        have hbound : q'.score ≤ N := State.score_le q'
        have hlt : N-q'.score < d := by omega
        obtain ⟨ins,mem'',q'',hrun,hfinal,hcomplete,hcost,hcount,hbounds⟩ :=
          ih (N-q'.score) hlt q' mem' rfl hinv
        refine ⟨instr::ins,mem'',q'',?_,hfinal,hcomplete,?_,?_,?_⟩
        · simp only [run,hex,Option.bind_some]
          exact hrun
        · simp only [List.length_cons]
          omega
        · simp only [starts,List.map_cons,List.sum_cons] at hcount ⊢
          omega
        · intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact hinsBound
          · exact hbounds i hi
  exact aux (N-s.score) s mem rfl hi

def finish (header : B → Header α L b) (mem : B → Memory α) :
    Option ((a : B) → Fin (negativeLength (header a)) → α) :=
  if ∀ a, (readBits (mem a) 0 (negativeLength (header a))).isSome then
    some (fun a => (readBits (mem a) 0 (negativeLength (header a))).getD (fun _ => default))
  else none

theorem finish_correct (M : Model B α x n k L b) (mem : B → Memory α)
    (hs : M.Sound mem) (hk : ∀ a, WindowKnown (mem a) 0 (negativeLength (M.header a))) :
    finish M.header mem=some (fun a i => M.negative a i.val) := by
  have heq : ∀ a, readBits (mem a) 0 (negativeLength (M.header a))=
      some (fun i => M.negative a i.val) := by
    intro a
    obtain ⟨bits,hread⟩ := hk a
    have hb : bits=(fun i => M.negative a i.val) := by
      funext i
      simpa only [Nat.zero_add] using readBits_sound (mem a) (M.negative a)
        (negativeLength (M.header a)) 0 (negativeLength (M.header a)) (hs a)
        (by omega) bits hread i
    simpa only [hb] using hread
  simp [finish,heq]

def decode (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k) (header : B → Header α L b)
    (roots : List (B × ℕ)) (ins : List (Instruction B α b)) :
    Option ((a : B) → Fin (negativeLength (header a)) → α) :=
  (loadRoots x n header (fun _ => empty) roots).bind fun mem =>
    (run x n k hbk header mem ins).bind (finish header)

theorem exists_record (M : Model B α x n k L b) (hx : KUnique x n k) :
    ∃ roots ins, roots.length=RecoveryInitialization.rootCount M ∧
      (∀ r ∈ roots, r.2 < n) ∧
      ins.length ≤ 4*Fintype.card B ∧ starts ins ≤ Fintype.card B ∧
      (∀ i ∈ ins, Bounded L i) ∧
      decode x n k M.bk M.header roots ins=some (fun a i => M.negative a i.val) := by
  obtain ⟨roots,mem,hroots,hload,hvalid,hi⟩ := RecoveryInitialization.initialization M
  obtain ⟨ins,mem',q,hrun,hinv,hdone,hlen,hstarts,hbounds⟩ := bounded M hx (initial M.schedule) mem hi
  have hcard : q.startedSet.card ≤ Fintype.card B := Finset.card_le_univ _
  refine ⟨roots,ins,hroots,?_,by omega,by omega,hbounds,?_⟩
  · rintro ⟨a,j⟩ hj
    have h := (hvalid a j hj).1
    have hl := (M.valid a).2.1
    have hpos := (M.header a).left.isLt
    dsimp only
    omega
  · simp only [decode,hload,Option.bind_some,hrun]
    apply finish_correct M mem' hinv.sound
    intro a
    exact M.complete_known q mem' hinv.realizes a (hdone a)

end DeletionGeneralization.RecoveryRun
namespace DeletionGeneralization.RecoveryFamily
open RecoveryWords RecoveryHeader RecoveryWindows RecoveryRoots RecoveryModel
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

structure EditedFamily (B : Type*) (α : Type u) (k L d : ℕ) where
  header : B → Header α L d
  negative : B → ℕ → α
  rank : B → ℕ
  bk : d ≤ k
  k_lt : k < L
  valid : ∀ a, Valid (header a) k
  correct : ∀ a, Correct (header a) (negative a)
  positive_lower : ∀ a, L ≤ positiveLength (header a)

variable {B : Type*} {k L d : ℕ}

def EditedFamily.family (E : EditedFamily B α k L d) : Family α B where
  rank := E.rank
  path a side := path (E.header a) (E.negative a) side
  extra a side := pathLength (E.header a) side-L

theorem EditedFamily.path_length_eq (E : EditedFamily B α k L d) (a : B) (side : Bool) :
    pathLength (E.header a) side=L+E.family.extra a side := by
  have hn := (E.valid a).2.1
  have hp := E.positive_lower a
  cases side <;> simp [family,pathLength] <;> omega

theorem EditedFamily.negative_extra (E : EditedFamily B α k L d) (a : B) :
    E.family.extra a false=extraLength (E.header a) := rfl

def componentSetoid (F : Family α B) (L : ℕ) : Setoid B where
  r := F.Connected L
  iseqv := ⟨fun b => Relation.EqvGen.refl b,
    fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

abbrev Components (E : EditedFamily B α k L d) := Quotient (componentSetoid E.family L)

theorem component_has_root (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L)
    (C : Components E) :
    ∃ b, Quotient.mk (componentSetoid E.family L) b = C ∧
      ∃ a, a + negativeLength (E.header b) ≤ n ∧
        Agree x a (E.negative b) 0 (negativeLength (E.header b)) := by
  induction C using Quotient.inductionOn with
  | _ b =>
    obtain ⟨r, a, hr, ha, hagree⟩ := E.family.component_root_subword
      x n k L hx E.k_lt hg b
    have hlen : L + E.family.extra r false = negativeLength (E.header r) :=
      (E.path_length_eq r false).symm
    rw [hlen] at ha hagree
    refine ⟨r, Quotient.sound hr, a, ?_, ?_⟩
    · exact ha
    · exact hagree

noncomputable def selectedRoot (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L)
    (C : Components E) : B := Classical.choose (component_has_root E x n hx hg C)

theorem selectedRoot_spec (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L)
    (C : Components E) :
    let b := selectedRoot E x n hx hg C
    Quotient.mk (componentSetoid E.family L) b = C ∧
      ∃ a, a + negativeLength (E.header b) ≤ n ∧
        Agree x a (E.negative b) 0 (negativeLength (E.header b)) :=
  Classical.choose_spec (component_has_root E x n hx hg C)

def SourceValid (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (b : B) (w : Recovery.Slot) (source : Option B) : Prop :=
  match source with
  | none => ∃ a, a + L ≤ n ∧
      Agree x a (E.negative b)
        (windowStart (extraLength (E.header b)) w) L
  | some a => E.rank a < E.rank b ∧
      ∃ side j, j + L ≤ pathLength (E.header a) side ∧
        Agree (E.negative b)
          (windowStart (extraLength (E.header b)) w)
          (path (E.header a) (E.negative a) side) j L

theorem source_exists (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n L) (b : B) (w : Recovery.Slot) :
    ∃ source, SourceValid E x n b w source := by
  have hvalid : windowStart (extraLength (E.header b)) w ≤ E.family.extra b false :=
    start_le _ w
  rcases hg b _ hvalid with hbase | ⟨a, side, j, hearlier, hj, hagree⟩
  · exact ⟨none, hbase⟩
  · refine ⟨some a, hearlier, side, j, ?_, hagree⟩
    rw [E.path_length_eq a side]
    omega

noncomputable def source (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n L) (b : B) (w : Recovery.Slot) : Option B :=
  Classical.choose (source_exists E x n hg b w)

theorem source_spec (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hg : E.family.Generating x n L) (b : B) (w : Recovery.Slot) :
    SourceValid E x n b w (source E x n hg b w) :=
  Classical.choose_spec (source_exists E x n hg b w)

theorem adjacent_symm (F : Family α B) (L : ℕ) {a b : B} (h : F.Adjacent L a b) :
    F.Adjacent L b a := by
  obtain ⟨sa, sb, i, j, hi, hj, hbi, hbj, hagree⟩ := h
  exact ⟨sb, sa, j, i, hj, hi, hbj, hbi, fun q hq => (hagree q hq).symm⟩

private theorem reach_trans {adj : B → B → Prop} {a b c : B}
    (hab : Recovery.Reach adj a b) (hbc : Recovery.Reach adj b c) :
    Recovery.Reach adj a c := by
  induction hbc with
  | refl => exact hab
  | tail hbc hcd ih => exact Recovery.Reach.tail ih hcd

theorem connected_reach (F : Family α B) (L : ℕ) {a b : B} (h : F.Connected L a b) :
    Recovery.Reach (F.Adjacent L) a b := by
  have aux : ∀ {a b}, F.Connected L a b →
      Recovery.Reach (F.Adjacent L) a b ∧ Recovery.Reach (F.Adjacent L) b a := by
    intro a b h
    induction h with
    | rel a b h => exact ⟨Recovery.Reach.tail (Recovery.Reach.refl a) h,
        Recovery.Reach.tail (Recovery.Reach.refl b) (adjacent_symm F L h)⟩
    | refl a => exact ⟨Recovery.Reach.refl a, Recovery.Reach.refl a⟩
    | symm a b h ih => exact ⟨ih.2, ih.1⟩
    | trans a b c hab hbc ihab ihbc =>
      exact ⟨reach_trans ihab.1 ihbc.1, reach_trans ihbc.2 ihab.2⟩
  exact (aux h).1

noncomputable def schedule (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) : Recovery.Data B where
  rank := E.rank
  source := source E x n hg
  earlier b w a h := by
    have hs := source_spec E x n hg b w
    rw [h] at hs
    exact hs.1
  adjacent := E.family.Adjacent L
  root b := ∃ C, selectedRoot E x n hx hg C = b
  rooted b := by
    let C : Components E := Quotient.mk _ b
    let r := selectedRoot E x n hx hg C
    refine ⟨r, ⟨C, rfl⟩, connected_reach E.family L ?_⟩
    exact Quotient.exact (selectedRoot_spec E x n hx hg C).1

/-- Derive recovery semantics from genuine generating word paths. -/
noncomputable def model (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) : Model B α x n k L d where
  header := E.header
  negative := E.negative
  schedule := schedule E x n hx hg
  bk := E.bk
  valid := E.valid
  correct := E.correct
  base_occurrence a w h := by
    have hs := source_spec E x n hg a w
    change source E x n hg a w=none at h
    rw [h] at hs
    exact hs
  supplier_occurrence a w c h := by
    have hs := source_spec E x n hg a w
    change source E x n hg a w=some c at h
    rw [h] at hs
    exact hs.2
  adjacent_seed a c h := by
    obtain ⟨sa,sc,i,j,hi,hj,hbi,hbj,hagree⟩ := h
    have hk := E.k_lt
    refine ⟨sa,sc,i,j,?_,?_,?_⟩
    · rw [E.path_length_eq a sa]
      omega
    · rw [E.path_length_eq c sc]
      omega
    · intro q hq
      exact hagree q (by omega)
  root_occurrence a h := by
    obtain ⟨C,rfl⟩ := h
    exact (selectedRoot_spec E x n hx hg C).2

noncomputable instance [Fintype B] (E : EditedFamily B α k L d) :
    Fintype (Components E) := Fintype.ofFinite _

noncomputable def rootEquiv (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) :
    Components E ≃ {a // (model E x n hx hg).schedule.root a} where
  toFun C := ⟨selectedRoot E x n hx hg C,C,rfl⟩
  invFun a := Quotient.mk (componentSetoid E.family L) a.val
  left_inv C := (selectedRoot_spec E x n hx hg C).1
  right_inv a := by
    apply Subtype.ext
    obtain ⟨C,hC⟩ := a.property
    change selectedRoot E x n hx hg (Quotient.mk (componentSetoid E.family L) a.val)=a.val
    rw [←hC,(selectedRoot_spec E x n hx hg C).1]

theorem root_count [Fintype B] [DecidableEq B]
    (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) :
    RecoveryInitialization.rootCount (model E x n hx hg)=Fintype.card (Components E) := by
  classical
  unfold RecoveryInitialization.rootCount
  rw [←Fintype.card_subtype]
  exact (Fintype.card_congr (rootEquiv E x n hx hg)).symm

theorem exists_record [Fintype B] [DecidableEq B]
    (E : EditedFamily B α k L d) (x : Letters α) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n L) :
    ∃ roots ins, roots.length=Fintype.card (Components E) ∧
      (∀ r ∈ roots, r.2 < n) ∧
      ins.length ≤ 4*Fintype.card B ∧ RecoveryDecoder.starts ins ≤ Fintype.card B ∧
      (∀ i ∈ ins, RecoveryDecoder.Bounded L i) ∧
      RecoveryRun.decode x n k E.bk E.header roots ins=some (fun a i => E.negative a i.val) := by
  obtain ⟨roots,ins,hr,hpositions,hl,hs,hbounds,hd⟩ := RecoveryRun.exists_record (model E x n hx hg) hx
  exact ⟨roots,ins,hr.trans (root_count E x n hx hg),hpositions,hl,hs,hbounds,hd⟩

end DeletionGeneralization.RecoveryFamily
namespace DeletionGeneralization.RecoveryList
open DeletionHash.MixedEdit RecoveryHeader
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]

def total (s : List α) : ℕ → α := fun j => s[j]?.getD default

theorem total_append (A B : List α) (i : ℕ) :
    total (A++B) i=if i < A.length then total A i else total B (i-A.length) := by
  simp only [total,List.getElem?_append]
  split_ifs <;> rfl

theorem splice_words (A U V B : List α) :
    RecoveryTransfer.splice (total (A++U++B)) A.length U.length V.length
      (fun i => total V i.val)=total (A++V++B) := by
  funext i
  by_cases hl : i < A.length
  · have hp : i < A.length+U.length := by omega
    simp [RecoveryTransfer.splice,total_append,List.append_assoc,hl]
  · by_cases hm : i < A.length+V.length
    · have hv : i-A.length < V.length := by omega
      simp [RecoveryTransfer.splice,total_append,List.append_assoc,hl,hm,hv]
    · have hx : ¬i+U.length-V.length < A.length := by omega
      have hy : ¬i+U.length-V.length-A.length < U.length := by omega
      have hz : ¬i-A.length < V.length := by omega
      have heq : i+U.length-V.length-A.length-U.length=i-A.length-V.length := by omega
      simp [RecoveryTransfer.splice,total_append,List.append_assoc,hl,hm,hx,hy,hz,heq]

def boundedLetters (s : List α) (b : ℕ) : Fin b → α := fun i => total s i.val

def header {L b : ℕ} (A U V B : List α)
    (hA : A.length < L) (hB : B.length < L) (hU : U.length ≤ b) (hV : V.length ≤ b) :
    Header α L b :=
  ⟨⟨A.length,hA⟩,⟨B.length,hB⟩,⟨U.length,by omega⟩,⟨V.length,by omega⟩,
    boundedLetters U b,boundedLetters V b⟩

theorem header_correct {L b : ℕ} (A U V B : List α)
    (hA : A.length < L) (hB : B.length < L) (hU : U.length ≤ b) (hV : V.length ≤ b) :
    Correct (header A U V B hA hB hU hV) (total (A++U++B)) := by
  intro i
  have hi : i.val < U.length := i.isLt
  simp [Correct,oldLetters,header,boundedLetters,List.append_assoc,total_append,hi]

theorem header_positive {L b : ℕ} (A U V B : List α)
    (hA : A.length < L) (hB : B.length < L) (hU : U.length ≤ b) (hV : V.length ≤ b) :
    positive (header A U V B hA hB hU hV) (total (A++U++B))=total (A++V++B) := by
  exact splice_words A U V B

theorem bubble_header {k L b : ℕ} (hL : L=3*(k+b+1)) (hb : b < k)
    {P Q : List α} (h : Bubble k L b P Q) :
    ∃ H : Header α L b,
      negativeLength H=P.length ∧ positiveLength H=Q.length ∧
      Valid H k ∧ Correct H (total P) ∧ positive H (total P)=total Q := by
  obtain ⟨A,U,V,B,hP,hQ,hne,hU,hV,hAl,hAu,hBl,hBu⟩ := h.1
  have hA : A.length < L := by omega
  have hB : B.length < L := by omega
  let H := header A U V B hA hB hU hV
  have hneg : negativeLength H=P.length := by simp [H,header,negativeLength,hP,Nat.add_assoc]
  have hpos : positiveLength H=Q.length := by simp [H,header,positiveLength,hQ,Nat.add_assoc]
  refine ⟨H,hneg,hpos,?_,?_,?_⟩
  · apply geometry H k hL hAl hBl
    rw [hneg]
    exact h.2.1
  · rw [hP]
    exact header_correct A U V B hA hB hU hV
  · rw [hP,hQ]
    exact header_positive A U V B hA hB hU hV

end DeletionGeneralization.RecoveryList
namespace DeletionGeneralization.WindowTools
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


end DeletionGeneralization.WindowTools
namespace DeletionGeneralization.BubbleSupport
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


end DeletionGeneralization.BubbleSupport
namespace DeletionGeneralization.CatalogueSupport
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

end DeletionGeneralization.CatalogueSupport
namespace DeletionGeneralization.SupportPaths
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


end DeletionGeneralization.SupportPaths
namespace DeletionGeneralization.BubbleConnectivity
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

end DeletionGeneralization.BubbleConnectivity
namespace DeletionGeneralization.ComponentCover
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

end DeletionGeneralization.ComponentCover
namespace DeletionGeneralization.RecoveryOccurrences
open DeletionHash.MixedEdit RecoveryList RecoveryWords WindowTools BubbleSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]

theorem window_total (P : List α) (a len : ℕ) (ha : a+len ≤ P.length) :
    window len P a=List.ofFn (fun i : Fin len => total P (a+i.val)) := by
  apply List.ext_getElem
  · simp only [window,List.length_take,List.length_drop,List.length_ofFn]
    omega
  · intro j hj hj'
    have hlen : j < len := by simpa only [List.length_ofFn] using hj'
    have hp : a+j < P.length := by omega
    simp [window,List.getElem_ofFn,total,List.getElem?_eq_getElem,hp]

theorem agree_iff (P Q : List α) (a c len : ℕ)
    (ha : a+len ≤ P.length) (hc : c+len ≤ Q.length) :
    Agree (total P) a (total Q) c len ↔ window len P a=window len Q c := by
  rw [window_total P a len ha,window_total Q c len hc,List.ofFn_inj]
  constructor
  · intro h
    funext i
    exact h i.val i.isLt
  · intro h i hi
    exact congrFun h ⟨i,hi⟩

theorem total_unique {k : ℕ} (P : List α) (hp : IsUnique k P) :
    KUnique (total P) P.length k := by
  intro a c ha hc hagree
  exact unique_positions.mp hp a c ha hc ((agree_iff P P a c k ha hc).mp hagree)

theorem occurrence_of_mem {L : ℕ} (P : List α) (g : Gram α L)
    (hg : List.ofFn g ∈ windows L P) :
    ∃ a, a+L ≤ P.length ∧ List.ofFn g=window L P a := by
  obtain ⟨a,ha,hg⟩ := List.mem_map.mp hg
  refine ⟨a,?_,hg.symm⟩
  simp only [starts,List.mem_range] at ha
  split_ifs at ha <;> omega

theorem agree_of_gram {L : ℕ} (P Q : List α) (a c : ℕ)
    (ha : a+L ≤ P.length) (hc : c+L ≤ Q.length) (g : Gram α L)
    (hp : List.ofFn g=window L P a) (hq : List.ofFn g=window L Q c) :
    Agree (total P) a (total Q) c L :=
  (agree_iff P Q a c L ha hc).mpr (hp.symm.trans hq)

theorem negative_value {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    (spectrum L Q-spectrum L P) g= -1 := by
  have hp : spectrum L P g≠0 := (nonzero_iff_mem L P g).mpr hg
  have hq : spectrum L Q g=0 := by
    by_contra hn
    exact bubble_grams_disjoint hB hL g ⟨hg,(nonzero_iff_mem L Q g).mp hn⟩
  have hs := BubbleSupport.spectrum_boolean P hB.2.2.2.2.2.2.2.1 g
  change spectrum L Q g-spectrum L P g= -1
  omega

end DeletionGeneralization.RecoveryOccurrences
namespace DeletionGeneralization.CatalogueRecovery
open DeletionHash.MixedEdit RecoveryHeader RecoveryFamily RecoveryList RecoveryOccurrences
open BubbleSupport CatalogueSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]
variable {n k L t b R : ℕ}

structure Pieces (G : Fin R → Spectrum α L) where
  words : Fin R → Fin (2*t) → List α × List α
  bubble : ∀ j i, Bubble k L b (words j i).1 (words j i).2
  disjoint : ∀ j i i', i≠i' → Disjoint (bubbleVertices L (words j i).1 (words j i).2)
    (bubbleVertices L (words j i').1 (words j i').2)
  sum_eq : ∀ j, G j=∑ i, (spectrum L (words j i).2-spectrum L (words j i).1)

theorem pieces_exist (G : Fin R → Spectrum α L) (hg : ∀ j, G j ∈ Catalogue k L t b) :
    Nonempty (Pieces (k:=k) (t:=t) (b:=b) G) := by
  classical
  choose B hB hdis heq using hg
  exact ⟨⟨B,hB,hdis,heq⟩⟩

def pairWord {G : Fin R → Spectrum α L} (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (a : Fin R × Fin (2*t)) (side : Bool) : List α :=
  if side then (C.words a.1 a.2).2 else (C.words a.1 a.2).1

structure Representation {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G) where
  family : EditedFamily (Fin R × Fin (2*t)) α k L b
  path_eq : ∀ a side, family.family.path a side=total (pairWord C a side)
  length_eq : ∀ a side, pathLength (family.header a) side=(pairWord C a side).length
  rank_eq : ∀ a, family.rank a=a.1.val

theorem representation {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (hL : L=3*(k+b+1)) (hb : b < k) :
    Nonempty (Representation C) := by
  classical
  have hex (a : Fin R × Fin (2*t)) := bubble_header hL hb (C.bubble a.1 a.2)
  choose H hn hp hv hc hpos using hex
  let E : EditedFamily (Fin R × Fin (2*t)) α k L b :=
    { header := H
      negative := fun a => total (C.words a.1 a.2).1
      rank := fun a => a.1.val
      bk := by omega
      k_lt := by omega
      valid := hv
      correct := hc
      positive_lower := fun a => by rw [hp a];exact (C.bubble a.1 a.2).2.2.2.1 }
  refine ⟨⟨E,?_,?_,fun _ => rfl⟩⟩
  · intro a side
    cases side
    · rfl
    · exact hpos a
  · intro a side
    cases side
    · exact hn a
    · exact hp a

theorem generates {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G) (E : Representation C)
    (x : Word α n) (hg : GeneratingSequence k t b (spectrum L (letters x)) G)
    (hL : 1 ≤ L) :
    E.family.family.Generating (total (letters x)) n L := by
  intro a pos hpos
  have hlen : pathLength (E.family.header a) false=L+E.family.family.extra a false :=
    E.family.path_length_eq a false
  have hbound : pos+L ≤ (C.words a.1 a.2).1.length := by
    have hh := E.length_eq a false
    change pathLength (E.family.header a) false=(C.words a.1 a.2).1.length at hh
    omega
  let g := gramAt (C.words a.1 a.2).1 pos L hbound
  have hgram : List.ofFn g=window L (C.words a.1 a.2).1 pos := ofFn_gramAt _ _ _ _
  have hmem : List.ofFn g ∈ windows L (C.words a.1 a.2).1 := by
    rw [hgram]
    exact mem_windows _ L pos hbound
  have hneg := negative_value (C.bubble a.1 a.2) hL g hmem
  have hG : G a.1 g= -1 := by
    rw [C.sum_eq a.1,sum_piece_eq (C.words a.1) (C.bubble a.1) (C.disjoint a.1) hL a.2 g
      (by rw [hneg];decide)]
    exact hneg
  rcases hg.2.2 a.1 g hG with hbase | ⟨j,hj,hjg⟩
  · left
    obtain ⟨z,hz,hzg⟩ := occurrence_of_mem (letters x) g ((nonzero_iff_mem _ _ _).mp hbase)
    refine ⟨z,?_,?_⟩
    · simpa [letters] using hz
    · rw [E.path_eq a false]
      exact agree_of_gram (letters x) (C.words a.1 a.2).1 z pos hz hbound g hzg hgram
  · right
    rw [C.sum_eq j] at hjg
    obtain ⟨i,hi⟩ := (sum_support (C.words j) (C.bubble j) (C.disjoint j) hL g).mp hjg
    rcases (difference_support (C.bubble j i) hL g).mp hi with hp | hq
    · obtain ⟨z,hz,hzg⟩ := occurrence_of_mem (C.words j i).1 g hp
      refine ⟨(j,i),false,z,?_,?_,?_⟩
      · change E.family.rank (j,i) < E.family.rank a
        rw [E.rank_eq,E.rank_eq]
        exact hj
      · have hh := E.length_eq (j,i) false
        have hl := E.family.path_length_eq (j,i) false
        change pathLength (E.family.header (j,i)) false=(C.words j i).1.length at hh
        omega
      · rw [E.path_eq a false,E.path_eq (j,i) false]
        exact agree_of_gram _ _ pos z hbound hz g hgram hzg
    · obtain ⟨z,hz,hzg⟩ := occurrence_of_mem (C.words j i).2 g hq
      refine ⟨(j,i),true,z,?_,?_,?_⟩
      · change E.family.rank (j,i) < E.family.rank a
        rw [E.rank_eq,E.rank_eq]
        exact hj
      · have hh := E.length_eq (j,i) true
        have hl := E.family.path_length_eq (j,i) true
        change pathLength (E.family.header (j,i)) true=(C.words j i).2.length at hh
        omega
      · rw [E.path_eq a false,E.path_eq (j,i) true]
        exact agree_of_gram _ _ pos z hbound hz g hgram hzg

end DeletionGeneralization.CatalogueRecovery
namespace DeletionGeneralization.ComponentInsert
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

end DeletionGeneralization.ComponentInsert
namespace DeletionGeneralization.ConnectedBlocks
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

theorem connected_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (B : Finset (Spectrum α L)) (hB : ∀ z ∈ B, z ∈ Catalogue k L t b)
    (hconn : ConnectedRules B) :
    componentCount B ≤ (2*t-1)*B.card+1 := by
  classical
  let S := B.powerset.filter (fun F => F.Nonempty ∧ componentCount F ≤ (2*t-1)*F.card+1)
  obtain ⟨z,hz⟩ := hconn.1
  have hseed : {z} ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hz),Finset.singleton_nonempty z,?_⟩
    have hc := catalogue_count_le z (hB z hz) hL
    simp only [Finset.card_singleton,mul_one]
    omega
  obtain ⟨F,hF,hmax⟩ := Finset.exists_max_image S Finset.card ⟨{z},hseed⟩
  have hfdata := Finset.mem_filter.mp hF
  have hsub : F ⊆ B := Finset.mem_powerset.mp hfdata.1
  have hne := hfdata.2.1
  have hbound := hfdata.2.2
  have hclosed : ∀ v : {w : Spectrum α L // w ∈ B}, v.val ∈ F →
      ∀ w : {w : Spectrum α L // w ∈ B}, (ruleGraph B).Adj v w → w.val ∈ F := by
    intro v hv w hadj
    by_contra hw
    have hnewbound : componentCount (insert w.val F) ≤ (2*t-1)*(insert w.val F).card+1 := by
      have ha : ∃ z ∈ F, RuleAdjacent w.val z := by
        refine ⟨v.val,hv,?_⟩
        obtain ⟨p,hp,hq⟩ := hadj.2
        exact ⟨p,hq,hp⟩
      have hc := insert_bound hL ht F w.val (hB w.val w.property) ha
      rw [Finset.card_insert_of_notMem hw,Nat.mul_add,Nat.mul_one]
      omega
    have hnew : insert w.val F ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_,Finset.insert_nonempty _ _,hnewbound⟩
      exact Finset.insert_subset w.property hsub
    have hm := hmax _ hnew
    rw [Finset.card_insert_of_notMem hw] at hm
    omega
  obtain ⟨v,hv⟩ := hne
  have hBF : B ⊆ F := by
    intro w hw
    exact reachable_mem (ruleGraph B) {z | z.val ∈ F} hclosed hv
      (hconn.2 ⟨v,hsub hv⟩ ⟨w,hw⟩)
  have heq : F=B := Finset.Subset.antisymm hsub hBF
  rwa [heq] at hbound

theorem blocks (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L) :
    (∀ F : Finset (Spectrum α L), (∀ z ∈ F, z ∈ Catalogue k L t b) →
      ∀ w : Spectrum α L, w ∈ Catalogue k L t b → w ∉ F →
        (∃ z ∈ F, RuleAdjacent w z) →
        componentCount (insert w F) ≤ componentCount F+(2*t-1)) ∧
    (∀ B : Finset (Spectrum α L), (∀ z ∈ B, z ∈ Catalogue k L t b) →
      ConnectedRules B → componentCount B ≤ (2*t-1)*B.card+1) := by
  have ht : 1 ≤ t := by have h := hreg.2.1; omega
  have hL : 1 ≤ L := by have h := hreg.2.2.2.2.1; omega
  exact ⟨fun F _ w hw _ ha => insert_bound hL ht F w hw ha,
    fun B hB hconn => connected_bound hL ht B hB hconn⟩

end DeletionGeneralization.ConnectedBlocks
namespace DeletionGeneralization.RecoveryComponents
open DeletionHash.MixedEdit CatalogueRecovery RecoveryOccurrences RecoveryFamily RecoveryList
open BubbleSupport CatalogueSupport BubbleConnectivity ComponentCover
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]
variable {k L t b R : ℕ} {G : Fin R → Spectrum α L}

theorem support_iff (C : Pieces (k:=k) (t:=t) (b:=b) G) (hL : 1 ≤ L) (g : Gram α L) :
    g ∈ supportUnion (ruleSet G) ↔
      ∃ a : Fin R × Fin (2*t), (spectrum L (C.words a.1 a.2).2-spectrum L (C.words a.1 a.2).1) g≠0 := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  constructor
  · rintro ⟨w,hw,hwg⟩
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    rw [C.sum_eq j] at hwg
    obtain ⟨i,hi⟩ := (sum_support (C.words j) (C.bubble j) (C.disjoint j) hL g).mp hwg
    exact ⟨(j,i),hi⟩
  · rintro ⟨⟨j,i⟩,hi⟩
    refine ⟨G j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
    rw [C.sum_eq j]
    exact (sum_support (C.words j) (C.bubble j) (C.disjoint j) hL g).mpr ⟨i,hi⟩

theorem overlap_adjacent (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (E : Representation C) (hL : 1 ≤ L)
    (a c : Fin R × Fin (2*t)) (v : Gram α (L-1))
    (ha : v ∈ bubbleVertices L (C.words a.1 a.2).1 (C.words a.1 a.2).2)
    (hc : v ∈ bubbleVertices L (C.words c.1 c.2).1 (C.words c.1 c.2).2) :
    E.family.family.Adjacent L a c := by
  have occurs (d : Fin R × Fin (2*t))
      (hd : v ∈ bubbleVertices L (C.words d.1 d.2).1 (C.words d.1 d.2).2) :
      ∃ side i, i+(L-1) ≤ (pairWord C d side).length ∧
        List.ofFn v=window (L-1) (pairWord C d side) i := by
    rcases hd with hd | hd
    · obtain ⟨i,hi,he⟩ := occurrence_of_mem (C.words d.1 d.2).1 v hd
      exact ⟨false,i,hi,he⟩
    · obtain ⟨i,hi,he⟩ := occurrence_of_mem (C.words d.1 d.2).2 v hd
      exact ⟨true,i,hi,he⟩
  obtain ⟨sa,i,hi,hei⟩ := occurs a ha
  obtain ⟨sc,j,hj,hej⟩ := occurs c hc
  have hal := E.length_eq a sa
  have hcl := E.length_eq c sc
  have hea := E.family.path_length_eq a sa
  have hec := E.family.path_length_eq c sc
  refine ⟨sa,sc,i,j,by omega,by omega,by omega,by omega,?_⟩
  rw [E.path_eq a sa,E.path_eq c sc]
  exact agree_of_gram _ _ i j hi hj v hei hej

theorem components_le (C : Pieces (k:=k) (t:=t) (b:=b) G)
    (E : Representation C) (hL : 1 ≤ L) :
    Fintype.card (Components E.family) ≤ componentCount (ruleSet G) := by
  classical
  let F := ruleSet G
  let B : (Fin R × Fin (2*t)) → List α × List α := fun a => C.words a.1 a.2
  have hb : ∀ a, Bubble k L b (B a).1 (B a).2 := fun a => C.bubble a.1 a.2
  have hsupp : ∀ a g, (spectrum L (B a).2-spectrum L (B a).1) g≠0 → g ∈ supportUnion F :=
    fun a g h => (support_iff C hL g).mpr ⟨a,h⟩
  have hcover : ∀ g ∈ supportUnion F, ∃ a, (spectrum L (B a).2-spectrum L (B a).1) g≠0 :=
    fun g h => (support_iff C hL g).mp h
  obtain ⟨r,hr,_,_⟩ := cover_by_bubbles F B hb hL hsupp hcover
  have connected_of_reachable (a c : Fin R × Fin (2*t))
      (h : (supportGraph F).Reachable (r a) (r c)) :
      E.family.family.Connected L a c := by
    let S : Set {v : Gram α (L-1) // v ∈ incidentVertices F} :=
      {v | ∃ d, E.family.family.Connected L a d ∧ v.val ∈ bubbleVertices L (B d).1 (B d).2}
    have hclosed : ∀ v ∈ S, ∀ w, (supportGraph F).Adj v w → w ∈ S := by
      rintro v ⟨d,had,hvd⟩ w ⟨hne,g,hg,hends⟩
      obtain ⟨e,he⟩ := hcover g hg
      have heps := difference_endpoint (hb e) hL g he
      have hve : v.val ∈ bubbleVertices L (B e).1 (B e).2 := by
        rcases hends with hends | hends
        · rw [hends.1];exact heps.1
        · rw [hends.2];exact heps.2
      have hwe : w.val ∈ bubbleVertices L (B e).1 (B e).2 := by
        rcases hends with hends | hends
        · rw [hends.2];exact heps.2
        · rw [hends.1];exact heps.1
      have hde := overlap_adjacent C E hL d e v.val hvd hve
      exact ⟨e,Relation.EqvGen.trans a d e had (Relation.EqvGen.rel d e hde),hwe⟩
    have haS : r a ∈ S := ⟨a,Relation.EqvGen.refl a,hr a⟩
    obtain ⟨d,had,hdc⟩ := ConnectedBlocks.reachable_mem (supportGraph F) S hclosed haS h
    have hdc' := overlap_adjacent C E hL d c (r c).val hdc (hr c)
    exact Relation.EqvGen.trans a d c had (Relation.EqvGen.rel d c hdc')
  let f : Components E.family → (supportGraph F).ConnectedComponent :=
    fun c => (supportGraph F).connectedComponentMk (r c.out)
  have hf : Function.Injective f := by
    intro c d heq
    have hh : (supportGraph F).Reachable (r c.out) (r d.out) :=
      SimpleGraph.ConnectedComponent.exact heq
    have hcd := connected_of_reachable c.out d.out hh
    have hq : Quotient.mk (componentSetoid E.family.family L) c.out=
        Quotient.mk (componentSetoid E.family.family L) d.out := Quotient.sound hcd
    simpa only [Quotient.out_eq] using hq
  rw [←Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective f hf

end DeletionGeneralization.RecoveryComponents
namespace DeletionGeneralization.RecoveryCodec
open RecoveryDecoder
universe u
variable {B : Type*} {α : Type u} {b L : ℕ}

def strip : Instruction B α b → Instruction B Unit b
  | .start a sa i c sc j _ => .start a sa i c sc j (fun _ => ())
  | .fillBase a w r => .fillBase a w r
  | .fillSupplier a s i c w => .fillSupplier a s i c w

def extension : Instruction B α b → Option (Fin b → α)
  | .start _ _ _ _ _ _ extra => some extra
  | _ => none

def restore : List (Instruction B Unit b) → List (Fin b → α) → Option (List (Instruction B α b))
  | [], [] => some []
  | [], _::_ => none
  | .start a sa i c sc j _::rest, extra::extras =>
      (restore rest extras).map (Instruction.start a sa i c sc j extra :: ·)
  | .start ..::_, [] => none
  | .fillBase a w r::rest, extras =>
      (restore rest extras).map (Instruction.fillBase a w r :: ·)
  | .fillSupplier a s i c w::rest, extras =>
      (restore rest extras).map (Instruction.fillSupplier a s i c w :: ·)

theorem restore_strip (ins : List (Instruction B α b)) :
    restore (ins.map strip) (ins.filterMap extension)=some ins := by
  induction ins with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [List.filterMap_cons,strip,extension,restore,ih]

theorem extension_count (ins : List (Instruction B α b)) :
    (ins.filterMap extension).length=starts ins := by
  induction ins with
  | nil => rfl
  | cons i rest ih => cases i <;> simp [List.filterMap_cons,extension,starts,isStart,Nat.add_comm] <;> exact ih

abbrev Shape (B : Type*) (L : ℕ) :=
  Fin 3 × Option B × Option B × Bool × Bool × Fin (3*L+1) × Fin (3*L+1) × Fin 3

def encode (i : Instruction B Unit b) (hi : Bounded L i) : Shape B L :=
  match i with
  | .start a sa o c sc d _ =>
      (0,some a,some c,sa,sc,⟨o,by exact Nat.lt_succ_of_lt hi.1⟩,
        ⟨d,by exact Nat.lt_succ_of_lt hi.2⟩,0)
  | .fillBase a w r =>
      (1,none,some a,false,false,⟨r,by exact Nat.lt_succ_of_lt hi⟩,0,w)
  | .fillSupplier a s o c w =>
      (2,some a,some c,s,false,⟨o,by exact Nat.lt_succ_of_lt hi⟩,0,w)

def decode (s : Shape B L) : Option (Instruction B Unit b) :=
  let (tag,a,c,sa,sc,o,d,w) := s
  if tag.val=0 then a.bind fun a => c.map fun c => .start a sa o.val c sc d.val (fun _ => ())
  else if tag.val=1 then c.map fun c => .fillBase c w o.val
  else a.bind fun a => c.map fun c => .fillSupplier a sa o.val c w

theorem decode_encode (i : Instruction B Unit b) (hi : Bounded L i) :
    decode (encode i hi)=some i := by
  cases i with
  | start a sa o c sc d extra =>
    have he : extra=(fun _ => ()) := Subsingleton.elim _ _
    subst extra
    rfl
  | fillBase a w r => rfl
  | fillSupplier a s o c w => rfl

instance (i : Instruction B α b) : Decidable (Bounded L i) := by
  cases i <;> unfold Bounded <;> infer_instance

def encodeTotal (i : Instruction B Unit b) : Option (Shape B L) :=
  if hi : Bounded L i then some (encode i hi) else none

def decodeRow (row : Option (Shape B L)) : Option (Option (Instruction B Unit b)) :=
  match row with
  | none => some none
  | some s => (decode s).map some

theorem decode_total (i : Instruction B Unit b) (hi : Bounded L i) :
    decodeRow (encodeTotal (L:=L) i)=some (some i) := by
  simp [encodeTotal,hi,decodeRow,decode_encode]

theorem strip_bounded (i : Instruction B α b) (hi : Bounded L i) :
    Bounded L (strip i) := by
  cases i <;> exact hi

end DeletionGeneralization.RecoveryCodec

/-! Fixed-width padding of instruction lists, with a proved decoding round trip. -/
namespace DeletionGeneralization.RecordPacking

variable {α β : Type*}

def pack (padding : β) (xs : List β) (size : ℕ) : Fin size → β :=
  fun i => xs[i.val]?.getD padding

def unpack (decode : β → Option (Option α)) :
    (size : ℕ) → (Fin size → β) → Option (List α)
  | 0, _ => some []
  | size + 1, rows =>
    (decode (rows ⟨0, by omega⟩)).bind fun entry =>
      (unpack decode size (fun i => rows i.succ)).map fun rest => entry.toList ++ rest

theorem unpack_of_positions (decode : β → Option (Option α)) (size : ℕ)
    (rows : Fin size → β) (xs : List α) (hsize : xs.length ≤ size)
    (hrows : ∀ i, decode (rows i) = some xs[i.val]?) :
    unpack decode size rows = some xs := by
  induction size generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    rfl
  | succ size ih =>
    cases xs with
    | nil =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some none at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some ([] : List α)[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) [] (by simp) hrest
      simp [unpack, hfirst, hr]
    | cons a xs =>
      have hfirst := hrows ⟨0, by omega⟩
      change decode (rows 0) = some (some a) at hfirst
      have hrest : ∀ i : Fin size, decode (rows i.succ) = some xs[i.val]? := by
        intro i
        simpa using hrows i.succ
      have hr := ih (fun i => rows i.succ) xs (by simp at hsize; omega) hrest
      simp [unpack, hfirst, hr]

theorem unpack_pack (decode : β → Option (Option α)) (encode : α → β)
    (padding : β) (hpadding : decode padding = some none)
    (xs : List α) (hencode : ∀ a ∈ xs, decode (encode a) = some (some a))
    (size : ℕ) (hsize : xs.length ≤ size) :
    unpack decode size (pack padding (xs.map encode) size) = some xs := by
  apply unpack_of_positions decode size _ xs hsize
  intro i
  unfold pack
  cases hget : xs[i.val]? with
  | none => simpa [List.getElem?_map, hget] using hpadding
  | some a =>
    have ha : a ∈ xs := List.mem_of_getElem? hget
    simpa [List.getElem?_map, hget] using hencode a ha


end DeletionGeneralization.RecordPacking
namespace DeletionGeneralization.RecoveryDescription
open RecoveryMemory RecoveryHeader RecoveryDecoder RecordPacking
universe u
variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {B : Type*} [Fintype B] [DecidableEq B] {n k L b c : ℕ}

abbrev Code (B : Type*) [Fintype B] (α : Type u) (n L b c : ℕ) :=
  (Fin c → Option (B × Fin n)) ×
  (Fin (4*Fintype.card B) → Option (RecoveryCodec.Shape B L)) ×
  (Fin (Fintype.card B) → Option (Fin b → α))

def encodeRoot (r : B × ℕ) : Option (B × Fin n) :=
  if h : r.2 < n then some (r.1,⟨r.2,h⟩) else none

def decodeRoot (row : Option (B × Fin n)) : Option (Option (B × ℕ)) :=
  some (row.map (fun r => (r.1,r.2.val)))

theorem root_roundtrip (r : B × ℕ) (hr : r.2 < n) :
    decodeRoot (encodeRoot (n:=n) r)=some (some r) := by
  simp [encodeRoot,decodeRoot,hr]

def decode (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k) (header : B → Header α L b)
    (code : Code B α n L b c) : Option ((a : B) → Fin (negativeLength (header a)) → α) :=
  (unpack decodeRoot c code.1).bind fun roots =>
    (unpack RecoveryCodec.decodeRow (4*Fintype.card B) code.2.1).bind fun shapes =>
      (unpack some (Fintype.card B) code.2.2).bind fun extras =>
        (RecoveryCodec.restore shapes extras).bind fun ins =>
          RecoveryRun.decode x n k hbk header roots ins

theorem pack_record (x : ℕ → α) (n k : ℕ) (hbk : b ≤ k) (header : B → Header α L b)
    (roots : List (B × ℕ)) (ins : List (Instruction B α b))
    (hc : roots.length ≤ c) (hr : ∀ r ∈ roots, r.2 < n)
    (hlen : ins.length ≤ 4*Fintype.card B) (hext : starts ins ≤ Fintype.card B)
    (hbounds : ∀ i ∈ ins, Bounded L i) :
    ∃ code : Code B α n L b c,
      decode x n k hbk header code=RecoveryRun.decode x n k hbk header roots ins := by
  let rootRows := pack none (roots.map (encodeRoot (n:=n))) c
  let shapes := ins.map RecoveryCodec.strip
  let shapeRows := pack none (shapes.map (RecoveryCodec.encodeTotal (L:=L))) (4*Fintype.card B)
  let extras := ins.filterMap RecoveryCodec.extension
  let extraRows := pack none (extras.map some) (Fintype.card B)
  have hroot : unpack decodeRoot c rootRows=some roots :=
    unpack_pack decodeRoot (encodeRoot (n:=n)) none rfl roots
      (fun r hm => root_roundtrip r (hr r hm)) c hc
  have hshape : unpack RecoveryCodec.decodeRow (4*Fintype.card B) shapeRows=some shapes := by
    apply unpack_pack RecoveryCodec.decodeRow (RecoveryCodec.encodeTotal (L:=L)) none rfl shapes
    · intro s hs
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      exact RecoveryCodec.decode_total _ (RecoveryCodec.strip_bounded i (hbounds i hi))
    · simpa [shapes] using hlen
  have hextras : unpack some (Fintype.card B) extraRows=some extras := by
    apply unpack_pack some some none rfl extras (fun _ _ => rfl) (Fintype.card B)
    simpa [extras,RecoveryCodec.extension_count] using hext
  refine ⟨(rootRows,shapeRows,extraRows),?_⟩
  simp only [decode,hroot,hshape,hextras,Option.bind_some]
  rw [RecoveryCodec.restore_strip]
  rfl

end DeletionGeneralization.RecoveryDescription
namespace DeletionGeneralization.GeneratingEncoding
open DeletionHash.MixedEdit RecoveryHeader RecoveryList RecoveryOccurrences RecoveryFamily CatalogueRecovery
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]
variable {n k L t b R c : ℕ}

abbrev Index (t R : ℕ) := Fin R × Fin (2*t)
abbrev Description (α : Type u) (n L t b R c : ℕ) :=
  (Index t R → Header α L b) × RecoveryDescription.Code (Index t R) α n L b c

noncomputable def rules (header : Index t R → Header α L b)
    (negative : (a : Index t R) → Fin (negativeLength (header a)) → α) :
    Finset (Spectrum α L) :=
  ruleSet (fun j => ∑ i : Fin (2*t),
    (spectrum L (List.ofFn (fun z : Fin (positiveLength (header (j,i))) =>
      positive (header (j,i)) (pad (negative (j,i))) z.val)) -
     spectrum L (List.ofFn (negative (j,i)))))

noncomputable def decode (x : Word α n) (k : ℕ) (hbk : b ≤ k)
    (desc : Description α n L t b R c) : Option (Finset (Spectrum α L)) :=
  (RecoveryDescription.decode (total (letters x)) n k hbk desc.1 desc.2).map (rules desc.1)

theorem ofFn_total (P : List α) (len : ℕ) (hlen : len=P.length) :
    List.ofFn (fun i : Fin len => total P i.val)=P := by
  subst len
  have h := window_total P 0 P.length (by omega)
  simpa only [window,List.drop_zero,List.take_length,Nat.zero_add] using h.symm

theorem reconstruct {G : Fin R → Spectrum α L}
    (C : Pieces (k:=k) (t:=t) (b:=b) G) (E : Representation C) :
    rules E.family.header (fun a i => E.family.negative a i.val)=ruleSet G := by
  have hn (a : Index t R) :
      List.ofFn (fun i : Fin (negativeLength (E.family.header a)) => E.family.negative a i.val)=
        (C.words a.1 a.2).1 := by
    have he := E.path_eq a false
    change E.family.negative a=total (C.words a.1 a.2).1 at he
    rw [he]
    exact ofFn_total _ _ (E.length_eq a false)
  have hp (a : Index t R) :
      List.ofFn (fun i : Fin (positiveLength (E.family.header a)) =>
        positive (E.family.header a) (pad (fun j : Fin (negativeLength (E.family.header a)) => E.family.negative a j.val)) i.val)=
      (C.words a.1 a.2).2 := by
    have he := E.path_eq a true
    change positive (E.family.header a) (E.family.negative a)=total (C.words a.1 a.2).2 at he
    have hf : (fun i : Fin (positiveLength (E.family.header a)) =>
        positive (E.family.header a) (pad (fun j : Fin (negativeLength (E.family.header a)) =>
          E.family.negative a j.val)) i.val)=
        (fun i : Fin (positiveLength (E.family.header a)) => total (C.words a.1 a.2).2 i.val) := by
      funext i
      rw [←he]
      apply positive_congr (E.family.header a) _ _ _ i.val i.isLt
      intro z hz
      simp [pad,hz]
    rw [hf]
    exact ofFn_total _ _ (E.length_eq a true)
  unfold rules
  congr 1
  funext j
  rw [C.sum_eq j]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hp (j,i),hn (j,i)]

theorem exists_description (x : Word α n) (hx : IsUnique k (letters x))
    (hL : L=3*(k+b+1)) (hb : b < k) (G : Fin R → Spectrum α L)
    (hg : GeneratingSequence k t b (spectrum L (letters x)) G)
    (hc : componentCount (ruleSet G) ≤ c) :
    ∃ desc : Description α n L t b R c, decode x k (by omega) desc=some (ruleSet G) := by
  classical
  obtain ⟨C⟩ := pieces_exist G hg.1
  obtain ⟨E⟩ := representation C hL hb
  have hgen := generates C E x hg (by omega)
  have hunique : RecoveryWords.KUnique (total (letters x)) n k := by
    simpa only [letters,List.length_ofFn] using total_unique (letters x) hx
  obtain ⟨roots,ins,hroots,hpositions,hlen,hstarts,hbounds,hrun⟩ :=
    RecoveryFamily.exists_record E.family (total (letters x)) n hunique hgen
  have hrootle : roots.length ≤ c := by
    rw [hroots]
    exact (RecoveryComponents.components_le C E (by omega)).trans hc
  obtain ⟨code,hcode⟩ := RecoveryDescription.pack_record (total (letters x)) n k E.family.bk
    E.family.header roots ins hrootle hpositions hlen hstarts hbounds
  refine ⟨(E.family.header,code),?_⟩
  unfold decode
  dsimp only
  rw [hcode,hrun]
  simp only [Option.map_some]
  congr 1
  exact reconstruct C E

end DeletionGeneralization.GeneratingEncoding
namespace DeletionGeneralization.DescriptionCount
open DeletionHash.MixedEdit GeneratingEncoding RecoveryHeader RecoveryDescription RecoveryCodec
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]

theorem header_card (L b : ℕ) :
    Fintype.card (Header α L b)=L^2*(b+1)^2*(Fintype.card α)^(2*b) := by
  let e : Header α L b ≃
      (Fin L × Fin L × Fin (b+1) × Fin (b+1) × (Fin b → α) × (Fin b → α)) :=
    { toFun := fun h => (h.left,h.right,h.removed,h.inserted,h.old,h.new)
      invFun := fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩
      left_inv := by intro h;cases h;rfl
      right_inv := by rintro ⟨a,c,d,e,f,g⟩;rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun]
  rw [show 2*b=b+b by omega,pow_add]
  ring

theorem shape_card (B : Type*) [Fintype B] (L : ℕ) :
    Fintype.card (Shape B L)=36*(Fintype.card B+1)^2*(3*L+1)^2 := by
  simp only [Shape,Fintype.card_prod,Fintype.card_fin,Fintype.card_option,Fintype.card_bool]
  ring

theorem description_card (n L t b R c : ℕ) :
    Fintype.card (Description α n L t b R c)=
      (L^2*(b+1)^2*(Fintype.card α)^(2*b))^(2*t*R) *
      (((2*t*R)*n+1)^c *
        ((36*(2*t*R+1)^2*(3*L+1)^2+1)^(4*(2*t*R)) *
          ((Fintype.card α)^b+1)^(2*t*R))) := by
  simp only [Description,Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_option,Fintype.card_bool,header_card,shape_card,Index]
  congr 1 <;> congr 1 <;> ring

theorem count_le_description {n k L t b R c : ℕ}
    (x : Word α n) (hx : IsUnique k (letters x)) (hL : L=3*(k+b+1)) (hb : b < k) :
    generatingCount k t b (spectrum L (letters x)) R c ≤
      (Fintype.card (Description α n L t b R c) : ℕ∞) := by
  classical
  let S : Set (Finset (Spectrum α L)) :=
    {F | GeneratingSet k t b (spectrum L (letters x)) F ∧ F.card=R ∧ componentCount F=c}
  have hex' (F : Finset (Spectrum α L))
      (hf : GeneratingSet k t b (spectrum L (letters x)) F ∧ F.card=R ∧ componentCount F=c) :
      ∃ d : Description α n L t b R c, GeneratingEncoding.decode x k (by omega) d=some F := by
    obtain ⟨⟨G,hG,hset⟩,hcard,hcomp⟩ := hf
    subst R
    have hc : componentCount (ruleSet G) ≤ c := by rw [hset];exact hcomp.le
    obtain ⟨d,hd⟩ := GeneratingEncoding.exists_description x hx hL hb G hG hc
    exact ⟨d,by simpa only [hset] using hd⟩
  have hex (F : S) := hex' F.val F.property
  let enc : S → Description α n L t b R c := fun F => Classical.choose (hex F)
  have henc (F : S) : GeneratingEncoding.decode x k (by omega) (enc F)=some F.val :=
    Classical.choose_spec (hex F)
  have hinj : Function.Injective enc := by
    intro F H heq
    apply Subtype.ext
    apply Option.some.inj
    rw [←henc F,←henc H,heq]
  letI : Finite S := Finite.of_injective enc hinj
  letI : Fintype S := Fintype.ofFinite S
  have hc := Fintype.card_le_of_injective enc hinj
  change S.encard ≤ _
  rw [←Set.coe_fintypeCard S]
  exact_mod_cast hc

end DeletionGeneralization.DescriptionCount
namespace DeletionGeneralization.CountArithmetic
open DeletionHash.MixedEdit GeneratingEncoding DescriptionCount
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Inhabited α]

def field (L ν : ℕ) : ℕ := 100*L*(ν+1)
def exponent (t : ℕ) : ℕ := 60*t*(100*(2*t+1)+1)

theorem exponent_pos (t : ℕ) (ht : 1 ≤ t) : 1 ≤ exponent t := by
  unfold exponent
  nlinarith

theorem raw_bound (n L b q ν c : ℕ)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (hb : b+1 ≤ L) (hq : 1 ≤ q)
    (hν : 1 ≤ ν) (hc : c ≤ ν) :
    (L^2*(b+1)^2*q^(2*b))^ν *
      ((ν*n+1)^c*((36*(ν+1)^2*(3*L+1)^2+1)^(4*ν)*(q^b+1)^ν)) ≤
      n^c*q^(3*b*ν)*(field L ν)^(30*ν) := by
  let D := field L ν
  have hd100 : 100*L ≤ D := by
    dsimp [D,field]
    nlinarith [Nat.mul_le_mul_left (100*L) (show 1 ≤ ν+1 by omega)]
  have hdn : ν+1 ≤ D := by
    dsimp [D,field]
    nlinarith [Nat.mul_le_mul_right (ν+1) (show 1 ≤ 100*L by omega)]
  have hdL : L ≤ D := by omega
  have hd3 : 3*L+1 ≤ D := by omega
  have hd36 : 36 ≤ D := by omega
  have hd2 : 2 ≤ D := by omega
  have hhead : L^2*(b+1)^2 ≤ D^4 := by
    calc
      _ ≤ D^2*D^2 := by gcongr <;> omega
      _ = D^4 := by ring
  have hroot : ν*n+1 ≤ n*D := by nlinarith
  have hsh : 36*(ν+1)^2*(3*L+1)^2 ≤ D^5 := by
    calc
      _ ≤ D*D^2*D^2 := by gcongr
      _ = D^5 := by ring
  have hshape : 36*(ν+1)^2*(3*L+1)^2+1 ≤ D^6 := by
    have hp : 1 ≤ D^5 := one_le_pow₀ (by omega)
    calc
      _ ≤ D^5+1 := by omega
      _ ≤ D^5*D := by nlinarith
      _ = D^6 := by ring
  have hqp : 1 ≤ q^b := one_le_pow₀ hq
  have hextra : q^b+1 ≤ D*q^b := by nlinarith
  calc
    _ ≤ (D^4*q^(2*b))^ν * ((n*D)^c*((D^6)^(4*ν)*(D*q^b)^ν)) := by
      gcongr
    _ = n^c*q^(3*b*ν)*D^(29*ν+c) := by
      simp only [mul_pow,←pow_mul]
      rw [show 3*b*ν=2*b*ν+b*ν by ring,
        show 29*ν+c=4*ν+c+6*(4*ν)+ν by ring]
      simp only [pow_add]
      ring
    _ ≤ n^c*q^(3*b*ν)*D^(30*ν) := by
      gcongr <;> omega

theorem self_le_power (base : ℕ) (hbase : 2 ≤ base) : ∀ q, q ≤ base^q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hp : 1 ≤ base^q := one_le_pow₀ (by omega)
    calc
      q+1 ≤ base^q+base^q := by omega
      _ = 2*base^q := by omega
      _ ≤ base*base^q := Nat.mul_le_mul_right _ hbase
      _ = base^(q+1) := by rw [pow_succ,Nat.mul_comm]

theorem field_bound (L t R : ℕ) (hL : 2 ≤ L) (hR : 1 ≤ R) :
    (field L (2*t*R))^(30*(2*t*R)) ≤ (L*R)^(exponent t*R) := by
  let C := 100*(2*t+1)
  have hbase : 2 ≤ L*R := by nlinarith
  have hC : C ≤ (L*R)^C := self_le_power (L*R) hbase C
  have hfield : field L (2*t*R) ≤ C*(L*R) := by
    have hi : 2*t*R+1 ≤ (2*t+1)*R := by nlinarith
    calc
      _ ≤ 100*L*((2*t+1)*R) := Nat.mul_le_mul_left _ hi
      _ = C*(L*R) := by dsimp [C];ring
  have hb : field L (2*t*R) ≤ (L*R)^(C+1) := by
    calc
      _ ≤ C*(L*R) := hfield
      _ ≤ (L*R)^C*(L*R) := Nat.mul_le_mul_right _ hC
      _ = (L*R)^(C+1) := (pow_succ _ _).symm
  calc
    _ ≤ ((L*R)^(C+1))^(30*(2*t*R)) := by gcongr
    _ = (L*R)^(exponent t*R) := by
      rw [←pow_mul]
      congr 1
      dsimp [C,exponent]
      ring

theorem cardinal_bound (q n k L t b R c : ℕ) (hqa : Fintype.card α=q)
    (hreg : Regime q n t b k L) (hR : 1 ≤ R) (hc : c ≤ 2*t*R) :
    Fintype.card (Description α n L t b R c) ≤
      n^c*q^(6*b*t*R)*(L*R)^(exponent t*R) := by
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  rw [description_card,hqa]
  have hν : 1 ≤ 2*t*R := by nlinarith
  have hh := raw_bound n L b q (2*t*R) c (by omega) (by omega) (by omega)
    (by omega) hν hc
  have he : 3*b*(2*t*R)=6*b*t*R := by ring
  rw [he] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (field_bound L t R (by omega) hR))

end DeletionGeneralization.CountArithmetic
namespace DeletionGeneralization.Counting
open DeletionHash.MixedEdit

universe u

/-- Lemma 5.1: counts underlying sets admitting an order, without an R! factor. -/
theorem count (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞) := by
  refine ⟨DeletionGeneralization.CountArithmetic.exponent t,
    DeletionGeneralization.CountArithmetic.exponent_pos t (by omega),?_⟩
  intro q α instF instD hqa n k L hreg x hx R c hR hc
  have hpos : 0 < Fintype.card α := by have hq := hreg.1;omega
  letI : Inhabited α := ⟨Classical.choice (Fintype.card_pos_iff.mp hpos)⟩
  have hle := DeletionGeneralization.DescriptionCount.count_le_description (t:=t) (R:=R) (c:=c) x hx hreg.2.2.2.2.1 hreg.2.2.2.2.2.1
  have hcard := DeletionGeneralization.CountArithmetic.cardinal_bound q n k L t b R c hqa hreg hR hc
  exact hle.trans (by exact_mod_cast hcard)



end DeletionGeneralization.Counting

/-!
A non-two-colorable connected graph has an odd closed walk based at any
specified vertex. The same conclusion holds at a vertex whose own connected
component is non-two-colorable. The final interface indexes the actual walk by
`Fin (m + 1)`, including both endpoints, for use with finite scan arguments.
No finiteness assumption on the ambient graph is needed.
-/
namespace DeletionGeneralization.OddGraphWalk

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


end DeletionGeneralization.OddGraphWalk

/-!
Finite connected sets can be built from one member by repeatedly adding a
member adjacent to the current set. The growth order is proved to exist from
induced connectedness; no enumeration or spanning tree is assumed.
-/

namespace DeletionGeneralization.FiniteConnectedGrowth

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


end DeletionGeneralization.FiniteConnectedGrowth
namespace DeletionGeneralization.BubbleVertexCount
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

end DeletionGeneralization.BubbleVertexCount
namespace DeletionGeneralization.CatalogueVertexCount
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

end DeletionGeneralization.CatalogueVertexCount
namespace DeletionGeneralization.WitnessBlocks
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

end DeletionGeneralization.WitnessBlocks
namespace DeletionGeneralization.WitnessSupport
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

end DeletionGeneralization.WitnessSupport
namespace DeletionGeneralization.WitnessAdjunction
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

theorem new_block_component_bound {k L t b : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (U : Finset (Spectrum α L)) (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hcat : ∀ u ∈ U, u ∈ Catalogue k L t b) :
    componentCount (blockOf (insert w U) w) ≤
      (2*t-1)*(blockOf (insert w U) w).card+1 := by
  apply ConnectedBlocks.connected_bound hL ht
  · intro u hu
    have hmem := ((mem_blockOf (insert w U) w u).mp hu).1
    rcases Finset.mem_insert.mp hmem with rfl | hu
    · exact hw
    · exact hcat u hu
  · exact connected_rules _ (blockOf_nonempty _ _ (Finset.mem_insert_self _ _))
      (blockOf_connected _ _)

end DeletionGeneralization.WitnessAdjunction
namespace DeletionGeneralization.ComponentRelation
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity ComponentCover
universe u v w
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem two_card_le {A : Type v} {B : Type w} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f)
    (hmate : ∀ a, ∃ a', a' ≠ a ∧ f a'=f a) : 2*Fintype.card B ≤ Fintype.card A := by
  classical
  have hcard : ∀ b, 2 ≤ Fintype.card {a : A // f a=b} := by
    intro b
    obtain ⟨a,ha⟩ := hf b
    obtain ⟨a',hne,he⟩ := hmate a
    have ha' : f a'=b := he.trans ha
    apply Fintype.one_lt_card_iff.mpr
    refine ⟨⟨a,ha⟩,⟨a',ha'⟩,?_⟩
    intro h
    exact hne (congrArg (fun x : {a : A // f a=b} => x.val) h).symm
  calc
    2*Fintype.card B = ∑ _b : B, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ b : B, Fintype.card {a : A // f a=b} := Finset.sum_le_sum (fun b hb => hcard b)
    _ = Fintype.card A := by
      simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)

theorem count_le_half {ι : Type v} [Fintype ι] {k L b : ℕ}
    (F : Finset (Spectrum α L)) (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2) (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0)
    (hzero : ∀ g, ∑ i, parity (spectrum L (B i).2-spectrum L (B i).1) g=0) :
    2*componentCount F ≤ Fintype.card ι := by
  classical
  obtain ⟨r,hr,hreach,hsurj⟩ := cover_by_bubbles F B hB hL hsupport hcover
  let f := fun i => (supportGraph F).connectedComponentMk (r i)
  have hmate : ∀ i, ∃ j, j ≠ i ∧ f j=f i := by
    intro i
    obtain ⟨g,hg⟩ := bubble_nonzero (B i).1 (B i).2 (hB i) hL
    have hpar : parity (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 := by
      intro h
      rcases difference_values (hB i) g with he | he | he
      · exact hg he
      · change (((spectrum L (B i).2-spectrum L (B i).1) g : ℤ) : ZMod 2)=0 at h
        rw [he] at h
        norm_num at h
      · change (((spectrum L (B i).2-spectrum L (B i).1) g : ℤ) : ZMod 2)=0 at h
        rw [he] at h
        norm_num at h
    have hex : ∃ j, j ≠ i ∧ parity (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 := by
      by_contra hn
      push_neg at hn
      have hs : (∑ j, parity (spectrum L (B j).2-spectrum L (B j).1) g) =
          parity (spectrum L (B i).2-spectrum L (B i).1) g := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          exact hn j hji
        · simp
      exact hpar (hs.symm.trans (hzero g))
    obtain ⟨j,hji,hjpar⟩ := hex
    have hj : (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 := by
      intro hj
      apply hjpar
      simp only [parity,hj,Int.cast_zero]
    let z : {v : Gram α (L-1) // v ∈ incidentVertices F} :=
      ⟨gramPrefix g,⟨g,hsupport i g hg,Or.inl rfl⟩⟩
    have hiZ := (difference_endpoint (hB i) hL g hg).1
    have hjZ := (difference_endpoint (hB j) hL g hj).1
    refine ⟨j,hji,?_⟩
    exact SimpleGraph.ConnectedComponent.sound
      ((hreach j z hjZ).trans (hreach i z hiZ).symm)
  letI : Fintype (supportGraph F).ConnectedComponent := Fintype.ofFinite _
  have h := two_card_le f hsurj hmate
  simpa only [componentCount,Nat.card_eq_fintype_card] using h

end DeletionGeneralization.ComponentRelation
namespace DeletionGeneralization.RelationSavings
open DeletionHash.MixedEdit CatalogueSupport ComponentRelation
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem bound {k L t b : ℕ} (hL : 1 ≤ L)
    (I : Finset (Spectrum α L)) (hI : ∀ z ∈ I, z ∈ Catalogue k L t b)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hrel : parity w=∑ z ∈ I, parity z) :
    componentCount I ≤ t*I.card+t := by
  classical
  obtain ⟨W,hW,hWd,heW⟩ := hw
  choose Z hZ hZd heZ using fun z : {z : Spectrum α L // z ∈ I} => hI z.val z.property
  let J := Fin (2*t) ⊕ ({z : Spectrum α L // z ∈ I} × Fin (2*t))
  let B : J → List α × List α := Sum.elim W (fun p => Z p.1 p.2)
  have hB : ∀ j, Bubble k L b (B j).1 (B j).2 := by
    intro j
    rcases j with i | ⟨z,i⟩
    · exact hW i
    · exact hZ z i
  have hsupport : ∀ j g, (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 →
      g ∈ supportUnion I := by
    intro j g hg
    rcases j with i | ⟨z,i⟩
    · apply relation_support_subset w ⟨W,hW,hWd,heW⟩ hL I hrel
      refine ⟨w,Finset.mem_singleton_self _,?_⟩
      rw [heW]
      exact (sum_support W hW hWd hL g).mpr ⟨i,hg⟩
    · refine ⟨z.val,z.property,?_⟩
      rw [heZ z]
      exact (sum_support (Z z) (hZ z) (hZd z) hL g).mpr ⟨i,hg⟩
  have hcover : ∀ g ∈ supportUnion I, ∃ j, (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 := by
    rintro g ⟨z,hz,hg⟩
    have he : z = ∑ i, (spectrum L (Z ⟨z,hz⟩ i).2-spectrum L (Z ⟨z,hz⟩ i).1) := heZ ⟨z,hz⟩
    rw [he] at hg
    obtain ⟨i,hi⟩ := (sum_support (Z ⟨z,hz⟩) (hZ ⟨z,hz⟩) (hZd ⟨z,hz⟩) hL g).mp hg
    exact ⟨Sum.inr (⟨z,hz⟩,i),hi⟩
  have hparW (g : Gram α L) :
      ∑ i, parity (spectrum L (W i).2-spectrum L (W i).1) g=parity w g := by
    rw [heW]
    simp [parity,Finset.sum_apply]
  have hparZ (z : {z : Spectrum α L // z ∈ I}) (g : Gram α L) :
      ∑ i, parity (spectrum L (Z z i).2-spectrum L (Z z i).1) g=parity z.val g := by
    rw [heZ z]
    simp [parity,Finset.sum_apply]
  have hzero : ∀ g, ∑ j, parity (spectrum L (B j).2-spectrum L (B j).1) g=0 := by
    intro g
    change (∑ j : Fin (2*t) ⊕ ({z : Spectrum α L // z ∈ I} × Fin (2*t)),
      parity (spectrum L (B j).2-spectrum L (B j).1) g)=0
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    change (∑ i, parity (spectrum L (W i).2-spectrum L (W i).1) g)+
      (∑ z : {z : Spectrum α L // z ∈ I}, ∑ i,
        parity (spectrum L (Z z i).2-spectrum L (Z z i).1) g)=0
    simp_rw [hparW,hparZ]
    have hs : (∑ z : {z : Spectrum α L // z ∈ I}, parity z.val g)=parity w g := by
      rw [hrel,Finset.sum_apply]
      exact Finset.sum_coe_sort I (fun z => parity z g)
    rw [hs]
    have he : (2 : ZMod 2)=0 := by decide
    calc
      parity w g+parity w g=(2 : ZMod 2)*parity w g := by ring
      _=0 := by rw [he,zero_mul]
  have hc := count_le_half I B hB hL hsupport hcover hzero
  have hcard : Fintype.card J=2*t+I.card*(2*t) := by
    simp [J]
  rw [hcard] at hc
  nlinarith [hc]

theorem savings (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (I : Finset (Spectrum α L)) (hI : ∀ z ∈ I, z ∈ Catalogue k L t b)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hrel : parity w=∑ z ∈ I, parity z) :
    componentCount I ≤ t*I.card+t ∧ (2 ≤ I.card → componentCount I ≤ (2*t-1)*I.card) := by
  have ht : 2 ≤ t := hreg.2.1
  have hL : 1 ≤ L := by have h := hreg.2.2.2.2.1; omega
  have hc := bound hL I hI w hw hrel
  refine ⟨hc,?_⟩
  intro hi
  have hprod := Nat.mul_le_mul_left (t-1) hi
  have hdiff : (2*t-1)*I.card = t*I.card+(t-1)*I.card := by
    rw [←Nat.add_mul]
    congr 1
    omega
  rw [hdiff]
  have hsub : t ≤ (t-1)*I.card := by omega
  omega

end DeletionGeneralization.RelationSavings
namespace DeletionGeneralization.WitnessHull
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

theorem growth_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
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
    have hc := ComponentInsert.insert_bound hL ht F z (hcat z hz) ⟨a,ha,adjacent_symm hadj⟩
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
  apply growth_bound hL ht I (blockHull G I) (subset_hull G I hIG)
  · intro z hz
    exact hcat z (hull_subset G I hz)
  · exact hull_path G I
  · exact (RelationSavings.savings n t b k L hreg I (fun z hz => hcat z (hIG hz)) w hw hrel).2 hI

end DeletionGeneralization.WitnessHull
namespace DeletionGeneralization.GeneratingSets
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


end DeletionGeneralization.GeneratingSets
namespace DeletionGeneralization.RelationBlocks
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

end DeletionGeneralization.RelationBlocks
namespace DeletionGeneralization.LargeBlock
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


end DeletionGeneralization.LargeBlock
namespace DeletionGeneralization.BinaryRelations
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

end DeletionGeneralization.BinaryRelations
namespace DeletionGeneralization.GeneratingOrder
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

end DeletionGeneralization.GeneratingOrder
namespace DeletionGeneralization.WitnessCases
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
    new_block_component_bound ht (by omega) G w hw hcat,?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp (hsub hz) with rfl | hz
    · exact hw
    · exact hcat z hz
  · intro hsmall
    omega

end DeletionGeneralization.WitnessCases
namespace DeletionGeneralization.BinaryClosedWalk
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

end DeletionGeneralization.BinaryClosedWalk

/-!
A finite greedy scan of the actual step indices of a closed walk. Before a
stop, the selected earlier steps are independent, satisfy the chosen cutoff,
and represent every earlier step up to sign. The representation is causal:
its selected index is no later than the step it represents. If the scan never
stops, closed-walk parity contradicts an odd length.
-/
namespace DeletionGeneralization.WalkScan

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


end DeletionGeneralization.WalkScan
namespace DeletionGeneralization.GeneratingScan
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

end DeletionGeneralization.GeneratingScan
namespace DeletionGeneralization.SelectedRules
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

end DeletionGeneralization.SelectedRules
namespace DeletionGeneralization.WitnessWalk
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

end DeletionGeneralization.WitnessWalk

namespace DeletionGeneralization.EditConnection
open DeletionHash.MixedEdit
universe u

private theorem replace_parts {α : Type*} (b : ℕ) (a u v c : List α)
    (hu : u.length ≤ b) (hv : v.length ≤ b) (hne : u ≠ v) :
    let e : Edit α := ⟨a.length, u.length, v⟩
    ValidEdit b (a ++ u ++ c) e ∧ applyEdit e (a ++ u ++ c) = a ++ v ++ c := by
  dsimp
  constructor
  · simp only [ValidEdit, window, List.length_append]
    refine ⟨by omega, hu, hv, ?_⟩
    simpa [List.append_assoc] using hne
  · simp [applyEdit, List.append_assoc, ← List.drop_drop]

private theorem reverse_edit {α : Type*} {b : ℕ} {x : List α} {e : Edit α}
    (he : ValidEdit b x e) :
    ∃ f : Edit α, ValidEdit b (applyEdit e x) f ∧ applyEdit f (applyEdit e x) = x := by
  let a := x.take e.position
  let u := window e.removed x e.position
  let c := x.drop (e.position + e.removed)
  have hp : e.position ≤ x.length := by have := he.1; omega
  have ha : a.length = e.position := by simp [a, List.length_take, Nat.min_eq_left hp]
  have hu : u.length = e.removed := by
    simp only [u, window, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by have := he.1; omega)
  have hx : a ++ u ++ c = x := by
    dsimp [a, u, c, window]
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hy : applyEdit e x = a ++ e.replacement ++ c := rfl
  let f : Edit α := ⟨a.length, e.replacement.length, u⟩
  obtain ⟨hf, hback⟩ := replace_parts b a e.replacement u c he.2.2.1
    (by rw [hu]; exact he.2.1) (Ne.symm he.2.2.2)
  exact ⟨f, by simpa only [hy] using hf, by simpa only [hy, hx] using hback⟩

private theorem append_valid {α : Type*} {b : ℕ} {x : List α}
    {r s : List (Edit α)} (hr : ValidRecord b x r)
    (hs : ValidRecord b (target x r) s) : ValidRecord b x (r ++ s) := by
  induction r generalizing x with
  | nil => simpa [target] using hs
  | cons e r ih =>
    exact ⟨hr.1, ih hr.2 hs⟩

private theorem reverse_record {α : Type*} {b : ℕ} {x : List α}
    {r : List (Edit α)} (hr : ValidRecord b x r) :
    ∃ s : List (Edit α), s.length = r.length ∧
      ValidRecord b (target x r) s ∧ target (target x r) s = x := by
  induction r generalizing x with
  | nil => exact ⟨[], rfl, trivial, rfl⟩
  | cons e r ih =>
    obtain ⟨s, hlen, hs, htarget⟩ := ih hr.2
    obtain ⟨f, hf, hback⟩ := reverse_edit hr.1
    refine ⟨s ++ [f], by simp [hlen], append_valid hs ?_, ?_⟩
    · change ValidRecord b (target (target (applyEdit e x) r) s) [f]
      rw [htarget]
      exact ⟨hf, trivial⟩
    · change target (target (applyEdit e x) r) (s ++ [f]) = x
      simp only [target, List.foldl_append, List.foldl_cons, List.foldl_nil] at htarget ⊢
      rw [htarget]
      exact hback

theorem connect {α : Type u} [Fintype α] [DecidableEq α]
    (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (hq : 2 ≤ Fintype.card α)
    (x z : List α) (hne : x ≠ z) (hconf : Confusable b t x z) :
    ∃ record : List (Edit α), record.length ≤ 2*t ∧ ValidRecord b x record ∧ target x record = z := by
  obtain ⟨y, ⟨r, hrlen, hr, hry⟩, ⟨s, hslen, hs, hsy⟩⟩ := hconf
  obtain ⟨s', hs'len, hs', hs'target⟩ := reverse_record hs
  have hsame : target x r = target z s := hry.trans hsy.symm
  refine ⟨r ++ s', ?_, append_valid hr (hsame.symm ▸ hs'), ?_⟩
  · simp only [List.length_append, hs'len]
    omega
  · have happ : target x (r ++ s') = target (target x r) s' := List.foldl_append
    rw [happ]
    rw [hsame]
    exact hs'target

end DeletionGeneralization.EditConnection
namespace DeletionGeneralization.SourceLetters
open DeletionHash.MixedEdit
universe u
variable {α : Type u}

theorem common_block (m k b i j a c u v : ℕ) (hu : u ≤ b) (hv : v ≤ b)
    (hm : 3*k+2*b ≤ m) :
    ∃ o, o+k ≤ m ∧ (i+o+k ≤ a ∨ a+u ≤ i+o) ∧
      (j+o+k ≤ c ∨ c+v ≤ j+o) := by
  by_cases h0 : (i+k ≤ a ∨ a+u ≤ i) ∧ (j+k ≤ c ∨ c+v ≤ j)
  · exact ⟨0, by omega, by simpa using h0.1, by simpa using h0.2⟩
  by_cases h1 : (i+(k+b)+k ≤ a ∨ a+u ≤ i+(k+b)) ∧
      (j+(k+b)+k ≤ c ∨ c+v ≤ j+(k+b))
  · exact ⟨k+b, by omega, h1⟩
  refine ⟨2*(k+b), by omega, ?_⟩
  omega

theorem edited_length (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length) :
    (applyEdit e x).length = e.position+e.replacement.length+(x.length-(e.position+e.removed)) := by
  simp [applyEdit, List.length_take, Nat.min_eq_left (show e.position ≤ x.length by omega), Nat.add_assoc]

theorem word_before (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (a : ℕ) (ha : a < e.position) : (applyEdit e x)[a]? = x[a]? := by
  simp [applyEdit, List.getElem?_append, List.getElem?_take,
    Nat.min_eq_left (show e.position ≤ x.length by omega), ha]

theorem word_after (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (a : ℕ) (ha : e.position+e.replacement.length ≤ a) :
    (applyEdit e x)[a]? = x[a-e.replacement.length+e.removed]? := by
  have hp : e.position ≤ x.length := by omega
  simp only [applyEdit, List.getElem?_append, List.length_append, List.length_take,
    Nat.min_eq_left hp, if_neg (show ¬ a < e.position+e.replacement.length by omega),
    List.getElem?_drop]
  congr 1
  omega

theorem trace_before (x : List α) (e : Edit α) (a : ℕ) (ha : a < e.position) :
    (sourceTrace x (some e))[a]? = some (some a) := by
  simp [sourceTrace, List.getElem?_append, List.getElem?_map, ha]

theorem trace_after (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (a : ℕ) (ha : e.position+e.replacement.length ≤ a)
    (hb : a < (applyEdit e x).length) :
    (sourceTrace x (some e))[a]? = some (some (a-e.replacement.length+e.removed)) := by
  rw [edited_length x e he] at hb
  simp only [sourceTrace, List.getElem?_append, List.length_append, List.length_map,
    List.length_range, List.length_replicate,
    if_neg (show ¬ a < e.position+e.replacement.length by omega), List.getElem?_map]
  simp [List.getElem?_range', show a-(e.position+e.replacement.length) <
    x.length-(e.position+e.removed) by omega]
  omega


def cut (e : Option (Edit α)) : ℕ := e.elim 0 Edit.position
def newLength (e : Option (Edit α)) : ℕ := e.elim 0 (fun e => e.replacement.length)

theorem original_block (x : List α) (e : Option (Edit α)) (b a k : ℕ)
    (he : ValidOne b x e) (ha : a+k ≤ (oneWord x e).length)
    (hside : a+k ≤ cut e ∨ cut e+newLength e ≤ a) :
    ∃ s, s+k ≤ x.length ∧ ∀ h, h < k →
      (oneWord x e)[a+h]? = x[s+h]? ∧
      (sourceTrace x e)[a+h]? = some (some (s+h)) := by
  cases e with
  | none =>
    refine ⟨a, ha, ?_⟩
    intro h hh
    exact ⟨rfl, by simp [sourceTrace, show a+h < x.length by simpa [oneWord] using (show a+h < (oneWord x none).length by omega)]⟩
  | some e =>
    change ValidEdit b x e at he
    have he0 := he.1
    change a+k ≤ (applyEdit e x).length at ha
    change a+k ≤ e.position ∨ e.position+e.replacement.length ≤ a at hside
    rcases hside with hside | hside
    · refine ⟨a, by omega, ?_⟩
      intro h hh
      exact ⟨word_before x e he.1 (a+h) (by omega), trace_before x e (a+h) (by omega)⟩
    · refine ⟨a-e.replacement.length+e.removed, ?_, ?_⟩
      · rw [edited_length x e he.1] at ha
        omega
      · intro h hh
        have hid : a+h-e.replacement.length+e.removed =
            (a-e.replacement.length+e.removed)+h := by omega
        constructor
        · change (applyEdit e x)[a+h]? = _
          rw [word_after x e he.1 (a+h) (by omega), hid]
        · rw [trace_after x e he.1 (a+h) (by omega) (by omega), hid]

theorem trace_position (x : List α) (e : Edit α) (p s : ℕ)
    (h : (sourceTrace x (some e))[p]? = some (some s)) :
    (p < e.position ∧ s=p) ∨
      (e.position+e.replacement.length ≤ p ∧ s=p-e.replacement.length+e.removed) := by
  by_cases hp : p < e.position
  · rw [trace_before x e p hp] at h
    exact Or.inl ⟨hp, (Option.some.inj (Option.some.inj h)).symm⟩
  · right
    by_cases hn : p < e.position+e.replacement.length
    · simp [sourceTrace, List.getElem?_append, hp,
        show p-e.position < e.replacement.length by omega] at h
    · refine ⟨by omega, ?_⟩
      simp only [sourceTrace, List.getElem?_append, List.length_append, List.length_map,
        List.length_range, List.length_replicate, if_neg hn, List.getElem?_map] at h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp h
      simp only [List.getElem_range'] at hv
      omega

theorem trace_injective (x : List α) (e : Option (Edit α)) (p q s : ℕ)
    (hp : (sourceTrace x e)[p]? = some (some s))
    (hq : (sourceTrace x e)[q]? = some (some s)) : p=q := by
  cases e with
  | none =>
    simp [sourceTrace, Option.map_eq_some_iff] at hp hq
    obtain ⟨hp', hvp⟩ := List.getElem?_eq_some_iff.mp hp
    obtain ⟨hq', hvq⟩ := List.getElem?_eq_some_iff.mp hq
    simp only [List.getElem_range] at hvp hvq
    omega
  | some e =>
    have h1 := trace_position x e p s hp
    have h2 := trace_position x e q s hq
    omega


theorem newLength_le (x : List α) (e : Option (Edit α)) (b : ℕ)
    (he : ValidOne b x e) : newLength e ≤ b := by
  cases e with
  | none => simp [newLength]
  | some e => exact he.2.2.1

theorem shared [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b k m : ℕ) (hm : 3*k+2*b ≤ m)
    (x : Word α n) (hx : IsUnique k (letters x))
    (e f : Option (Edit α)) (he : ValidOne b (letters x) e) (hf : ValidOne b (letters x) f)
    (i j : ℕ) (hi : i+m ≤ (oneWord (letters x) e).length)
    (hj : j+m ≤ (oneWord (letters x) f).length)
    (heq : window m (oneWord (letters x) e) i = window m (oneWord (letters x) f) j) :
    ∃ o : ℕ, o+k ≤ m ∧ ∀ h : ℕ, h < k → ∃ s : ℕ,
      (sourceTrace (letters x) e)[i+o+h]? = some (some s) ∧
      (sourceTrace (letters x) f)[j+o+h]? = some (some s) := by
  obtain ⟨o, ho, hoe, hof⟩ := common_block m k b i j (cut e) (cut f)
    (newLength e) (newLength f) (newLength_le _ e b he) (newLength_le _ f b hf) hm
  obtain ⟨s, hs, hse⟩ := original_block (letters x) e b (i+o) k he (by omega) (by simpa [Nat.add_assoc] using hoe)
  obtain ⟨v, hv, hvf⟩ := original_block (letters x) f b (j+o) k hf (by omega) (by simpa [Nat.add_assoc] using hof)
  have hs' : s+k ≤ n := by simpa [letters] using hs
  have hv' : v+k ≤ n := by simpa [letters] using hv
  have hsv : s=v := by
    apply (UniqueBridge.unique_iff x).mp hx s v hs' hv'
    intro h hh
    have hh' : o+h < m := by omega
    have hg := congrArg (fun l : List α => l[o+h]?) heq
    have hg' : (oneWord (letters x) e)[i+o+h]? = (oneWord (letters x) f)[j+o+h]? := by
      simpa [window, hh', Nat.add_assoc] using hg
    rw [(hse h hh).1, (hvf h hh).1] at hg'
    simpa [OverlapCollision.padBits, letters, show s+h<n by omega, show v+h<n by omega] using hg'
  subst v
  exact ⟨o, ho, fun h hh => ⟨s+h, (hse h hh).2, (hvf h hh).2⟩⟩

theorem unique_after [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b k m : ℕ) (hk : 0 < k) (hm : 3*k+2*b ≤ m)
    (x : Word α n) (hx : IsUnique k (letters x))
    (e : Option (Edit α)) (he : ValidOne b (letters x) e) :
    IsUnique m (oneWord (letters x) e) := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj hij
  simp only [List.mem_range] at hi hj
  by_cases hfit : m ≤ (oneWord (letters x) e).length
  · simp only [if_pos hfit] at hi hj
    obtain ⟨o, ho, hs⟩ := shared b k m hm x hx e e he he i j (by omega) (by omega) hij
    obtain ⟨s, h1, h2⟩ := hs 0 hk
    have h := trace_injective (letters x) e (i+o+0) (j+o+0) s h1 h2
    omega
  · simp [hfit] at hi



end DeletionGeneralization.SourceLetters
namespace DeletionGeneralization.RecordWindows
open DeletionHash.MixedEdit SourceLetters WindowTools
universe u
variable {α : Type u}

theorem before (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (i h : ℕ) (hi : i+h ≤ e.position) :
    window h (applyEdit e x) i=window h x i := by
  have hp : e.position ≤ x.length := by omega
  have ht : (applyEdit e x).take e.position=x.take e.position := by
    simp [applyEdit,List.take_append,List.length_take,Nat.min_eq_left hp]
  calc
    _=window h ((applyEdit e x).take e.position) i := (window_take _ _ _ _ hi).symm
    _=window h (x.take e.position) i := by rw [ht]
    _=window h x i := window_take _ _ _ _ hi

theorem after (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (i h : ℕ) (hi : e.position+e.replacement.length ≤ i) :
    window h (applyEdit e x) i=window h x (i-e.replacement.length+e.removed) := by
  have hp : e.position ≤ x.length := by omega
  have hd : (applyEdit e x).drop (e.position+e.replacement.length)=x.drop (e.position+e.removed) := by
    simp [applyEdit,List.drop_append,List.length_take,Nat.min_eq_left hp]
  have heq : i=(e.position+e.replacement.length)+(i-(e.position+e.replacement.length)) := by omega
  unfold window
  conv_lhs => rw [heq,←List.drop_drop,hd,List.drop_drop]
  congr 2
  omega

theorem pullback_single (b : ℕ) (x : List α) (e : Edit α) (he : ValidEdit b x e)
    (i h : ℕ) (hi : i+h ≤ (applyEdit e x).length)
    (hfar : i+h ≤ e.position ∨ e.position+e.replacement.length ≤ i) :
    ∃ a, a+h ≤ x.length ∧ window h (applyEdit e x) i=window h x a ∧
      a ≤ i+b ∧ i ≤ a+b := by
  have hn := edited_length x e he.1
  rcases hfar with hf | hf
  · exact ⟨i,by have hh:=he.1;omega,before x e he.1 i h hf,by omega,by omega⟩
  · refine ⟨i-e.replacement.length+e.removed,?_,after x e he.1 i h hf,?_,?_⟩
    all_goals have hu:=he.2.1;have hv:=he.2.2.1;have hh:=he.1;omega

theorem pullback (b : ℕ) (x : List α) (record : List (Edit α))
    (hr : ValidRecord b x record) (i h : ℕ) (hi : i+h ≤ (target x record).length)
    (hfar : ∀ e ∈ record,
      i+h+record.length*b ≤ e.position ∨ e.position+(record.length+1)*b ≤ i) :
    ∃ a, a+h ≤ x.length ∧ window h (target x record) i=window h x a ∧
      a ≤ i+record.length*b ∧ i ≤ a+record.length*b := by
  induction record generalizing x with
  | nil => exact ⟨i,hi,rfl,by simp,by simp⟩
  | cons e es ih =>
    have hlen : (e::es).length=es.length+1 := rfl
    have hrest : ∀ f ∈ es, i+h+es.length*b ≤ f.position ∨ f.position+(es.length+1)*b ≤ i := by
      intro f hf
      have hd := hfar f (List.mem_cons_of_mem _ hf)
      rw [hlen] at hd
      rcases hd with hd | hd
      · left; nlinarith
      · right; nlinarith
    obtain ⟨a,ha,heq,ha1,ha2⟩ := ih (applyEdit e x) hr.2 hi hrest
    have hef : a+h ≤ e.position ∨ e.position+e.replacement.length ≤ a := by
      have hd := hfar e (List.mem_cons_self)
      rw [hlen] at hd
      have hb := hr.1.2.2.1
      rcases hd with hd | hd
      · left; nlinarith
      · right; nlinarith
    obtain ⟨c,hc,hec,hc1,hc2⟩ := pullback_single b x e hr.1 a h ha hef
    refine ⟨c,hc,heq.trans hec,?_,?_⟩
    · rw [hlen]; nlinarith
    · rw [hlen]; nlinarith

end DeletionGeneralization.RecordWindows
namespace DeletionGeneralization.RecordStates
open DeletionHash.MixedEdit SourceLetters
universe u
variable {α : Type u}

theorem valid_take (b : ℕ) (x : List α) (r : List (Edit α))
    (hv : ValidRecord b x r) (j : ℕ) : ValidRecord b x (r.take j) := by
  induction r generalizing x j with
  | nil => simp [ValidRecord]
  | cons e r ih =>
    cases j with
    | zero => trivial
    | succ j => exact ⟨hv.1,ih (applyEdit e x) hv.2 j⟩

theorem valid_step (b : ℕ) (x : List α) (r : List (Edit α))
    (hv : ValidRecord b x r) (j : Fin r.length) :
    ValidEdit b (target x (r.take j.val)) (r.get j) := by
  induction r generalizing x with
  | nil => exact Fin.elim0 j
  | cons e r ih =>
    cases j using Fin.cases with
    | zero => exact hv.1
    | succ j => exact ih (applyEdit e x) hv.2 j

theorem length_bounds (b : ℕ) (x : List α) (r : List (Edit α))
    (hv : ValidRecord b x r) :
    (target x r).length ≤ x.length+r.length*b ∧
      x.length ≤ (target x r).length+r.length*b := by
  induction r generalizing x with
  | nil => simp [target]
  | cons e r ih =>
    obtain ⟨h1,h2⟩ := ih (applyEdit e x) hv.2
    have hlen := edited_length x e hv.1.1
    have hu := hv.1.2.1
    have hvv := hv.1.2.2.1
    have hp := hv.1.1
    change (target (applyEdit e x) r).length ≤ x.length+(r.length+1)*b ∧
      x.length ≤ (target (applyEdit e x) r).length+(r.length+1)*b
    constructor <;> nlinarith [Nat.sub_add_cancel hp]

theorem prior_index (r : List (Edit α)) (j : Fin r.length)
    (e : Edit α) (he : e ∈ r.take j.val) :
    ∃ i : Fin r.length, i.val<j.val ∧ r.get i=e := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
  have hib := i.isLt
  simp only [List.length_take] at hib
  have hij : i.val<j.val := by omega
  have hir : i.val<r.length := by omega
  refine ⟨⟨i.val,hir⟩,hij,?_⟩
  simpa only [List.get_eq_getElem,List.getElem_take] using hi

end DeletionGeneralization.RecordStates
namespace DeletionGeneralization.SeparatedWindows
open DeletionHash.MixedEdit RecordStates WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem source_window (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (r : List (Edit α))
    (hv : ValidRecord b (letters x) r) (hlen : r.length=2*t)
    (hsep : Separated n t b L r) (j : Fin r.length) :
    let p := (r.get j).position
    let M := 2*(L+b)
    let W := window (2*M+b) (target (letters x) (r.take j.val)) (p-M)
    ∃ a, a+(2*M+b) ≤ n ∧ W=window (2*M+b) (letters x) a ∧
      a ≤ p-M+j.val*b ∧ p-M ≤ a+j.val*b ∧ IsUnique k W ∧ W.length=2*M+b := by
  dsimp
  let p := (r.get j).position
  let M := 2*(L+b)
  let s := r.take j.val
  have ht : 2 ≤ t := hreg.2.1
  have hb : 1 ≤ b := hreg.2.2.1
  have hL : L=3*(k+b+1) := hreg.2.2.2.2.1
  have hj : j.val < 2*t := by simpa only [hlen] using j.isLt
  have hjs : s.length=j.val := by
    dsimp [s]
    rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  have hvalid : ValidRecord b (letters x) s := valid_take b (letters x) r hv j.val
  have hmargin := hsep.1 (r.get j) (List.get_mem _ _)
  change 8*(L+t*b) ≤ p ∧ p+8*(L+t*b) ≤ n at hmargin
  have hbudget : M+(j.val+1)*b ≤ 8*(L+t*b) := by
    dsimp [M]
    have hmul := Nat.mul_le_mul_right b (show j.val+1 ≤ 2*t by omega)
    nlinarith
  have hpM : M ≤ p := by nlinarith [hmargin.1]
  have hxy := length_bounds b (letters x) s hvalid
  have hxlen : (letters x).length=n := by simp [letters]
  rw [hjs,hxlen] at hxy
  have hwin : p-M+(2*M+b) ≤ (target (letters x) s).length := by
    nlinarith [hmargin.2,Nat.sub_add_cancel hpM]
  have hfar : ∀ e ∈ s,
      p-M+(2*M+b)+s.length*b ≤ e.position ∨ e.position+(s.length+1)*b ≤ p-M := by
    intro e he
    obtain ⟨i,hij,hie⟩ := prior_index r j e he
    have hne : i ≠ j := by intro h; subst i; omega
    have hd := hsep.2 i j hne
    rw [hie] at hd
    change 8*(L+t*b) ≤ Nat.dist e.position p at hd
    rw [hjs]
    rcases Nat.le_total e.position p with hep | hpe
    · right
      rw [Nat.dist_eq_sub_of_le hep] at hd
      have hgap : e.position+8*(L+t*b) ≤ p := by omega
      nlinarith [Nat.sub_add_cancel hpM]
    · left
      rw [Nat.dist_eq_sub_of_le_right hpe] at hd
      have hgap : p+8*(L+t*b) ≤ e.position := by omega
      nlinarith [Nat.sub_add_cancel hpM]
  obtain ⟨a,ha,he,ha1,ha2⟩ := RecordWindows.pullback b (letters x) s hvalid
    (p-M) (2*M+b) hwin hfar
  rw [hxlen] at ha
  rw [hjs] at ha1 ha2
  have hu : IsUnique k (window (2*M+b) (target (letters x) s) (p-M)) := by
    rw [he]
    exact unique_subwindow hx a (2*M+b) (by rwa [hxlen])
  have hwlen : (window (2*M+b) (target (letters x) s) (p-M)).length=2*M+b := by
    simp only [window,List.length_take,List.length_drop]
    omega
  exact ⟨a,ha,he,ha1,ha2,hu,hwlen⟩

end DeletionGeneralization.SeparatedWindows
namespace DeletionGeneralization.EditedPrefix
open DeletionHash.MixedEdit SourceLetters UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem prefix_get {x y : List α} {l i : ℕ} (h : x.take l = y.take l) (hi : i < l) :
    x[i]? = y[i]? := by
  have hg := congrArg (fun z : List α => z[i]?) h
  simpa [hi] using hg

theorem word_new (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (i : ℕ) (hi : i < e.replacement.length) :
    (applyEdit e x)[e.position+i]? = e.replacement[i]? := by
  have hp : e.position ≤ x.length := by omega
  simp [applyEdit, List.getElem?_append, Nat.min_eq_left hp,
    show ¬ e.position+i < e.position by omega, hi]

theorem prefix_bound {n k b : ℕ} (x : Word α n) (hx : IsUnique k (letters x))
    (e : Edit α) (he : ValidEdit b (letters x) e) (l : ℕ)
    (hlx : l ≤ n) (hly : l ≤ (applyEdit e (letters x)).length)
    (hpref : (letters x).take l = (applyEdit e (letters x)).take l) :
    l < e.position+k+b := by
  by_contra hbound
  have hu := he.2.1
  have hv := he.2.2.1
  have hpos : e.position+e.removed ≤ n := by simpa [letters] using he.1
  have hylen := edited_length (letters x) e he.1
  rw [show (letters x).length=n by simp [letters]] at hylen
  let a := e.position+b
  let c := a-e.replacement.length+e.removed
  have ha : a+k ≤ n := by dsimp [a]; omega
  have hc : c+k ≤ n := by dsimp [c,a]; omega
  have hac : a=c := by
    apply (unique_iff x).mp hx a c ha hc
    intro i hi
    have hidx : a+i-e.replacement.length+e.removed = c+i := by dsimp [a,c]; omega
    have hg := prefix_get hpref (show a+i<l by dsimp [a]; omega)
    rw [word_after (letters x) e he.1 (a+i) (by dsimp [a]; omega), hidx] at hg
    simpa [OverlapCollision.padBits, letters, show a+i<n by omega, show c+i<n by omega] using hg
  have huv : e.removed=e.replacement.length := by dsimp [a,c] at hac; omega
  apply he.2.2.2
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop, letters, List.length_ofFn]
    omega
  · intro i hi hj
    have hidx : e.position+i < (letters x).length := by
      simp only [letters, List.length_ofFn]
      omega
    have hg := prefix_get hpref (show e.position+i<l by omega)
    rw [word_new (letters x) e he.1 i hj] at hg
    simp only [window, List.getElem_take, List.getElem_drop]
    simpa only [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj,
      Option.some.injEq] using hg

end DeletionGeneralization.EditedPrefix
namespace DeletionGeneralization.EditedSuffix
open DeletionHash.MixedEdit SourceLetters UniqueBridge EditedPrefix
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem suffix_bound {n k b : ℕ} (x : Word α n) (hx : IsUnique k (letters x))
    (e : Edit α) (he : ValidEdit b (letters x) e) (s : ℕ)
    (hsx : s ≤ n) (hsy : s ≤ (applyEdit e (letters x)).length)
    (hsuff : (letters x).drop (n-s) =
      (applyEdit e (letters x)).drop ((applyEdit e (letters x)).length-s)) :
    s < n-(e.position+e.removed)+k+b := by
  by_contra hbound
  have hu := he.2.1
  have hv := he.2.2.1
  have hpos : e.position+e.removed ≤ n := by simpa [letters] using he.1
  have hylen := edited_length (letters x) e he.1
  rw [show (letters x).length=n by simp [letters]] at hylen
  let a := e.position+e.removed-(k+b)
  let d := e.position+e.replacement.length-(k+b)
  let o := a-(n-s)
  have hfit : k+b ≤ e.position+e.removed ∧ k+b ≤ e.position+e.replacement.length := by omega
  have ha : a+k ≤ e.position := by dsimp [a]; omega
  have hd : d+k ≤ e.position := by dsimp [d]; omega
  have hbase : n-s+o=a := by dsimp [o,a]; omega
  have hbase' : (applyEdit e (letters x)).length-s+o=d := by dsimp [o,a,d]; omega
  have had : a=d := by
    apply (unique_iff x).mp hx a d (by omega) (by omega)
    intro i hi
    have hg := congrArg (fun z : List α => z[o+i]?) hsuff
    have hg' : (letters x)[a+i]? = (applyEdit e (letters x))[d+i]? := by
      simpa only [List.getElem?_drop, ← Nat.add_assoc, hbase, hbase'] using hg
    rw [word_before (letters x) e he.1 (d+i) (by omega)] at hg'
    simpa [OverlapCollision.padBits, letters, show a+i<n by omega, show d+i<n by omega] using hg'
  have huv : e.removed=e.replacement.length := by dsimp [a,d] at had; omega
  have hylen' : (applyEdit e (letters x)).length=n := by omega
  rw [hylen'] at hsuff
  apply he.2.2.2
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop, letters, List.length_ofFn]
    omega
  · intro i hi hj
    have hidx : e.position+i < (letters x).length := by
      simp only [letters, List.length_ofFn]
      omega
    have hg := congrArg (fun z : List α => z[e.position-(n-s)+i]?) hsuff
    have hstart : n-s+(e.position-(n-s)+i)=e.position+i := by omega
    have hg' : (letters x)[e.position+i]? = (applyEdit e (letters x))[e.position+i]? := by
      simpa only [List.getElem?_drop, hstart] using hg
    rw [word_new (letters x) e he.1 i hj] at hg'
    simp only [window, List.getElem_take, List.getElem_drop]
    simpa only [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj,
      Option.some.injEq] using hg'

end DeletionGeneralization.EditedSuffix
namespace DeletionGeneralization.EditEndpoints
open DeletionHash.MixedEdit EditedPrefix
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem exists_best (bound : ℕ) (P : ℕ → Prop) (hzero : P 0) :
    ∃ l, l ≤ bound ∧ P l ∧ ∀ j, j ≤ bound → P j → j ≤ l := by
  classical
  let S := (Finset.range (bound+1)).filter P
  have hS : S.Nonempty := ⟨0, by simp [S,hzero]⟩
  have hm := Finset.mem_filter.mp (Finset.max'_mem S hS)
  refine ⟨S.max' hS, ?_, hm.2, ?_⟩
  · have h := Finset.mem_range.mp hm.1
    omega
  · intro j hj hp
    exact Finset.le_max' S j (by simp [S,hp]; omega)

theorem prefix_next (x y : List α) (l : ℕ) (hx : l < x.length) (hy : l < y.length)
    (he : x.take l = y.take l)
    (hmax : ∀ j, j ≤ min x.length y.length → x.take j = y.take j → j ≤ l) :
    x[l]? ≠ y[l]? := by
  intro hnext
  have he' : x.take (l+1) = y.take (l+1) := by
    apply List.ext_getElem
    · simp only [List.length_take]
      omega
    · intro i hi hj
      have hi' : i < l+1 := by
        have h := hi
        simp only [List.length_take] at h
        omega
      have hix : i < x.length := by omega
      have hiy : i < y.length := by omega
      simp only [List.getElem_take]
      have hg : x[i]? = y[i]? := by
        by_cases hil : i < l
        · exact prefix_get he hil
        · have hil : i=l := by omega
          simpa only [hil] using hnext
      simpa only [List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hiy,
        Option.some.injEq] using hg
  have h := hmax (l+1) (by omega) he'
  omega

theorem suffix_prev (x y : List α) (s : ℕ) (hx : s < x.length) (hy : s < y.length)
    (he : x.drop (x.length-s) = y.drop (y.length-s))
    (hmax : ∀ j, j ≤ min x.length y.length →
      x.drop (x.length-j) = y.drop (y.length-j) → j ≤ s) :
    x[x.length-s-1]? ≠ y[y.length-s-1]? := by
  intro hprev
  have he' : x.drop (x.length-(s+1)) = y.drop (y.length-(s+1)) := by
    apply List.ext_getElem
    · simp only [List.length_drop]
      omega
    · intro i hi hj
      have hix : x.length-(s+1)+i < x.length := by
        simp only [List.length_drop] at hi
        omega
      have hiy : y.length-(s+1)+i < y.length := by
        simp only [List.length_drop] at hj
        omega
      simp only [List.getElem_drop]
      have hg : x[x.length-(s+1)+i]? = y[y.length-(s+1)+i]? := by
        by_cases hi0 : i=0
        · subst i
          simpa only [Nat.add_zero, Nat.sub_add_eq] using hprev
        · have h := congrArg (fun z : List α => z[i-1]?) he
          have h1 : x.length-s+(i-1)=x.length-(s+1)+i := by omega
          have h2 : y.length-s+(i-1)=y.length-(s+1)+i := by omega
          simpa only [List.getElem?_drop,h1,h2] using h
      simpa only [List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hiy,
        Option.some.injEq] using hg
  have h := hmax (s+1) (by omega) he'
  omega


structure MatchingEnds (x y : List α) where
  prefixLen : ℕ
  suffixLen : ℕ
  prefix_le : prefixLen ≤ min x.length y.length
  suffix_le : suffixLen ≤ min x.length y.length
  prefix_eq : x.take prefixLen = y.take prefixLen
  suffix_eq : x.drop (x.length-suffixLen) = y.drop (y.length-suffixLen)
  prefix_max : ∀ j, j ≤ min x.length y.length → x.take j = y.take j → j ≤ prefixLen
  suffix_max : ∀ j, j ≤ min x.length y.length →
    x.drop (x.length-j) = y.drop (y.length-j) → j ≤ suffixLen

theorem matchingEnds_exist (x y : List α) : Nonempty (MatchingEnds x y) := by
  obtain ⟨l, hl, he, hm⟩ := exists_best (min x.length y.length)
    (fun j => x.take j=y.take j) (by simp)
  obtain ⟨s, hs, he', hm'⟩ := exists_best (min x.length y.length)
    (fun j => x.drop (x.length-j)=y.drop (y.length-j)) (by simp)
  exact ⟨⟨l,s,hl,hs,he,he',hm,hm'⟩⟩

theorem unchanged_prefix (x : List α) (e : Edit α)
    (he : e.position+e.removed ≤ x.length) :
    x.take e.position = (applyEdit e x).take e.position := by
  have hp : e.position ≤ x.length := by omega
  simp [applyEdit, List.take_append, Nat.min_eq_left hp]

theorem unchanged_suffix (x : List α) (e : Edit α)
    (he : e.position+e.removed ≤ x.length) :
    x.drop (e.position+e.removed) = (applyEdit e x).drop (e.position+e.replacement.length) := by
  have hp : e.position ≤ x.length := by omega
  simp [applyEdit, List.drop_append, Nat.min_eq_left hp]

theorem matchingEnds_bounds {n k b : ℕ} (x : Word α n) (hx : IsUnique k (letters x))
    (e : Edit α) (he : ValidEdit b (letters x) e)
    (ends : MatchingEnds (letters x) (applyEdit e (letters x))) :
    e.position ≤ ends.prefixLen ∧ ends.prefixLen < e.position+k+b ∧
      n-(e.position+e.removed) ≤ ends.suffixLen ∧
      ends.suffixLen < n-(e.position+e.removed)+k+b := by
  have hxlen : (letters x).length=n := by simp [letters]
  have hp : e.position+e.removed ≤ n := by simpa only [hxlen] using he.1
  have hylen := SourceLetters.edited_length (letters x) e he.1
  rw [hxlen] at hylen
  have hl := ends.prefix_le
  have hs := ends.suffix_le
  rw [hxlen] at hl hs
  refine ⟨?_, prefix_bound x hx e he ends.prefixLen (by omega) (by omega) ends.prefix_eq,
    ?_, EditedSuffix.suffix_bound x hx e he ends.suffixLen (by omega) (by omega) ?_⟩
  · apply ends.prefix_max
    · rw [hxlen]
      omega
    · exact unchanged_prefix _ e he.1
  · apply ends.suffix_max
    · rw [hxlen]
      omega
    · rw [hxlen]
      have h1 : n-(n-(e.position+e.removed))=e.position+e.removed := by omega
      have h2 : (applyEdit e (letters x)).length-(n-(e.position+e.removed))=
          e.position+e.replacement.length := by omega
      rw [h1,h2]
      exact unchanged_suffix _ e he.1
  · simpa only [hxlen] using ends.suffix_eq


end DeletionGeneralization.EditEndpoints
namespace DeletionGeneralization.LocalGeometry
open DeletionHash.MixedEdit SourceLetters EditEndpoints
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem common_windows {n b k L : ℕ} (hb : 1 ≤ b) (hL : L=3*(k+b+1)) (hbk : b<k)
    (x : Word α n) (hx : IsUnique k (letters x)) (e : Edit α)
    (he : ValidEdit b (letters x) e) (hleft : 2*(L+b) ≤ e.position)
    (hright : e.position+e.removed+2*(L+b) ≤ n)
    (ends : MatchingEnds (letters x) (applyEdit e (letters x)))
    (i j : ℕ)
    (hi : ends.prefixLen-(L-1) ≤ i ∧ i ≤ n-ends.suffixLen)
    (hj : ends.prefixLen-(L-1) ≤ j ∧ j ≤ (applyEdit e (letters x)).length-ends.suffixLen)
    (hw : window (L-1) (letters x) i = window (L-1) (applyEdit e (letters x)) j) :
    (i=ends.prefixLen-(L-1) ∧ j=ends.prefixLen-(L-1)) ∨
      (i=n-ends.suffixLen ∧ j=(applyEdit e (letters x)).length-ends.suffixLen) := by
  have hxu : (letters x).length=n := by simp [letters]
  have hu := he.2.1
  have hv := he.2.2.1
  have hp : e.position+e.removed ≤ n := by simpa only [hxu] using he.1
  have hylen := edited_length (letters x) e he.1
  rw [hxu] at hylen
  obtain ⟨hl0,hl1,hs0,hs1⟩ := matchingEnds_bounds x hx e he ends
  have hpl : ends.prefixLen < n := by omega
  have hpr : ends.prefixLen < (applyEdit e (letters x)).length := by omega
  have hsl : ends.suffixLen < n := by omega
  have hsr : ends.suffixLen < (applyEdit e (letters x)).length := by omega
  have hml : L-1 ≤ ends.prefixLen := by omega
  have hms : L-1 ≤ ends.suffixLen := by omega
  have hwi : i+(L-1) ≤ n := by omega
  have hwj : j+(L-1) ≤ (applyEdit e (letters x)).length := by omega
  obtain ⟨o,ho,hs⟩ := shared b k (L-1) (by omega) x hx none (some e)
    (by trivial) he i j (by simpa only [oneWord,hxu] using hwi) hwj hw
  obtain ⟨s,hsi,hsj⟩ := hs 0 (by omega)
  simp only [Nat.add_zero] at hsi hsj
  have hio : i+o<n := by omega
  have hsrc : i+o=s := by simpa [sourceTrace,hxu,hio] using hsi
  obtain hbefore | hafter := trace_position (letters x) e (j+o) s hsj
  · have hij : i=j := by omega
    have hia : i=ends.prefixLen-(L-1) := by
      by_contra hne
      have hoff : ends.prefixLen-i < L-1 := by omega
      have hidx : i+(ends.prefixLen-i)=ends.prefixLen := by omega
      have hidx' : j+(ends.prefixLen-i)=ends.prefixLen := by omega
      have hg := congrArg (fun z : List α => z[ends.prefixLen-i]?) hw
      have heq : (letters x)[ends.prefixLen]? = (applyEdit e (letters x))[ends.prefixLen]? := by
        simpa [window,hoff,hidx,hidx'] using hg
      exact prefix_next (letters x) (applyEdit e (letters x)) ends.prefixLen
        (by simpa only [hxu] using hpl) hpr ends.prefix_eq ends.prefix_max heq
    exact Or.inl ⟨hia,by omega⟩
  · have hij : i+e.replacement.length=j+e.removed := by omega
    have hcross : n-ends.suffixLen ≤ i+o := by omega
    have halign : n-ends.suffixLen+e.replacement.length =
        (applyEdit e (letters x)).length-ends.suffixLen+e.removed := by omega
    have hic : i=n-ends.suffixLen := by
      by_contra hne
      have hoff : n-ends.suffixLen-1-i < L-1 := by omega
      have hidx : i+(n-ends.suffixLen-1-i)=n-ends.suffixLen-1 := by omega
      have hidx' : j+(n-ends.suffixLen-1-i)=
          (applyEdit e (letters x)).length-ends.suffixLen-1 := by omega
      have hg := congrArg (fun z : List α => z[n-ends.suffixLen-1-i]?) hw
      have heq : (letters x)[n-ends.suffixLen-1]? =
          (applyEdit e (letters x))[(applyEdit e (letters x)).length-ends.suffixLen-1]? := by
        simpa [window,hoff,hidx,hidx'] using hg
      apply suffix_prev (letters x) (applyEdit e (letters x)) ends.suffixLen
        (by simpa only [hxu] using hsl) hsr ends.suffix_eq ends.suffix_max
      simpa only [hxu] using heq
    exact Or.inr ⟨hic,by omega⟩

end DeletionGeneralization.LocalGeometry
namespace DeletionGeneralization.EditFrame
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u}

theorem frame (x : List α) (e : Edit α) (a c : ℕ)
    (ha : a ≤ e.position) (hc : e.position+e.removed ≤ c) (hcn : c ≤ x.length) :
    ∃ A B X Y : List α,
      x=X++A++window e.removed x e.position++B++Y ∧
      applyEdit e x=X++A++e.replacement++B++Y ∧
      X.length=a ∧ A.length=e.position-a ∧ B.length=c-(e.position+e.removed) := by
  let X := x.take a
  let A := window (e.position-a) x a
  let B := window (c-(e.position+e.removed)) x (e.position+e.removed)
  let Y := x.drop c
  have hp : e.position ≤ x.length := by omega
  have hleft : x.take e.position=X++A := by
    have h : x.take (a+(e.position-a))=x.take a++(x.drop a).take (e.position-a) := List.take_add
    have hidx : a+(e.position-a)=e.position := by omega
    simpa only [hidx,X,A,window] using h
  have hright : x.drop (e.position+e.removed)=B++Y := by
    have h := (List.take_append_drop (c-(e.position+e.removed)) (x.drop (e.position+e.removed))).symm
    have hidx : (e.position+e.removed)+(c-(e.position+e.removed))=c := by omega
    simpa only [List.drop_drop,hidx,B,Y,window] using h
  have hmiddle : x.drop e.position =
      window e.removed x e.position ++ x.drop (e.position+e.removed) := by
    simpa only [window,List.drop_drop] using
      (List.take_append_drop e.removed (x.drop e.position)).symm
  have hword : x=x.take e.position++window e.removed x e.position++x.drop (e.position+e.removed) := by
    rw [List.append_assoc,← hmiddle]
    exact (List.take_append_drop e.position x).symm
  refine ⟨A,B,X,Y,?_,?_,?_,?_,?_⟩
  · rw [hleft,hright] at hword
    simpa only [List.append_assoc] using hword
  · simp only [applyEdit,hleft,hright,List.append_assoc]
  · dsimp [X]
    simp only [List.length_take]
    omega
  · dsimp [A]
    simp only [window,List.length_take,List.length_drop]
    omega
  · dsimp [B]
    simp only [window,List.length_take,List.length_drop]
    omega

end DeletionGeneralization.EditFrame
namespace DeletionGeneralization.SpectrumContext
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u}

theorem windows_append_left (X P : List α) (m : ℕ) (hm : m ≤ P.length) :
    windows (m+1) (X++P) = windows (m+1) (X++P.take m) ++ windows (m+1) P := by
  have hleft : (windows (m+1) (X++P.take m)).length=X.length := by
    rw [windows_length]
    simp only [List.length_append, List.length_take]
    omega
  apply List.ext_getElem
  · simp only [List.length_append, windows_length, List.length_take]
    omega
  · intro i hi hj
    rw [windows_get]
    by_cases hx : i<X.length
    · have hix : i<(windows (m+1) (X++P.take m)).length := by omega
      rw [List.getElem_append_left hix, windows_get]
      have htake : (X++P).take (X.length+m)=X++P.take m := by
        simp [List.take_append]
      rw [← htake, window_take _ _ _ _ (by omega)]
    · have hix : (windows (m+1) (X++P.take m)).length ≤ i := by omega
      rw [List.getElem_append_right hix, windows_get, hleft]
      have hdrop : X.drop i=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_drop]
        omega
      simp [window, List.drop_append, hdrop]

theorem windows_append_right (P Y : List α) (m : ℕ) (hm : m ≤ P.length) :
    windows (m+1) (P++Y) = windows (m+1) P ++
      windows (m+1) (P.drop (P.length-m)++Y) := by
  let A := P.take (P.length-m)
  let S := P.drop (P.length-m)
  have hP : A++S=P := List.take_append_drop _ _
  have hS : S.length=m := by dsimp [S]; simp only [List.length_drop]; omega
  have htake : (S++Y).take m=S := by rw [← hS]; simp
  have h := windows_append_left A (S++Y) m (by simp only [List.length_append,hS]; omega)
  rw [htake] at h
  simpa only [← List.append_assoc,hP,S] using h

theorem windows_context (X P Y : List α) (m : ℕ) (hm : m ≤ P.length) :
    windows (m+1) (X++P++Y) =
      windows (m+1) (X++P.take m) ++ windows (m+1) P ++
        windows (m+1) (P.drop (P.length-m)++Y) := by
  have htake : (P++Y).take m=P.take m := by
    simp [List.take_append, show m-P.length=0 by omega]
  rw [List.append_assoc, windows_append_left X (P++Y) m (by simp only [List.length_append]; omega),
    htake, windows_append_right P Y m hm, List.append_assoc]

theorem spectrum_context [DecidableEq α] (X P Y : List α) (m : ℕ) (hm : m ≤ P.length) :
    spectrum (m+1) (X++P++Y) =
      spectrum (m+1) (X++P.take m) + spectrum (m+1) P +
        spectrum (m+1) (P.drop (P.length-m)++Y) := by
  funext g
  simp only [DeletionHash.MixedEdit.spectrum, windows_context X P Y m hm,
    List.count_append, Nat.cast_add, Pi.add_apply]

theorem context_cancel [DecidableEq α] (X P Q Y : List α) (m : ℕ)
    (hP : m ≤ P.length) (hQ : m ≤ Q.length)
    (hfirst : P.take m=Q.take m)
    (hlast : P.drop (P.length-m)=Q.drop (Q.length-m)) :
    spectrum (m+1) (X++Q++Y)-spectrum (m+1) (X++P++Y) =
      spectrum (m+1) Q-spectrum (m+1) P := by
  rw [spectrum_context X Q Y m hQ,spectrum_context X P Y m hP,hfirst,hlast]
  abel

end DeletionGeneralization.SpectrumContext
namespace DeletionGeneralization.LocalConstruction
open DeletionHash.MixedEdit

universe u

/-- Lemma 2.4: actual flanks and unchanged exterior, full path and length geometry. -/
theorem construct {α : Type u} [Fintype α] [DecidableEq α]
    (n b k L : ℕ) (hq : 2 ≤ Fintype.card α) (hb : 1 ≤ b)
    (hL : L=3*(k+b+1)) (hbk : b<k)
    (x : Word α n) (hx : IsUnique k (letters x)) (e : Edit α)
    (he : ValidEdit b (letters x) e) (hleft : 2*(L+b) ≤ e.position)
    (hright : e.position+e.removed+2*(L+b) ≤ n) :
    let U := window e.removed (letters x) e.position
    ∃ A B X Y : List α,
      letters x = X ++ A ++ U ++ B ++ Y ∧
      applyEdit e (letters x) = X ++ A ++ e.replacement ++ B ++ Y ∧
      e.position = X.length + A.length ∧
      (L-1)-k-b ≤ A.length ∧ A.length ≤ L-1 ∧
      (L-1)-k-b ≤ B.length ∧ B.length ≤ L-1 ∧
      Bubble k L b (A ++ U ++ B) (A ++ e.replacement ++ B) ∧
      spectrum L (applyEdit e (letters x)) - spectrum L (letters x) =
        spectrum L (A ++ e.replacement ++ B) - spectrum L (A ++ U ++ B) := by
  classical
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let m := L-1
  let y := applyEdit e (letters x)
  let U := window e.removed (letters x) e.position
  obtain ⟨ends⟩ := EditEndpoints.matchingEnds_exist (letters x) y
  obtain ⟨hl0,hl1,hs0,hs1⟩ := EditEndpoints.matchingEnds_bounds x hx e he ends
  have hxlen : (letters x).length=n := by simp [letters]
  have hp : e.position+e.removed ≤ n := by simpa only [hxlen] using he.1
  have hu := he.2.1
  have hv := he.2.2.1
  have hylen : y.length=e.position+e.replacement.length+(n-(e.position+e.removed)) := by
    simpa only [hxlen] using SourceLetters.edited_length (letters x) e he.1
  have hm : m=3*k+3*b+2 := by dsimp [m]; omega
  have hLm : L=m+1 := by omega
  have hlm : m ≤ ends.prefixLen := by omega
  have hsm : m ≤ ends.suffixLen := by omega
  have hsl : ends.suffixLen < n := by omega
  have hsr : ends.suffixLen < y.length := by omega
  let a := ends.prefixLen-m
  let c := n-ends.suffixLen
  let d := y.length-ends.suffixLen
  have haeq : a+m=ends.prefixLen := by dsimp [a]; omega
  have hceq : c+ends.suffixLen=n := by dsimp [c]; omega
  have hdeq : d+ends.suffixLen=y.length := by dsimp [d]; omega
  have ha : a ≤ e.position := by omega
  have hc : e.position+e.removed ≤ c+m := by omega
  have hcn : c+m ≤ n := by omega
  have hdn : d+m ≤ y.length := by omega
  have hU : U.length=e.removed := by
    dsimp [U]
    simp only [window,List.length_take,List.length_drop,hxlen]
    omega
  obtain ⟨A,B,X,Y,hframe,hframe',hX,hA,hB⟩ :=
    EditFrame.frame (letters x) e a (c+m) ha hc (by simpa only [hxlen] using hcn)
  let P := A++U++B
  let Q := A++e.replacement++B
  have hword : letters x=X++P++Y := by simpa only [P,U,List.append_assoc] using hframe
  have hword' : y=X++Q++Y := by simpa only [Q,List.append_assoc] using hframe'
  have hAlow : m-k-b ≤ A.length := by omega
  have hAup : A.length ≤ m := by omega
  have hBlow : m-k-b ≤ B.length := by omega
  have hBup : B.length ≤ m := by omega
  have hPlen : P.length=c+m-a := by simp only [P,List.length_append,hU]; omega
  have hQlen : Q.length=d+m-a := by simp only [Q,List.length_append]; omega
  have hPlow : L ≤ P.length := by simp only [P,List.length_append]; omega
  have hQlow : L ≤ Q.length := by simp only [Q,List.length_append]; omega
  have hPup : P.length ≤ 2*m+b := by simp only [P,List.length_append]; omega
  have hQup : Q.length ≤ 2*m+b := by simp only [Q,List.length_append]; omega
  have hPm : m ≤ P.length := by omega
  have hQm : m ≤ Q.length := by omega
  have hP : window P.length (letters x) a=P := by
    rw [hword,← hX]
    exact WindowTools.window_of_append X P Y
  have hQ : window Q.length y a=Q := by
    rw [hword',← hX]
    exact WindowTools.window_of_append X Q Y
  have hfirstP := WindowTools.first_of_window (letters x) P a m hP hPm
  have hfirstQ := WindowTools.first_of_window y Q a m hQ hQm
  have hfirst : P.take m=Q.take m := by
    rw [hfirstP,hfirstQ]
    calc
      window m (letters x) a = window m ((letters x).take ends.prefixLen) a :=
        (WindowTools.window_take _ _ _ _ (by omega)).symm
      _ = window m (y.take ends.prefixLen) a := congrArg (fun z => window m z a) ends.prefix_eq
      _ = window m y a := WindowTools.window_take _ _ _ _ (by omega)
  have hlastP : P.drop (P.length-m)=window m (letters x) c := by
    have h := WindowTools.last_of_window (letters x) P a m hP hPm
    have heq : a+(P.length-m)=c := by omega
    simpa only [heq] using h
  have hlastQ : Q.drop (Q.length-m)=window m y d := by
    have h := WindowTools.last_of_window y Q a m hQ hQm
    have heq : a+(Q.length-m)=d := by omega
    simpa only [heq] using h
  have hlast : P.drop (P.length-m)=Q.drop (Q.length-m) := by
    rw [hlastP,hlastQ]
    have h := congrArg (List.take m) ends.suffix_eq
    simpa only [window,hxlen,c,d] using h
  have hxm : IsUnique m (letters x) := by
    simpa only [oneWord] using SourceLetters.unique_after b k m (by omega) (by omega)
      x hx none (by trivial)
  have hym : IsUnique m y := SourceLetters.unique_after b k m (by omega) (by omega)
    x hx (some e) he
  have hpu : IsUnique m P := by
    rw [← hP]
    exact WindowTools.unique_subwindow hxm a P.length (by rw [hxlen]; omega)
  have hqu : IsUnique m Q := by
    rw [← hQ]
    exact WindowTools.unique_subwindow hym a Q.length (by omega)
  have hpathsP : SpellsSimplePath L P := WindowTools.spells_list L P (by omega) hpu
  have hpathsQ : SpellsSimplePath L Q := WindowTools.spells_list L Q (by omega) hqu
  have hinter : ∀ v, v ∈ PathVertices L P → v ∈ PathVertices L Q →
      List.ofFn v=P.take m ∨ List.ofFn v=P.drop (P.length-m) := by
    intro v hpv hqv
    change List.ofFn v ∈ windows m P at hpv
    change List.ofFn v ∈ windows m Q at hqv
    obtain ⟨i,hi,hepi⟩ := List.mem_map.mp hpv
    obtain ⟨j,hj,heqj⟩ := List.mem_map.mp hqv
    simp only [starts,List.mem_range,if_pos hPm] at hi
    simp only [starts,List.mem_range,if_pos hQm] at hj
    have hip : i+m ≤ P.length := by omega
    have hjq : j+m ≤ Q.length := by omega
    have hepi' : window m (letters x) (a+i)=List.ofFn v := by
      rw [← WindowTools.window_window (letters x) a P.length i m hip,hP,hepi]
    have heqj' : window m y (a+j)=List.ofFn v := by
      rw [← WindowTools.window_window y a Q.length j m hjq,hQ,heqj]
    have h := LocalGeometry.common_windows hb hL hbk x hx e he hleft hright ends (a+i) (a+j)
      (by change a ≤ a+i ∧ a+i ≤ c; constructor <;> omega)
      (by change a ≤ a+j ∧ a+j ≤ d; constructor <;> omega)
      (hepi'.trans heqj'.symm)
    change (a+i=a ∧ a+j=a) ∨ (a+i=c ∧ a+j=d) at h
    rcases h with h | h
    · rw [h.1] at hepi'
      exact Or.inl (hepi'.symm.trans hfirstP.symm)
    · rw [h.1] at hepi'
      exact Or.inr (hepi'.symm.trans hlastP.symm)
  refine ⟨A,B,X,Y,hframe,hframe',?_,hAlow,hAup,hBlow,hBup,?_,?_⟩
  · omega
  · change Bubble k L b P Q
    refine ⟨⟨A,U,e.replacement,B,rfl,rfl,he.2.2.2,?_,hv,hAlow,hAup,hBlow,hBup⟩,
      hPlow,hPup,hQlow,hQup,hfirst,hlast,hpathsP,hpathsQ,hinter⟩
    omega
  · have h := SpectrumContext.context_cancel X P Q Y m hPm hQm hfirst hlast
    rw [← hword',← hword,← hLm] at h
    exact h

end DeletionGeneralization.LocalConstruction

namespace DeletionGeneralization.LocalContext
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u}

theorem apply_context (X W Y : List α) (e : Edit α)
    (he : e.position+e.removed ≤ W.length) :
    applyEdit ⟨X.length+e.position,e.removed,e.replacement⟩ (X++W++Y) =
      X++applyEdit e W++Y := by
  have hp : e.position ≤ W.length := by omega
  simp [applyEdit,List.take_append,List.drop_append,List.append_assoc,
    Nat.min_eq_left hp,Nat.min_eq_left he,Nat.add_assoc,
    List.take_of_length_le (show X.length ≤ X.length+e.position by omega),
    List.drop_eq_nil_of_le (show X.length ≤ X.length+(e.position+e.removed) by omega),
    Nat.sub_eq_zero_of_le hp,Nat.sub_eq_zero_of_le he]

theorem window_context (X W Y : List α) (i h : ℕ) (hi : i+h ≤ W.length) :
    window h (X++W++Y) (X.length+i)=window h W i := by
  have hp : i ≤ W.length := by omega
  simp [window,List.drop_append,List.take_append,List.append_assoc,
    Nat.min_eq_left hp,Nat.min_eq_left (show h ≤ W.length-i by omega),
    List.drop_eq_nil_of_le (show X.length ≤ X.length+i by omega),
    Nat.sub_eq_zero_of_le (show h ≤ W.length-i by omega)]

theorem valid_context [DecidableEq α] (b : ℕ) (X W Y : List α) (e : Edit α)
    (he : ValidEdit b W e) :
    ValidEdit b (X++W++Y) ⟨X.length+e.position,e.removed,e.replacement⟩ := by
  refine ⟨?_,he.2.1,he.2.2.1,?_⟩
  · simp only [List.length_append]
    have h:=he.1
    omega
  · change window e.removed (X++W++Y) (X.length+e.position) ≠ e.replacement
    rw [window_context X W Y e.position e.removed he.1]
    exact he.2.2.2

theorem construct [Fintype α] [DecidableEq α]
    (b k L : ℕ) (hq : 2 ≤ Fintype.card α) (hb : 1 ≤ b)
    (hL : L=3*(k+b+1)) (hbk : b<k)
    (W : List α) (hW : IsUnique k W) (e : Edit α)
    (he : ValidEdit b W e) (hl : 2*(L+b) ≤ e.position)
    (hr : e.position+e.removed+2*(L+b) ≤ W.length) :
    ∃ A B X Y : List α,
      W=X++A++window e.removed W e.position++B++Y ∧
      applyEdit e W=X++A++e.replacement++B++Y ∧
      e.position=X.length+A.length ∧ A.length ≤ L-1 ∧ B.length ≤ L-1 ∧
      Bubble k L b (A++window e.removed W e.position++B) (A++e.replacement++B) := by
  let x : Word α W.length := fun i => W.get i
  have hx : letters x=W := by simp [letters,x]
  obtain ⟨A,B,X,Y,h1,h2,h3,_,h4,_,h5,h6,_⟩ :=
    LocalConstruction.construct W.length b k L hq hb hL hbk x (by rwa [hx]) e
      (by rwa [hx]) hl hr
  exact ⟨A,B,X,Y,by simpa only [hx] using h1,by simpa only [hx] using h2,h3,h4,h5,
    by simpa only [hx] using h6⟩

end DeletionGeneralization.LocalContext
namespace DeletionGeneralization.SeparatedBubble
open DeletionHash.MixedEdit WindowTools RecordStates
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem window_frame (x : List α) (i h : ℕ) :
    x=x.take i++window h x i++x.drop (i+h) := by
  simp only [window,List.append_assoc,←List.drop_drop,List.take_append_drop]

theorem step (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (r : List (Edit α))
    (hv : ValidRecord b (letters x) r) (hlen : r.length=2*t)
    (hsep : Separated n t b L r) (j : Fin r.length) :
    let y := target (letters x) (r.take j.val)
    let e := r.get j
    ∃ (f : Edit α) (P Q : List α) (a : ℕ),
      ValidEdit b (letters x) f ∧ Bubble k L b P Q ∧
      spectrum L (applyEdit e y)-spectrum L y=spectrum L Q-spectrum L P ∧
      window P.length (letters x) a=P ∧
      window Q.length (applyEdit f (letters x)) a=Q ∧
      a+P.length ≤ n ∧ a+Q.length ≤ (applyEdit f (letters x)).length ∧
      a ≤ f.position ∧ f.position ≤ a+(L-1) ∧
      a+P.length ≤ f.position+b+(L-1) ∧ a+Q.length ≤ f.position+b+(L-1) ∧
      f.position ≤ e.position+j.val*b ∧ e.position ≤ f.position+j.val*b := by
  dsimp only
  let e := r.get j
  let y := target (letters x) (r.take j.val)
  let M := 2*(L+b)
  let H := 2*M+b
  let i := e.position-M
  let W := window H y i
  have he : ValidEdit b y e := valid_step b (letters x) r hv j
  have hp0 := hsep.1 (r.get j) (List.get_mem _ _)
  have ht := hreg.2.1
  have hLg := hreg.2.2.2.2.1
  have hp : M ≤ e.position := by
    change 2*(L+b) ≤ (r.get j).position
    nlinarith [hp0.1]
  have hi : i+M=e.position := by dsimp [i];omega
  obtain ⟨a0,ha0,hWsrc,ha1,ha2,hWu,hWlen⟩ := SeparatedWindows.source_window n t b k L hreg x hx r hv hlen hsep j
  change a0+H ≤ n at ha0
  change W=window H (letters x) a0 at hWsrc
  change a0 ≤ i+j.val*b at ha1
  change i ≤ a0+j.val*b at ha2
  change IsUnique k W at hWu
  change W.length=H at hWlen
  let e0 : Edit α := ⟨M,e.removed,e.replacement⟩
  have hu := he.2.1
  have he0 : ValidEdit b W e0 := by
    refine ⟨?_,he.2.1,he.2.2.1,?_⟩
    · change M+e.removed ≤ W.length
      rw [hWlen]
      dsimp [H]
      omega
    · change window e.removed W M ≠ e.replacement
      have h := window_window y i H M e.removed (by dsimp [H];omega)
      change window e.removed W M=window e.removed y (i+M) at h
      rw [h,hi]
      exact he.2.2.2
  obtain ⟨A,B,X,Y,hframe,hframe',hpos,hA,hB,hbubble⟩ := LocalContext.construct b k L
    hreg.1 hreg.2.2.1 hLg hreg.2.2.2.2.2.1 W hWu e0 he0 (by rfl)
      (by change M+e.removed+M ≤ W.length;rw [hWlen];dsimp [H];omega)
  let U := window e.removed W M
  let P := A++U++B
  let Q := A++e.replacement++B
  have hP : W=X++P++Y := by simpa only [P,U,e0,List.append_assoc] using hframe
  have hQ : applyEdit e0 W=X++Q++Y := by simpa only [Q,e0,List.append_assoc] using hframe'
  have hbubble : Bubble k L b P Q := hbubble
  have hU : U.length=e.removed := by
    dsimp [U,window]
    simp only [List.length_take,List.length_drop,hWlen]
    dsimp [H]
    omega
  have hpos : M=X.length+A.length := hpos
  let XS := (letters x).take a0
  let YS := (letters x).drop (a0+H)
  have hXS : XS.length=a0 := by
    dsimp [XS]
    simp only [List.length_take]
    have hxlen : (letters x).length=n := by simp [letters]
    rw [hxlen];omega
  have hsource : letters x=XS++W++YS := by
    rw [hWsrc]
    exact window_frame _ a0 H
  let f : Edit α := ⟨a0+M,e.removed,e.replacement⟩
  have hf : ValidEdit b (letters x) f := by
    rw [hsource]
    simpa only [hXS,e0,f] using LocalContext.valid_context b XS W YS e0 he0
  have hsource' : applyEdit f (letters x)=XS++applyEdit e0 W++YS := by
    rw [hsource]
    simpa only [hXS,e0,f] using LocalContext.apply_context XS W YS e0 he0.1
  have hsourceP : letters x=(XS++X)++P++(Y++YS) := by
    rw [hsource,hP];simp only [List.append_assoc]
  have hsourceQ : applyEdit f (letters x)=(XS++X)++Q++(Y++YS) := by
    rw [hsource',hQ];simp only [List.append_assoc]
  have hylen : i+H ≤ y.length := by
    have h := hWlen
    dsimp [W,window] at h
    simp only [List.length_take,List.length_drop] at h
    dsimp [H,M] at h ⊢
    omega
  let XC := y.take i
  let YC := y.drop (i+H)
  have hXC : XC.length=i := by
    dsimp [XC];simp only [List.length_take];omega
  have hcurrent : y=XC++W++YC := window_frame y i H
  have hcurrent' : applyEdit e y=XC++applyEdit e0 W++YC := by
    rw [hcurrent]
    have heq : e=⟨XC.length+e0.position,e0.removed,e0.replacement⟩ := by
      have h : e.position=XC.length+e0.position := by simpa only [hXC,e0] using hi.symm
      calc
        e=⟨e.position,e.removed,e.replacement⟩ := rfl
        _=⟨XC.length+e0.position,e0.removed,e0.replacement⟩ := by rw [h]
    rw [heq]
    exact LocalContext.apply_context XC W YC e0 he0.1
  have hcurrentP : y=(XC++X)++P++(Y++YC) := by
    rw [hcurrent,hP];simp only [List.append_assoc]
  have hcurrentQ : applyEdit e y=(XC++X)++Q++(Y++YC) := by
    rw [hcurrent',hQ];simp only [List.append_assoc]
  have hspectrum : spectrum L (applyEdit e y)-spectrum L y=spectrum L Q-spectrum L P := by
    have hL1 : 1 ≤ L := by omega
    have h := SpectrumContext.context_cancel (XC++X) P Q (Y++YC) (L-1)
      (by have h:=hbubble.2.1;omega) (by have h:=hbubble.2.2.2.1;omega)
      hbubble.2.2.2.2.2.1 hbubble.2.2.2.2.2.2.1
    have hLe : L-1+1=L := by omega
    rw [hLe,←hcurrentP,←hcurrentQ] at h
    exact h
  refine ⟨f,P,Q,a0+X.length,hf,hbubble,hspectrum,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hsourceP]
    simpa only [List.length_append,hXS] using window_of_append (XS++X) P (Y++YS)
  · rw [hsourceQ]
    simpa only [List.length_append,hXS] using window_of_append (XS++X) Q (Y++YS)
  · have h := congrArg List.length hsourceP
    simp only [List.length_append,hXS,letters,List.length_ofFn] at h
    omega
  · have h := congrArg List.length hsourceQ
    simp only [List.length_append,hXS] at h
    omega
  · dsimp [f];omega
  · dsimp [f];omega
  · dsimp [f,P]
    simp only [List.length_append,hU]
    omega
  · dsimp [f,Q]
    simp only [List.length_append]
    have hvv := he.2.2.1
    omega
  · change a0+M ≤ e.position+j.val*b
    omega
  · change e.position ≤ a0+M+j.val*b
    omega

end DeletionGeneralization.SeparatedBubble
namespace DeletionGeneralization.SeparatedDisjoint
open DeletionHash.MixedEdit SourceLetters WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem trace_shift (b : ℕ) (x : List α) (e : Option (Edit α))
    (he : ValidOne b x e) (i s : ℕ)
    (h : (sourceTrace x e)[i]?=some (some s)) : s ≤ i+b ∧ i ≤ s+b := by
  cases e with
  | none =>
    by_cases hi : i<x.length
    · have hs : i=s := by simpa [sourceTrace,hi] using h
      omega
    · simp [sourceTrace,hi] at h
  | some e =>
    obtain hf | hf := trace_position x e i s h
    · omega
    · have hu := he.2.1
      have hv := he.2.2.1
      omega

theorem positions_close [Nonempty α] {n : ℕ} (b k m : ℕ) (hk : 0<k)
    (hm : 3*k+2*b ≤ m) (x : Word α n) (hx : IsUnique k (letters x))
    (e f : Option (Edit α)) (he : ValidOne b (letters x) e) (hf : ValidOne b (letters x) f)
    (p q i j : ℕ) (hi : i+m ≤ (oneWord (letters x) e).length)
    (hj : j+m ≤ (oneWord (letters x) f).length)
    (hpi : p ≤ i+m) (hip : i ≤ p+b) (hqj : q ≤ j+m) (hjq : j ≤ q+b)
    (hw : window m (oneWord (letters x) e) i=window m (oneWord (letters x) f) j) :
    p ≤ q+2*m+3*b ∧ q ≤ p+2*m+3*b := by
  obtain ⟨o,ho,hs⟩ := shared b k m hm x hx e f he hf i j hi hj hw
  obtain ⟨s,hs1,hs2⟩ := hs 0 hk
  simp only [Nat.add_zero] at hs1 hs2
  have h1 := trace_shift b (letters x) e he (i+o) s hs1
  have h2 := trace_shift b (letters x) f hf (j+o) s hs2
  constructor <;> omega

theorem vertex_window {n b k L : ℕ} (x : Word α n) (f : Edit α)
    (hf : ValidEdit b (letters x) f) (P Q : List α) (a : ℕ)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L)
    (hP : window P.length (letters x) a=P)
    (hQ : window Q.length (applyEdit f (letters x)) a=Q)
    (hnP : a+P.length ≤ n) (hnQ : a+Q.length ≤ (applyEdit f (letters x)).length)
    (hpa : f.position ≤ a+(L-1))
    (hpP : a+P.length ≤ f.position+b+(L-1))
    (hpQ : a+Q.length ≤ f.position+b+(L-1))
    (v : Gram α (L-1)) (hv : v ∈ bubbleVertices L P Q) :
    ∃ (e : Option (Edit α)) (i : ℕ), ValidOne b (letters x) e ∧
      i+(L-1) ≤ (oneWord (letters x) e).length ∧
      window (L-1) (oneWord (letters x) e) i=List.ofFn v ∧
      f.position ≤ i+(L-1) ∧ i ≤ f.position+b := by
  have hmP : L-1 ≤ P.length := by have h:=hB.2.1;omega
  have hmQ : L-1 ≤ Q.length := by have h:=hB.2.2.2.1;omega
  rcases hv with hv | hv
  · change List.ofFn v ∈ windows (L-1) P at hv
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
    simp only [starts,List.mem_range,if_pos hmP] at hi
    have hip : i+(L-1) ≤ P.length := by omega
    refine ⟨none,a+i,by trivial,?_,?_,by omega,by omega⟩
    · simp only [oneWord,letters,List.length_ofFn];omega
    · change window (L-1) (letters x) (a+i)=List.ofFn v
      rw [←window_window _ a P.length i (L-1) hip,hP,he]
  · change List.ofFn v ∈ windows (L-1) Q at hv
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
    simp only [starts,List.mem_range,if_pos hmQ] at hi
    have hiq : i+(L-1) ≤ Q.length := by omega
    refine ⟨some f,a+i,hf,?_,?_,by omega,by omega⟩
    · change a+i+(L-1) ≤ (applyEdit f (letters x)).length
      omega
    · change window (L-1) (applyEdit f (letters x)) (a+i)=List.ofFn v
      rw [←window_window _ a Q.length i (L-1) hiq,hQ,he]

end DeletionGeneralization.SeparatedDisjoint
namespace DeletionGeneralization.SeparatedCoverage
open DeletionHash.MixedEdit SeparatedDisjoint
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem telescope {A : Type v} [AddCommGroup A] (F : List α → A)
    (x : List α) (r : List (Edit α)) :
    F (target x r)-F x =
      ∑ j : Fin r.length,
        (F (applyEdit (r.get j) (target x (r.take j.val)))-F (target x (r.take j.val))) := by
  induction r generalizing x with
  | nil => simp [target]
  | cons e es ih =>
    change F (target x (e::es))-F x = ∑ j : Fin (es.length+1),
      (F (applyEdit ((e::es).get j) (target x ((e::es).take j.val)))-F (target x ((e::es).take j.val)))
    rw [Fin.sum_univ_succ]
    change F (target (applyEdit e x) es)-F x =
      (F (applyEdit e x)-F x)+
        ∑ j : Fin es.length,
          (F (applyEdit (es.get j) (target (applyEdit e x) (es.take j.val)))-
            F (target (applyEdit e x) (es.take j.val)))
    rw [←ih (applyEdit e x)]
    abel

theorem coverage (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (r : List (Edit α))
    (hv : ValidRecord b (letters x) r) (hlen : r.length=2*t)
    (hsep : Separated n t b L r) :
    spectrum L (target (letters x) r)-spectrum L (letters x) ∈ Catalogue k L t b := by
  classical
  letI : Nonempty α := Fintype.card_pos_iff.mp (by have h:=hreg.1;omega)
  choose f P Q a hf hB hs hP hQ hnP hnQ ha hpa hpP hpQ hfp hpf using
    fun j => SeparatedBubble.step n t b k L hreg x hx r hv hlen hsep j
  have hLg : L=3*(k+b+1) := hreg.2.2.2.2.1
  have ht : 2 ≤ t := hreg.2.1
  have hb : 1 ≤ b := hreg.2.2.1
  have hbk : b<k := hreg.2.2.2.2.2.1
  have hL : 1 ≤ L := by omega
  have hdis : ∀ i j : Fin r.length, i ≠ j →
      Disjoint (bubbleVertices L (P i) (Q i)) (bubbleVertices L (P j) (Q j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨e,pi,he,hip,hwi,hpi,hpi'⟩ := vertex_window x (f i) (hf i)
      (P i) (Q i) (a i) (hB i) hL (hP i) (hQ i) (hnP i) (hnQ i)
      (hpa i) (hpP i) (hpQ i) v hvi
    obtain ⟨e',pj,he',hjp,hwj,hpj,hpj'⟩ := vertex_window x (f j) (hf j)
      (P j) (Q j) (a j) (hB j) hL (hP j) (hQ j) (hnP j) (hnQ j)
      (hpa j) (hpP j) (hpQ j) v hvj
    have hc := positions_close b k (L-1) (by omega) (by omega) x hx e e' he he'
      (f i).position (f j).position pi pj hip hjp hpi hpi' hpj hpj'
      (hwi.trans hwj.symm)
    have hd := hsep.2 i j hij
    have hi : i.val ≤ 2*t := by have h:=i.isLt;omega
    have hj : j.val ≤ 2*t := by have h:=j.isLt;omega
    have hib := Nat.mul_le_mul_right b hi
    have hjb := Nat.mul_le_mul_right b hj
    have hfi := hfp i
    have hfj := hfp j
    have hif := hpf i
    have hjf := hpf j
    rcases Nat.le_total (r.get i).position (r.get j).position with hpij | hpji
    · rw [Nat.dist_eq_sub_of_le hpij] at hd
      have hgap : (r.get i).position+8*(L+t*b) ≤ (r.get j).position := by omega
      nlinarith [Nat.sub_le L 1]
    · rw [Nat.dist_eq_sub_of_le_right hpji] at hd
      have hgap : (r.get j).position+8*(L+t*b) ≤ (r.get i).position := by omega
      nlinarith [Nat.sub_le L 1]
  let E : Fin (2*t) ≃ Fin r.length := finCongr hlen.symm
  refine ⟨fun i => (P (E i),Q (E i)),fun i => hB (E i),
    fun i j hij => hdis (E i) (E j) (fun he => hij (E.injective he)),?_⟩
  have hsum := telescope (spectrum L) (letters x) r
  simp_rw [hs] at hsum
  calc
    _ = ∑ j : Fin r.length, (spectrum L (Q j)-spectrum L (P j)) := hsum
    _ = ∑ i : Fin (2*t), (spectrum L (Q (E i))-spectrum L (P (E i))) :=
      (E.sum_comp (fun j => spectrum L (Q j)-spectrum L (P j))).symm

end DeletionGeneralization.SeparatedCoverage
namespace DeletionGeneralization.ConflictRules
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
  obtain ⟨record,hrlen,hvalid,htarget⟩ := EditConnection.connect t b hreg.2.1 hreg.2.2.1 hreg.1
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
  · have h := SeparatedCoverage.coverage n t b k L hreg x.val x.property.1 record hvalid hlen hsep
    simpa only [htarget] using h
  · rw [ExceptionalProbability.hash_sub,sub_eq_zero]
    exact hedge.2.2.symm

end DeletionGeneralization.ConflictRules
namespace DeletionGeneralization.BoundedWitness
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
    apply SpectrumPath.spectrum_boolean
    apply ExceptionalProbability.unique_mono (k := k)
    · have h:=hreg.2.2.2.2.1
      omega
    · exact (verts j).property.1
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

end DeletionGeneralization.BoundedWitness
namespace DeletionGeneralization.ExponentAbsorption
open DeletionHash.MixedEdit

theorem witness_le_cube (t b L : ℕ) (hL : 1+4*t+4*t*b ≤ L) :
    witnessBound t b L ≤ L^3 := by
  have hL1 : 1 ≤ L := by omega
  have hb : 2*L+2*b-2 ≤ 2*L+2*b := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_left (2*t) hb
  have hm' := Nat.mul_le_mul_right L hm
  have hLsq : 1 ≤ L^2 := one_le_pow₀ hL1
  have hconst : (1+4*t+4*t*b)*L^2 ≤ L^3 := by
    calc
      _ ≤ L*L^2 := Nat.mul_le_mul_right _ hL
      _ = L^3 := by ring
  have hterm : 4*t*b*L ≤ 4*t*b*L^2 := by
    apply Nat.mul_le_mul_left
    nlinarith
  unfold witnessBound
  nlinarith [hm',hconst,hterm]

theorem exponent_bound (t b a L : ℕ) (hL : 1+4*t+4*t*b ≤ L) :
    ExponentBound t b a (4*a+2) L := by
  intro R hR hRmax
  have hL1 : 1 ≤ L := by omega
  have hRc : R ≤ L^3 := hRmax.trans (witness_le_cube t b L hL)
  have hpoly : 2*t*R+1 ≤ L^4 := by
    have h1 : 2*t*R+1 ≤ (2*t+1)*R := by nlinarith
    have h2 : (2*t+1)*R ≤ L*L^3 :=
      Nat.mul_le_mul (by omega) hRc
    have he : L*L^3=L^4 := by ring
    omega
  have hpow : L^4 ≤ L^(2*R) := by
    exact Nat.pow_le_pow_right hL1 (by omega)
  have hbase : L*R ≤ L^4 := by
    calc
      _ ≤ L*L^3 := Nat.mul_le_mul_left L hRc
      _ = L^4 := by ring
  calc
    (2*t*R+1)*(L*R)^(a*R) ≤ L^(2*R)*(L^4)^(a*R) :=
      Nat.mul_le_mul (hpoly.trans hpow) (Nat.pow_le_pow_left hbase _)
    _ = L^((4*a+2)*R) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring

theorem eventual (t b a : ℕ) :
    ∃ lam L₀ : ℕ, 2 ≤ lam ∧ 1 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ExponentBound t b a lam L := by
  exact ⟨4*a+2,1+4*t+4*t*b,by omega,by omega,
    fun L hL => exponent_bound t b a L hL⟩

end DeletionGeneralization.ExponentAbsorption
namespace DeletionGeneralization.WitnessCount
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def Family (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R c : ℕ) : Set (Finset (Spectrum α L)) :=
  {F | GeneratingSet k t b v F ∧ F.card=R ∧ componentCount F=c}

def Allowed (t L R c : ℕ) : Prop :=
  c ≤ (2*t-1)*R+1 ∧ (R ≤ L → c ≤ (2*t-1)*R)

def Candidate (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ) (F : Finset (Spectrum α L)) : Prop :=
  GeneratingSet k t b v F ∧ F.card=R ∧ Allowed t L R (componentCount F)

abbrev CIndex (t L R : ℕ) := {c : Fin (2*t*R+1) // Allowed t L R c.val}

noncomputable instance (t L R : ℕ) : Fintype (CIndex t L R) := by
  classical
  unfold CIndex
  infer_instance

theorem index_card (t L R : ℕ) : Fintype.card (CIndex t L R) ≤ 2*t*R+1 := by
  simpa only [Fintype.card_fin] using
    Fintype.card_subtype_le (fun c : Fin (2*t*R+1) => Allowed t L R c.val)

theorem allowed_le {t L R c : ℕ} (ht : 1 ≤ t) (hR : 1 ≤ R) (hc : Allowed t L R c) :
    c ≤ 2*t*R := by
  have hs : (2*t-1)*R+R=2*t*R := by
    calc
      _ = (2*t-1+1)*R := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega)]
  have hh := hc.1
  omega

abbrev Indexed (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ) :=
  Σ c : CIndex t L R, Family k t b v R c.val.val

noncomputable def partition (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ)
    (ht : 1 ≤ t) (hR : 1 ≤ R) :
    {F // Candidate k t b v R F} → Indexed k t b v R :=
  fun F => ⟨⟨⟨componentCount F.val,by have h := allowed_le ht hR F.property.2.2;omega⟩,F.property.2.2⟩,
    ⟨F.val,F.property.1,F.property.2.1,rfl⟩⟩

theorem partition_injective (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ)
    (ht : 1 ≤ t) (hR : 1 ≤ R) : Function.Injective (partition k t b v R ht hR) := by
  intro F H heq
  apply Subtype.ext
  exact congrArg (fun z : Indexed k t b v R => z.2.val) heq

theorem component_power (q t L n R c : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hbonus : L < R → n ≤ q^R) (hc : Allowed t L R c) :
    n^c ≤ q^R*n^((2*t-1)*R) := by
  by_cases hs : R ≤ L
  · calc
      _ ≤ n^((2*t-1)*R) := Nat.pow_le_pow_right hn (hc.2 hs)
      _ ≤ q^R*n^((2*t-1)*R) := by
        have hp : 1 ≤ q^R := one_le_pow₀ hq
        simpa only [one_mul] using Nat.mul_le_mul_right (n^((2*t-1)*R)) hp
  · calc
      _ ≤ n^((2*t-1)*R+1) := Nat.pow_le_pow_right hn hc.1
      _ = n*n^((2*t-1)*R) := by rw [pow_succ,Nat.mul_comm]
      _ ≤ q^R*n^((2*t-1)*R) := Nat.mul_le_mul_right _ (hbonus (by omega))

theorem finite_and_card (q n k L t b A R : ℕ) (v : Spectrum α L)
    (ht : 1 ≤ t) (hR : 1 ≤ R) (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hbonus : L < R → n ≤ q^R)
    (hcount : ∀ c, c ≤ 2*t*R → generatingCount k t b v R c ≤
      ((n^c*q^(6*b*t*R)*(L*R)^(A*R) : ℕ) : ℕ∞)) :
    Finite {F // Candidate k t b v R F} ∧
      Nat.card {F // Candidate k t b v R F} ≤
        (2*t*R+1)*q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R) := by
  classical
  have hf (c : CIndex t L R) :
      (Family k t b v R c.val.val).Finite ∧
      (Family k t b v R c.val.val).ncard ≤ n^c.val.val*q^(6*b*t*R)*(L*R)^(A*R) :=
    Set.encard_le_coe_iff_finite_ncard_le.mp (hcount c.val.val (by have h := c.val.isLt;omega))
  letI : ∀ c : CIndex t L R, Finite (Family k t b v R c.val.val) := fun c => (hf c).1.to_subtype
  letI : Finite (Indexed k t b v R) := by unfold Indexed;infer_instance
  have hfin : Finite {F // Candidate k t b v R F} :=
    Finite.of_injective (partition k t b v R ht hR) (partition_injective k t b v R ht hR)
  refine ⟨hfin,?_⟩
  calc
    _ ≤ Nat.card (Indexed k t b v R) :=
      Nat.card_le_card_of_injective (partition k t b v R ht hR) (partition_injective k t b v R ht hR)
    _ = ∑ c : CIndex t L R, Nat.card (Family k t b v R c.val.val) := Nat.card_sigma
    _ ≤ ∑ _c : CIndex t L R, q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R) := by
      apply Finset.sum_le_sum
      intro c hc
      exact (hf c).2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (component_power q t L n R c.val.val hq hn hbonus c.property)))
    _ = Fintype.card (CIndex t L R)*(q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R)) := by simp
    _ ≤ (2*t*R+1)*(q^R*n^((2*t-1)*R)*q^(6*b*t*R)*(L*R)^(A*R)) :=
      Nat.mul_le_mul_right _ (index_card t L R)
    _ = _ := by ring

theorem bonus (q n t b k L R : ℕ) (hreg : Regime q n t b k L) (hR : L < R) :
    n ≤ q^R := by
  have hq : 1 < q := by have h := hreg.1;omega
  have hk := hreg.2.2.2.1
  have hL := hreg.2.2.2.2.1
  have he : uniqueLength q n=2*Nat.clog q n+2 := by
    change 2*⌈Real.logb (q:ℝ) (n:ℝ)⌉₊+2=_
    rw [Real.natCeil_logb_natCast]
  rw [he] at hk
  exact (Nat.le_pow_clog hq n).trans (Nat.pow_le_pow_right (by omega) (by omega))

end DeletionGeneralization.WitnessCount
namespace DeletionGeneralization.WitnessProbability
open DeletionHash.MixedEdit WitnessCount ExceptionalProbability
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {n k L t b r R : ℕ}

def Test (F : Finset (Spectrum α L)) (ξ : HashSample α L r) : Prop :=
  ∀ w ∈ F, hash ξ w=0

def Event (k t b : ℕ) {L : ℕ} (v : Spectrum α L) (R : ℕ) (ξ : HashSample α L r) : Prop :=
  ∃ F, Candidate k t b v R F ∧ Test F ξ

theorem ruleSet_card (G : Fin R → Spectrum α L)
    (hi : LinearIndependent (ZMod 2) (fun j => parity (G j))) : (ruleSet G).card=R := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  have hinj : Function.Injective G := fun i j h => hi.injective (congrArg parity h)
  unfold ruleSet
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem test_probability (v : Spectrum α L) (F : Finset (Spectrum α L))
    (hg : GeneratingSet k t b v F) :
    uniformProbability (Test (r:=r) F)=1/((2:ℝ)^r)^F.card := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  obtain ⟨G,hgen,hset⟩ := hg
  have he : Test (r:=r) F=(fun ξ => ∀ j, hash ξ (G j)=0) := by
    funext ξ
    apply propext
    constructor
    · intro h j
      apply h
      rw [←hset]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    · intro h w hw
      rw [←hset] at hw
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      exact h j
  rw [he]
  exact HashUniform.joint G hgen.2.1 (fun _ => 0)

theorem event_bound (v : Spectrum α L) (hfinite : Finite {F // Candidate k t b v R F}) :
    uniformProbability (Event (r:=r) k t b v R) ≤
      (Nat.card {F // Candidate k t b v R F} : ℝ)/((2:ℝ)^r)^R := by
  classical
  letI : Finite {F // Candidate k t b v R F} := hfinite
  letI : Fintype {F // Candidate k t b v R F} := Fintype.ofFinite _
  have hcover : ∀ ξ, Event (r:=r) k t b v R ξ →
      ∃ F ∈ (Finset.univ : Finset {F // Candidate k t b v R F}), Test F.val ξ := by
    rintro ξ ⟨F,hF,hT⟩
    exact ⟨⟨F,hF⟩,Finset.mem_univ _,hT⟩
  calc
    _ ≤ uniformProbability (fun ξ => ∃ F ∈ (Finset.univ : Finset {F // Candidate k t b v R F}),
        Test F.val ξ) := probability_mono hcover
    _ ≤ ∑ F : {F // Candidate k t b v R F}, uniformProbability (Test (r:=r) F.val) :=
      probability_union _ _
    _ = ∑ _F : {F // Candidate k t b v R F}, 1/((2:ℝ)^r)^R := by
      apply Finset.sum_congr rfl
      intro F hF
      rw [test_probability v F.val F.property.1,F.property.2.1]
    _ = _ := by simp [Nat.card_eq_fintype_card,div_eq_mul_inv]

theorem bad_cover (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (hr : 1 ≤ r) (x : Word α n) :
    ∀ ξ : HashSample α L r, BadComponent n k t b ξ x →
      ∃ R ∈ Finset.Icc 2 (witnessBound t b L), Event k t b (spectrum L (letters x)) R ξ := by
  classical
  letI : DecidableEq (Spectrum α L) := fun a b => Classical.propDecidable (a=b)
  intro ξ hbad
  obtain ⟨R,G,hgen,hsurv,hR,hmax,hcomp,hsmall⟩ :=
    BoundedWitness.bounded n t b k L r hreg hr ξ x hbad
  have hcard := ruleSet_card G hgen.2.1
  have hset : GeneratingSet k t b (spectrum L (letters x)) (ruleSet G) := by
    unfold GeneratingSet
    rw [hcard]
    exact ⟨G,hgen,rfl⟩
  refine ⟨R,Finset.mem_Icc.mpr ⟨hR,hmax⟩,ruleSet G,⟨hset,hcard,hcomp,hsmall⟩,?_⟩
  intro w hw
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
  exact (hsurv j).2

end DeletionGeneralization.WitnessProbability
namespace DeletionGeneralization.OddBound
open DeletionHash.MixedEdit WitnessCount WitnessProbability ExceptionalProbability
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

def scale (q n t b L lam : ℕ) : ℕ := q^(6*b*t+1)*n^(2*t-1)*L^lam

theorem candidate_scale (q n k L t b A lam R : ℕ) (v : Spectrum α L)
    (hreg : Regime q n t b k L) (hR : 2 ≤ R) (hmax : R ≤ witnessBound t b L)
    (hexp : ExponentBound t b A lam L)
    (hcount : ∀ c, c ≤ 2*t*R → generatingCount k t b v R c ≤
      ((n^c*q^(6*b*t*R)*(L*R)^(A*R) : ℕ) : ℕ∞)) :
    Finite {F // Candidate k t b v R F} ∧
      Nat.card {F // Candidate k t b v R F} ≤ (scale q n t b L lam)^R := by
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  obtain ⟨hf,hcard⟩ := finite_and_card q n k L t b A R v (by omega) (by omega)
    (by omega) (by omega) (bonus q n t b k L R ⟨hq,ht,hb,hk,hL,hbk,hLn⟩) hcount
  refine ⟨hf,hcard.trans ?_⟩
  calc
    _ = q^R*n^((2*t-1)*R)*q^(6*b*t*R)*((2*t*R+1)*(L*R)^(A*R)) := by ring
    _ ≤ q^R*n^((2*t-1)*R)*q^(6*b*t*R)*L^(lam*R) :=
      Nat.mul_le_mul_left _ (hexp R hR hmax)
    _ = _ := by
      simp only [scale,mul_pow,←pow_mul]
      rw [show (6*b*t+1)*R=6*b*t*R+R by ring]
      rw [pow_add]
      ring

theorem survival_term (C N Q R : ℕ) (hC : C ≤ N^R) (hQ : 4*N ≤ Q) (hQpos : 0 < Q) :
    (C:ℝ)/(Q:ℝ)^R ≤ (1/4:ℝ)^R := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hNQ : 4*(N:ℝ) ≤ Q := by exact_mod_cast hQ
  have hratio : (N:ℝ)/Q ≤ 1/4 := by
    rw [div_le_iff₀ hQr]
    linarith
  calc
    _ ≤ (N:ℝ)^R/(Q:ℝ)^R := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hC
    _ = ((N:ℝ)/Q)^R := (div_pow _ _ _).symm
    _ ≤ (1/4:ℝ)^R := by gcongr

theorem geometric_tail_identity (N : ℕ) :
    (∑ i ∈ Finset.range N, (1/4:ℝ)^(i+2))=(1-(1/4:ℝ)^N)/12 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [pow_succ]
    ring

theorem geometric_tail_le (M : ℕ) :
    (∑ R ∈ Finset.Icc 2 M, (1/4:ℝ)^R) ≤ 1/12 := by
  have hset : Finset.Icc 2 M=Finset.Ico 2 (M+1) := by ext i;simp
  rw [hset,Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.add_comm 2]
  rw [geometric_tail_identity]
  have hp : 0 ≤ (1/4:ℝ)^(M+1-2) := by positivity
  linarith

theorem probability_bound (q n k L t b A lam r : ℕ)
    (hqa : Fintype.card α=q) (hreg : Regime q n t b k L) (hr : 1 ≤ r)
    (hexp : ExponentBound t b A lam L)
    (hQ : 4*scale q n t b L lam ≤ 2^r) (x : Word α n)
    (hcount : ∀ R c, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c*q^(6*b*t*R)*(L*R)^(A*R) : ℕ) : ℕ∞)) :
    uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12 := by
  have hreg' : Regime (Fintype.card α) n t b k L := by simpa only [hqa] using hreg
  calc
    _ ≤ uniformProbability (fun ξ : HashSample α L r =>
        ∃ R ∈ Finset.Icc 2 (witnessBound t b L), Event k t b (spectrum L (letters x)) R ξ) :=
      probability_mono (bad_cover n t b k L r hreg' hr x)
    _ ≤ ∑ R ∈ Finset.Icc 2 (witnessBound t b L),
        uniformProbability (Event (r:=r) k t b (spectrum L (letters x)) R) :=
      probability_union _ _
    _ ≤ ∑ R ∈ Finset.Icc 2 (witnessBound t b L), (1/4:ℝ)^R := by
      apply Finset.sum_le_sum
      intro R hR
      obtain ⟨hRlo,hRhi⟩ := Finset.mem_Icc.mp hR
      obtain ⟨hf,hcard⟩ := candidate_scale q n k L t b A lam R (spectrum L (letters x))
        hreg hRlo hRhi hexp (fun c hc => hcount R c (by omega) hc)
      have hp := event_bound (r:=r) (spectrum L (letters x)) hf
      have ht := survival_term _ (scale q n t b L lam) (2^r) R hcard hQ (by positivity)
      exact hp.trans (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht)
    _ ≤ _ := geometric_tail_le _

end DeletionGeneralization.OddBound
namespace DeletionGeneralization.OddTheorem
open DeletionHash.MixedEdit

universe u

/-- Proposition 6.1 with the alphabet-uniform choices and eventual-L regime of §6.1.
The counting estimate is a conclusion here, not an assumed oracle for a selected exponent. -/
theorem rare (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ (∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞)) ∧
    ∃ lam L₀ : ℕ, 2 ≤ lam ∧ 1 ≤ L₀ ∧
      (∀ L : ℕ, L₀ ≤ L → ExponentBound t b a lam L) ∧
      ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
        ∀ n k L r : ℕ, Regime q n t b k L → L₀ ≤ L → 1 ≤ r →
        4*q^(6*b*t+1)*n^(2*t-1)*L^lam ≤ 2^r →
        ∀ x : Word α n, IsUnique k (letters x) →
        uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12 := by
  obtain ⟨a,ha,hcount⟩ := DeletionGeneralization.Counting.count.{u} t b ht hb
  obtain ⟨lam,L₀,hlam,hL₀,hexp⟩ := DeletionGeneralization.ExponentAbsorption.eventual t b a
  refine ⟨a,ha,hcount,lam,L₀,hlam,hL₀,hexp,?_⟩
  intro q α instF instD hqa n k L r hreg hready hr hQ x hx
  apply DeletionGeneralization.OddBound.probability_bound q n k L t b a lam r hqa hreg hr
    (hexp L hready) _ x (hcount q α hqa n k L hreg x hx)
  simpa [DeletionGeneralization.OddBound.scale,Nat.mul_assoc] using hQ

end DeletionGeneralization.OddTheorem

namespace DeletionGeneralization.DiscardBound
open DeletionHash.MixedEdit
universe u

theorem probability_or {Ω : Type u} [Fintype Ω] (P Q : Ω → Prop) :
    uniformProbability (fun ω => P ω ∨ Q ω) ≤ uniformProbability P + uniformProbability Q := by
  classical
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.filter_or, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_union_le (Finset.univ.filter P) (Finset.univ.filter Q)

theorem exceptional_quarter {α : Type u} [Fintype α] [DecidableEq α]
    (q n k L t b lam r : ℕ) (hqa : Fintype.card α=q)
    (hreg : Regime q n t b k L) (hlam : 2≤lam)
    (hconst : RecordArithmetic.countConstant t b ≤ L)
    (hQ : 4*q^(6*b*t+1)*n^(2*t-1)*L^lam≤2^r)
    (x : Word α n) (hx : IsUnique k (letters x)) :
    uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤ (1:ℝ)/4 := by
  have hreg' : Regime (Fintype.card α) n t b k L := by simpa only [hqa] using hreg
  have he := ExceptionalProbability.exceptional_bound n t b k L r hreg' x hx
  rw [hqa] at he
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  have hL1 : 1≤L := by omega
  have hpow : q^(2*b*t)≤q^(6*b*t+1) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hwin : RecordArithmetic.countConstant t b * L ≤ L^lam := by
    calc
      _ ≤ L*L := Nat.mul_le_mul_right L hconst
      _ = L^2 := by ring
      _ ≤ L^lam := Nat.pow_le_pow_right hL1 hlam
  have hnum : RecordArithmetic.countConstant t b * q^(2*b*t)*L*n^(2*t-1) ≤
      q^(6*b*t+1)*n^(2*t-1)*L^lam := by
    calc
      _ = (RecordArithmetic.countConstant t b*L)*q^(2*b*t)*n^(2*t-1) := by ring
      _ ≤ L^lam*q^(6*b*t+1)*n^(2*t-1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hwin hpow)
      _ = _ := by ring
  have hnumR : (RecordArithmetic.countConstant t b:ℝ)*(q:ℝ)^(2*b*t)*L*(n:ℝ)^(2*t-1) ≤
      (q:ℝ)^(6*b*t+1)*(n:ℝ)^(2*t-1)*(L:ℝ)^lam := by exact_mod_cast hnum
  have hQR : 4*(q:ℝ)^(6*b*t+1)*(n:ℝ)^(2*t-1)*(L:ℝ)^lam≤(2:ℝ)^r := by exact_mod_cast hQ
  apply he.trans
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^r)).mpr
  nlinarith

end DeletionGeneralization.DiscardBound
namespace DeletionGeneralization.CodeExistence
open DeletionHash.MixedEdit
universe u

theorem large_code {α : Type u} [Fintype α] [DecidableEq α]
    (q n k L t b lam r : ℕ) (hqa : Fintype.card α=q)
    (hreg : Regime q n t b k L) (hlam : 2≤lam)
    (hconst : RecordArithmetic.countConstant t b ≤ L)
    (hQ : 4*q^(6*b*t+1)*n^(2*t-1)*L^lam≤2^r)
    (hbad : ∀ x : Word α n, IsUnique k (letters x) →
      uniformProbability (fun ξ : HashSample α L r => BadComponent n k t b ξ x) ≤ (1:ℝ)/12) :
    ∃ code : Finset (Word α n), Corrects b t code ∧ q^n ≤ 8*2^r*code.card := by
  classical
  let s := uniqueFamily α n k
  let E : Word α n → HashSample α L r → Prop := fun x ξ =>
    Exceptional n k t b ξ x ∨ BadComponent n k t b ξ x
  obtain ⟨ξ,hhalf⟩ := FiniteAverage.half_retained s E (by
    intro x hx
    have hu : IsUnique k (letters x) := by simpa only [s,uniqueFamily,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    have he := DiscardBound.exceptional_quarter q n k L t b lam r hqa hreg hlam hconst hQ x hu
    have hb := hbad x hu
    have h := DiscardBound.probability_or
      (fun ξ : HashSample α L r => Exceptional n k t b ξ x)
      (fun ξ => BadComponent n k t b ξ x)
    exact h.trans (by linarith))
  have hret : s.filter (fun x => ¬ E x ξ) = CodeSelection.retained (n:=n) (k:=k) (t:=t) (b:=b) ξ := by
    ext x
    simp [s,uniqueFamily,E,CodeSelection.retained]
  have hhalf' : s.card ≤ 2*(CodeSelection.retained (n:=n) (k:=k) (t:=t) (b:=b) ξ).card := by
    convert hhalf using 1
    congr 2
    ext x
    simp [CodeSelection.retained,s,uniqueFamily,E]

  obtain ⟨code,hcorrect,hselect⟩ := CodeSelection.exists_code (n:=n) (k:=k) (t:=t) (b:=b) ξ
  obtain ⟨hq,ht,hb,hk,hL,hbk,hLn⟩ := hreg
  have hn : 1≤n := by omega
  have hmass := UniqueMass.mass (α:=α) n hn (by omega)
  dsimp only at hmass
  rw [hqa, ← hk] at hmass
  have hreal : (q:ℝ)^n ≤ 2*(s.card:ℝ) := by
    dsimp only [s]
    linarith [hmass.1,hmass.2.1,hmass.2.2]
  have hnat : q^n ≤ 2*s.card := by exact_mod_cast hreal
  refine ⟨code,hcorrect,?_⟩
  calc
    q^n ≤ 2*s.card := hnat
    _ ≤ 2*(2*(2*2^r*code.card)) := Nat.mul_le_mul_left 2
      (hhalf'.trans (Nat.mul_le_mul_left 2 hselect))
    _ = _ := by ring

end DeletionGeneralization.CodeExistence
namespace DeletionGeneralization.CodeParameters
open DeletionHash.MixedEdit

noncomputable def window (q b n : ℕ) : ℕ := 3*(uniqueLength q n+b+1)

theorem length_eq_clog (q n : ℕ) : uniqueLength q n = 2*Nat.clog q n+2 := by
  change 2*⌈Real.logb (q:ℝ) (n:ℝ)⌉₊+2 = _
  rw [Real.natCeil_logb_natCast]

theorem window_eq (q b n : ℕ) : window q b n = 6*Nat.clog q n+3*b+9 := by
  unfold window
  rw [length_eq_clog]
  omega

private theorem affine_le_pow (m : ℕ) : 10*(m+10) ≤ 2^(m+10) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m+1+10=(m+10)+1 by omega, pow_succ]
    omega

def threshold (q b M : ℕ) : ℕ := q^(max (3*b+11) (max b M)) + q^q + 1

theorem ready (q t b M n : ℕ) (hq : 2≤q) (ht : 2≤t) (hb : 1≤b)
    (hn : threshold q b M ≤ n) :
    q^q ≤ n ∧ Regime q n t b (uniqueLength q n) (window q b n) ∧
      M ≤ window q b n := by
  have hc : max (3*b+11) (max b M) < Nat.clog q n := by
    apply (Nat.lt_clog_iff_pow_lt (by omega : 1<q)).mpr
    unfold threshold at hn
    omega
  have hnpow : q^(Nat.clog q n-1) < n :=
    Nat.pow_lt_of_lt_clog (by omega : Nat.clog q n-1 < Nat.clog q n)
  have hp := affine_le_pow (Nat.clog q n-11)
  rw [show Nat.clog q n-11+10=Nat.clog q n-1 by omega] at hp
  have hbase : 2^(Nat.clog q n-1) ≤ q^(Nat.clog q n-1) := Nat.pow_le_pow_left hq _
  have hfit : window q b n ≤ n := by rw [window_eq]; omega
  refine ⟨by unfold threshold at hn; omega, ?_, ?_⟩
  · refine ⟨hq,ht,hb,rfl,rfl,?_,hfit⟩
    rw [length_eq_clog]
    omega
  · rw [window_eq]
    omega

theorem log_large (q n : ℕ) (hq : 2≤q) (hn : q^q≤n) :
    (q:ℝ) ≤ Real.logb (q:ℝ) (n:ℝ) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have h := Real.logb_le_logb_of_le hq'
    (pow_pos (by linarith : (0:ℝ)<q) q) (show (q:ℝ)^q≤n by exact_mod_cast hn)
  simpa only [Real.logb_pow, Real.logb_self_eq_one hq', mul_one] using h

theorem loglog_one (q n : ℕ) (hq : 2≤q) (hn : q^q≤n) :
    1 ≤ Real.logb (q:ℝ) (Real.logb (q:ℝ) (n:ℝ)) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have h := Real.logb_le_logb_of_le hq' (by linarith : (0:ℝ)<q) (log_large q n hq hn)
  simpa only [Real.logb_self_eq_one hq'] using h

theorem log_window (q b n : ℕ) (hq : 2≤q) (hn : q^q≤n) :
    Real.logb (q:ℝ) (window q b n:ℝ) ≤
      (3*b+22:ℕ) * Real.logb (q:ℝ) (Real.logb (q:ℝ) (n:ℝ)) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have hlog : 1 ≤ Real.logb (q:ℝ) (n:ℝ) := by
    have := log_large q n hq hn
    have : (2:ℝ)≤q := by exact_mod_cast hq
    linarith
  have hceil : (Nat.clog q n:ℝ) < Real.logb (q:ℝ) (n:ℝ)+1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (by linarith)
  have hL : (window q b n:ℝ) ≤ (3*b+21:ℕ)*Real.logb (q:ℝ) (n:ℝ) := by
    have he : (window q b n:ℝ)=6*(Nat.clog q n:ℝ)+3*b+9 := by exact_mod_cast window_eq q b n
    push_cast
    have hb : (0:ℝ)≤b := Nat.cast_nonneg _
    nlinarith
  have hd : 3*b+21 ≤ q^(3*b+21) :=
    (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hq _)
  have hL' : (window q b n:ℝ) ≤ (q:ℝ)^(3*b+21)*Real.logb (q:ℝ) (n:ℝ) :=
    hL.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by linarith))
  have hpos : (0:ℝ)<window q b n := by
    have he:=window_eq q b n
    exact_mod_cast (show 0<window q b n by omega)
  have h := Real.logb_le_logb_of_le hq' hpos hL'
  rw [Real.logb_mul (pow_ne_zero _ (by linarith : (q:ℝ)≠0)) (by linarith),
    Real.logb_pow, Real.logb_self_eq_one hq', mul_one] at h
  have hll := loglog_one q n hq hn
  have hb : (0:ℝ)≤b := Nat.cast_nonneg _
  push_cast at h ⊢
  nlinarith

end DeletionGeneralization.CodeParameters
namespace DeletionGeneralization.CodeRedundancy
open DeletionHash.MixedEdit
universe u

def coefficient (t b lam : ℕ) : ℕ := 6*b*t+8+lam*(3*b+22)

theorem bound {α : Type u} {n : ℕ} (q t b lam : ℕ)
    (code : Finset (Word α n)) (hq : 2≤q) (ht : 2≤t) (hn : q^q≤n)
    (hcard : q^n ≤ 64*q^(6*b*t+1)*n^(2*t-1)*(CodeParameters.window q b n)^lam*code.card) :
    code.Nonempty ∧ redundancy q code ≤
      ((2*t:ℝ)-1)*logBase q (n:ℝ) +
        (coefficient t b lam:ℝ)*logBase q (logBase q (n:ℝ)) := by
  have hq' : (1:ℝ)<q := by exact_mod_cast (show 1<q by omega)
  have hqp : (0:ℝ)<q := by linarith
  have hcp : 0<code.card := by
    have hp : 0<q^n := pow_pos (by omega) _
    by_contra h
    have hz : code.card=0 := by omega
    rw [hz,mul_zero] at hcard
    omega
  have hc : (0:ℝ)<code.card := by exact_mod_cast hcp
  have hnp : (0:ℝ)<n := by
    have hp : 0<q^q := pow_pos (by omega) _
    exact_mod_cast (show 0<n by omega)
  have hLp : (0:ℝ)<CodeParameters.window q b n := by
    have h:=CodeParameters.window_eq q b n
    exact_mod_cast (show 0<CodeParameters.window q b n by omega)
  have hreal : (q:ℝ)^n ≤ 64*(q:ℝ)^(6*b*t+1)*(n:ℝ)^(2*t-1)*
      (CodeParameters.window q b n:ℝ)^lam*(code.card:ℝ) := by exact_mod_cast hcard
  have hlog := Real.logb_le_logb_of_le hq' (pow_pos hqp n) hreal
  rw [Real.logb_mul (by positivity) (ne_of_gt hc),
    Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hLp)),
    Real.logb_mul (by positivity) (pow_ne_zero _ (ne_of_gt hnp)),
    Real.logb_mul (by norm_num : (64:ℝ)≠0) (pow_ne_zero _ (ne_of_gt hqp))] at hlog
  simp only [Real.logb_pow, Real.logb_self_eq_one hq', mul_one] at hlog
  have h64 : Real.logb (q:ℝ) 64 ≤ 6 := by
    have hbase : (64:ℝ) ≤ (q:ℝ)^(6:ℕ) := by
      have h : (2:ℕ)^6≤q^6 := Nat.pow_le_pow_left hq 6
      norm_num at h
      exact_mod_cast h
    have h := Real.logb_le_logb_of_le hq' (by norm_num : (0:ℝ)<64) hbase
    simpa only [Real.logb_pow,Real.logb_self_eq_one hq',mul_one,Nat.cast_ofNat] using h
  have hw := mul_le_mul_of_nonneg_left (CodeParameters.log_window q b n hq hn)
    (Nat.cast_nonneg lam : (0:ℝ)≤lam)
  have hll := CodeParameters.loglog_one q n hq hn
  have he : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*t)]
    push_cast
    rfl
  rw [he] at hlog
  refine ⟨Finset.card_pos.mp hcp,?_⟩
  change (n:ℝ)-Real.logb (q:ℝ) (code.card:ℝ) ≤
    (2*(t:ℝ)-1)*Real.logb (q:ℝ) (n:ℝ)+
      (coefficient t b lam:ℝ)*Real.logb (q:ℝ) (Real.logb (q:ℝ) (n:ℝ))
  have hd : (0:ℝ)≤6*b*t+8 := by positivity
  have hconst := mul_le_mul_of_nonneg_left hll hd
  unfold coefficient
  push_cast at hlog hw ⊢
  nlinarith

end DeletionGeneralization.CodeRedundancy
namespace DeletionGeneralization.SubstringTheorem
open DeletionHash.MixedEdit

universe u

/-- Theorems 1.2 and 6.2: C is chosen before q, and N before the alphabet type. -/
theorem codes (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects b t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by
  classical
  obtain ⟨a,ha,hcount,lam,L₀,hlam,hL₀,hexp,hprob⟩ := OddTheorem.rare.{u} t b ht hb
  refine ⟨(CodeRedundancy.coefficient t b lam:ℝ), ?_, ?_⟩
  · unfold CodeRedundancy.coefficient
    positivity
  intro q hq
  let M := max L₀ (RecordArithmetic.countConstant t b)
  let N := CodeParameters.threshold q b M
  refine ⟨N, ?_, ?_⟩
  · dsimp [N,CodeParameters.threshold]
    omega
  intro α instF instD hqa n hn
  let k := uniqueLength q n
  let L := CodeParameters.window q b n
  obtain ⟨hnq,hreg,hM⟩ := CodeParameters.ready q t b M n hq ht hb hn
  have hreg' : Regime q n t b k L := hreg
  have hLpos : 1≤L := by
    have he:=CodeParameters.window_eq q b n
    dsimp only [L]
    omega
  have hnpos : 1≤n := by
    have hp : 0<q^q := pow_pos (by omega) _
    omega
  let A := 4*q^(6*b*t+1)*n^(2*t-1)*L^lam
  have hA : 1<A := by
    have hqp : 0<q^(6*b*t+1) := pow_pos (by omega) _
    have hnp : 0<n^(2*t-1) := pow_pos (by omega) _
    have hLp : 0<L^lam := pow_pos (by omega) _
    have hp : 1≤q^(6*b*t+1)*n^(2*t-1)*L^lam :=
      Nat.succ_le_of_lt (mul_pos (mul_pos hqp hnp) hLp)
    calc
      1 < 4 := by decide
      _ = 4*1 := by omega
      _ ≤ 4*(q^(6*b*t+1)*n^(2*t-1)*L^lam) := Nat.mul_le_mul_left 4 hp
      _ = A := by dsimp only [A]; ring
  let r := Nat.clog 2 A
  have hr : 1≤r := Nat.clog_pos (by decide) hA
  have hQ : A≤2^r := Nat.le_pow_clog (by decide) A
  have hround : 2^r≤2*A := by
    have hp : 2^(r-1)<A := Nat.pow_lt_of_lt_clog (by omega : r-1<r)
    calc
      2^r=2*2^(r-1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hr]
        rw [pow_succ,Nat.mul_comm]
      _ ≤ 2*A := Nat.mul_le_mul_left 2 hp.le
  obtain ⟨code,hcorrect,hcard⟩ := CodeExistence.large_code q n k L t b lam r hqa hreg'
    hlam (by dsimp only [M] at hM; omega) hQ
    (hprob q α hqa n k L r hreg' (by dsimp only [M] at hM; omega) hr hQ)
  have hcard' : q^n≤64*q^(6*b*t+1)*n^(2*t-1)*L^lam*code.card := by
    calc
      q^n ≤ 8*2^r*code.card := hcard
      _ ≤ 8*(2*A)*code.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hround)
      _ = _ := by dsimp only [A]; ring
  obtain ⟨hne,hred⟩ := CodeRedundancy.bound q t b lam code hq ht hnq hcard'
  exact ⟨code,hne,hcorrect,hred⟩

end DeletionGeneralization.SubstringTheorem

open DeletionHash.MixedEdit

universe u

/-- Theorem 1.1: C is chosen before q, and N before the alphabet type. -/
theorem solution (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects 1 t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by exact DeletionGeneralization.SubstringTheorem.codes t 1 ht (by decide)



#print axioms solution
