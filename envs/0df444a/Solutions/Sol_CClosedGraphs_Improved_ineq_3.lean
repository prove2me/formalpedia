-- Prove2me | solution 1 for CClosedGraphs.Improved.ineq_3
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T00:27:18.907355+00:00
-- url     : https://prove2.me/submissions/2311b810-9d7a-4e52-826a-e9b64f08665a

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace Prove2SwarmSubmission
open CClosedGraphs.Improved

set_option autoImplicit false

namespace CClosedGraphs.Improved

open Classical
open Finset

variable {V : Type*} [Fintype V]

/-! ## Finite helpers for `A = W ∩ N(v)` and `W ∩ N(v) ∩ N(u)`

These definitions are deliberately computational descriptions of the target's
`Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)` and of the set
`W ∩ G.commonNeighbors v u`.  They are useful when counting subsets. -/

/-- The finite set version of `A = W ∩ N_G(v)`. -/
noncomputable def nbrsInFinset (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)

/-- The finite set version of `W ∩ N_G(v) ∩ N_G(u)`. -/
noncomputable def commonNbrsInFinset (G : SimpleGraph V) (W : Set V) (v u : V) : Finset V :=
  Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x ∧ G.Adj u x)

@[simp]
theorem mem_nbrsInFinset {G : SimpleGraph V} {W : Set V} {v x : V} :
    x ∈ nbrsInFinset G W v ↔ x ∈ W ∧ G.Adj v x := by
  simp [nbrsInFinset]

@[simp]
theorem mem_commonNbrsInFinset {G : SimpleGraph V} {W : Set V} {v u x : V} :
    x ∈ commonNbrsInFinset G W v u ↔
      x ∈ W ∧ G.Adj v x ∧ G.Adj u x := by
  simp [commonNbrsInFinset]

/-! ## The local c-closure bound -/

omit [Fintype V] in
/-- If `u` is at distance two from `v` inside `W`, then the two vertices have
at most `c - 1` common neighbours inside `W`.

The proof uses only the fact that `u ∈ W`, `u ≠ v`, and `¬ G.Adj v u` from
`u ∈ dist2In G W v`.  The two-edge witness in the definition of `dist2In` is
not needed for this bound. -/
theorem ncard_commonNeighbors_le_pred_of_dist2In
    {c : ℕ} (_hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    (W ∩ G.commonNeighbors v u).ncard ≤ c - 1 := by
  have huW : u ∈ W := hu.1
  have huv : u ≠ v := hu.2.1
  have hnonadj : ¬ G.Adj v u := hu.2.2.1
  have hnot_ge : ¬ c ≤ (W ∩ G.commonNeighbors v u).ncard := by
    intro hge
    exact hnonadj (hW v hv u huW huv.symm hge)
  exact Nat.le_sub_one_of_lt (Nat.lt_of_not_ge hnot_ge)

/-- Finite-cardinality form of the local closure bound, stated for the
explicit finite set `W ∩ N(v) ∩ N(u)`. -/
theorem card_commonNbrsInFinset_le_pred
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    (commonNbrsInFinset G W v u).card ≤ c - 1 := by
  have hset : (commonNbrsInFinset G W v u : Set V) =
      W ∩ G.commonNeighbors v u := by
    ext x
    simp [commonNbrsInFinset, SimpleGraph.commonNeighbors, and_assoc]; tauto
  rw [← Set.ncard_coe_finset]
  rw [hset]
  exact ncard_commonNeighbors_le_pred_of_dist2In hc hW hv hu

/-! ## Characterizing subsets whose common neighbourhood contains `u` -/

/-- For a subset `S ⊆ A = W ∩ N_G(v)`, the vertex `u` is in `N(S)` exactly
when `S` is contained in the finite set `W ∩ N_G(v) ∩ N_G(u)`.

This is the fiber characterization needed for double counting.  The proof of
the forward direction uses adjacency symmetry only because `commonNbrs G S`
records the edge as `(s,u)`, while `G.commonNeighbors v u` records it as
`(u,s)`. -/
theorem mem_commonNbrs_iff_subset_commonNbrsInFinset
    {G : SimpleGraph V} {W : Set V} {v u : V} {S : Finset V}
    (hS : S ⊆ nbrsInFinset G W v) :
    u ∈ commonNbrs G S ↔ S ⊆ commonNbrsInFinset G W v u := by
  constructor
  · intro hu x hx
    have hxA := mem_nbrsInFinset.mp (hS hx)
    exact mem_commonNbrsInFinset.mpr
      ⟨hxA.1, hxA.2, G.adj_symm (hu x hx)⟩
  · intro hsub x hx
    have hx' := mem_commonNbrsInFinset.mp (hsub hx)
    exact G.adj_symm hx'.2.2

/-- The same subset characterization using exactly the set intersection from
the target statement. -/
theorem mem_commonNbrs_iff_subset_commonNeighbors
    {G : SimpleGraph V} {W : Set V} {v u : V} {S : Finset V}
    (hS : S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset) :
    u ∈ commonNbrs G S ↔
      (S : Set V) ⊆ W ∩ G.commonNeighbors v u := by
  have hSsub : S ⊆ nbrsInFinset G W v := by
    simpa [nbrsInFinset] using (Finset.mem_powerset.mp hS)
  rw [mem_commonNbrs_iff_subset_commonNbrsInFinset hSsub]
  constructor
  · intro hsub x hx
    have hx' := mem_commonNbrsInFinset.mp (hsub (by simpa using hx))
    refine ⟨hx'.1, ?_⟩
    simpa [SimpleGraph.commonNeighbors] using hx'.2
  · intro hsub x hx
    have hx' := hsub (by simpa using hx)
    rw [mem_commonNbrsInFinset]
    exact ⟨hx'.1, by simpa [SimpleGraph.commonNeighbors] using hx'.2⟩

/-! ## Per-vertex fiber bound -/

/-- The number of nonempty subsets `S ⊆ A = W ∩ N_G(v)` with `u ∈ N(S)` is at
most `2 ^ (c - 1)`, for every `u ∈ dist2In G W v`.

All such subsets are subsets of `W ∩ N_G(v) ∩ N_G(u)`, a finite set of size
at most `c - 1`; the nonemptiness condition can therefore be discarded in the
upper bound. -/
theorem fiber_card_le_pow
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    ((nbrsInFinset G W v).powerset.filter
        (fun S => S.Nonempty ∧ u ∈ commonNbrs G S)).card
      ≤ 2 ^ (c - 1) := by
  calc
    ((nbrsInFinset G W v).powerset.filter
        (fun S => S.Nonempty ∧ u ∈ commonNbrs G S)).card
        ≤ (commonNbrsInFinset G W v u).powerset.card := by
          apply Finset.card_le_card
          intro S hS
          rw [Finset.mem_filter] at hS
          exact Finset.mem_powerset.mpr
            ((mem_commonNbrs_iff_subset_commonNbrsInFinset
              (Finset.mem_powerset.mp hS.1)).mp hS.2.2)
    _ = 2 ^ (commonNbrsInFinset G W v u).card := by
          rw [Finset.card_powerset]
    _ ≤ 2 ^ (c - 1) := by
          exact Nat.pow_le_pow_right (by norm_num)
            (card_commonNbrsInFinset_le_pred hc hW hv hu)

/-- The per-vertex fiber bound with the exact filtered-power-set expression
appearing in the target theorem. -/
theorem card_filter_commonNbrs_le_pow
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    (((Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty)).filter
        (fun S => u ∈ commonNbrs G S)).card
      ≤ 2 ^ (c - 1) := by
  simpa [nbrsInFinset, Finset.filter_filter, and_assoc] using
    (fiber_card_le_pow hc hW hv hu)

end CClosedGraphs.Improved


set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CClosedGraphs.Improved

open Classical
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite set underlying `dist2In G W v`, used for incidence bounds. -/
noncomputable def dist2InFinset (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ dist2In G W v)

@[simp]
theorem mem_dist2InFinset {G : SimpleGraph V} {W : Set V} {v u : V} :
    u ∈ dist2InFinset G W v ↔ u ∈ dist2In G W v := by
  simp [dist2InFinset]

/-- The finite set of neighbours of `v` inside `W`. -/
noncomputable def nbrsInFinset' (G : SimpleGraph V) (W : Set V) (v : V) : Finset V :=
  Finset.univ.filter (fun y => y ∈ W ∧ G.Adj v y)

@[simp]
theorem mem_nbrsInFinset' {G : SimpleGraph V} {W : Set V} {v y : V} :
    y ∈ nbrsInFinset' G W v ↔ y ∈ W ∧ G.Adj v y := by
  simp [nbrsInFinset']

/-- Fiber of candidates at a first-step vertex `y`: vertices of `W` adjacent to `y`. -/
noncomputable def neighborFiberInFinset (G : SimpleGraph V) (W : Set V) (y : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ W ∧ G.Adj y u)

@[simp]
theorem mem_neighborFiberInFinset {G : SimpleGraph V} {W : Set V} {y u : V} :
    u ∈ neighborFiberInFinset G W y ↔ u ∈ W ∧ G.Adj y u := by
  simp [neighborFiberInFinset]

/-- The target's second-distance set in `W` is contained in the union, over
first-step vertices `y ∈ A = W ∩ N(v)`, of the within-`W` neighbourhood of `y`. -/
theorem dist2InFinset_subset_biUnion_neighborFiber
    {G : SimpleGraph V} {W : Set V} {v : V} :
    dist2InFinset G W v ⊆
      (nbrsInFinset' G W v).biUnion (neighborFiberInFinset G W) := by
  intro u hu
  rw [mem_dist2InFinset] at hu
  obtain ⟨huW, huv, hnonadj, y, hyW, hvy, hyu⟩ := hu
  refine Finset.mem_biUnion.mpr ⟨y, ?_, ?_⟩
  · rw [mem_nbrsInFinset']
    exact ⟨hyW, hvy⟩
  · rw [mem_neighborFiberInFinset]
    exact ⟨huW, hyu⟩

/-- Every fiber at `y ∈ A` is exactly `W ∩ N(y)`, so its cardinality is
bounded by `Δ` under the target's within-`W` degree hypothesis. -/
theorem neighborFiberInFinset_card_le
    {G : SimpleGraph V} {W : Set V} {y : V} (hyW : y ∈ W) {Δ : ℕ}
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (neighborFiberInFinset G W y).card ≤ Δ := by
  rw [← Set.ncard_coe_finset]
  convert hΔ y hyW using 2
  ext u
  simp [neighborFiberInFinset, SimpleGraph.mem_neighborSet]

/-- `|A| ≤ Δ`, where `A = W ∩ N(v)`. -/
theorem nbrsInFinset'_card_le
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W) {Δ : ℕ}
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (nbrsInFinset' G W v).card ≤ Δ := by
  rw [← Set.ncard_coe_finset]
  convert hΔ v hv using 2
  ext u
  simp [nbrsInFinset', SimpleGraph.mem_neighborSet]


/-- Incidence count for a single subset: cardinality of a common-neighbour
intersection with the internal distance-two set is the sum of its indicator
over the finite set `B`. -/
theorem ncard_inter_dist2In_eq_sum_indicator (G : SimpleGraph V) (W : Set V) (v : V)
    (C : Set V) :
    (C ∩ dist2In G W v).ncard =
      ∑ u ∈ dist2InFinset G W v, if u ∈ C then 1 else 0 := by
  let B : Finset V := dist2InFinset G W v
  have hset : C ∩ dist2In G W v = (B.filter (fun u => u ∈ C) : Set V) := by
    ext u
    simp [B, and_comm]
  rw [hset, Set.ncard_coe_finset]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- First conclusion of the target, with its exact finite sum. -/
theorem sum_commonNbrs_dist2In_le
    {c : ℕ} (hc : 0 < c) {G : SimpleGraph V} {W : Set V}
    (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W) :
    (∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) ≤
      (dist2In G W v).ncard * 2 ^ (c - 1) := by
  let A : Finset V := Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)
  let B : Finset V := dist2InFinset G W v
  let s : Finset (Finset V) := A.powerset.filter (fun S => S.Nonempty)
  have hBcard : (dist2In G W v).ncard = B.card := by
    rw [← Set.ncard_coe_finset B]
    congr 1
    ext u
    simp [B]
  have hstep : (∑ S ∈ s, (commonNbrs G S ∩ dist2In G W v).ncard) =
      ∑ u ∈ B, ∑ S ∈ s, if u ∈ commonNbrs G S then 1 else 0 := by
    calc
      (∑ S ∈ s, (commonNbrs G S ∩ dist2In G W v).ncard)
          = ∑ S ∈ s, ∑ u ∈ B, if u ∈ commonNbrs G S then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              simpa [B] using
                (ncard_inter_dist2In_eq_sum_indicator G W v (commonNbrs G S))
      _ = ∑ u ∈ B, ∑ S ∈ s, if u ∈ commonNbrs G S then 1 else 0 := by
              rw [Finset.sum_comm]
  rw [show (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)) = A by rfl]
  rw [show (∑ S ∈ A.powerset.filter (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) =
      ∑ S ∈ s, (commonNbrs G S ∩ dist2In G W v).ncard by rfl]
  rw [hstep]
  calc
    (∑ u ∈ B, ∑ S ∈ s, if u ∈ commonNbrs G S then 1 else 0)
        = ∑ u ∈ B, ((s.filter (fun S => u ∈ commonNbrs G S)).card : ℕ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.sum_boole]
            rfl
    _ ≤ ∑ u ∈ B, 2 ^ (c - 1) := by
            apply Finset.sum_le_sum
            intro u hu
            have huB : u ∈ dist2In G W v := by simpa [B] using hu
            simpa [A, s] using card_filter_commonNbrs_le_pow hc hW hv huB
    _ = B.card * 2 ^ (c - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rfl
    _ = (dist2In G W v).ncard * 2 ^ (c - 1) := by rw [hBcard]

/-- Distance-two degree bound: the internal second neighbourhood of `v` has
at most `Δ ^ 2` vertices. This uses exactly the target's within-`W` degree
bound and no c-closure or positivity hypothesis. -/
theorem dist2In_ncard_le_sq
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W) (Δ : ℕ)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (dist2In G W v).ncard ≤ Δ ^ 2 := by
  let A : Finset V := nbrsInFinset' G W v
  let B : Finset V := dist2InFinset G W v
  have hBcard : (dist2In G W v).ncard = B.card := by
    rw [← Set.ncard_coe_finset B]
    congr 1
    ext u
    simp [B]
  rw [hBcard]
  have hcover : B ⊆ A.biUnion (neighborFiberInFinset G W) := by
    simpa [A, B] using dist2InFinset_subset_biUnion_neighborFiber (G := G) (W := W) (v := v)
  have hfiber : ∀ y ∈ A, (neighborFiberInFinset G W y).card ≤ Δ := by
    intro y hy
    exact neighborFiberInFinset_card_le (mem_nbrsInFinset'.mp hy).1 hΔ
  calc
    B.card ≤ (A.biUnion (neighborFiberInFinset G W)).card := Finset.card_le_card hcover
    _ ≤ A.card * Δ := Finset.card_biUnion_le_card_mul A (neighborFiberInFinset G W) Δ hfiber
    _ ≤ Δ * Δ := Nat.mul_le_mul_right Δ (nbrsInFinset'_card_le hv hΔ)
    _ = Δ ^ 2 := by rw [pow_two]

/-- The same internal second neighbourhood has at most `|W|` vertices. -/
theorem dist2In_ncard_le_ncard
    {G : SimpleGraph V} {W : Set V} {v : V} :
    (dist2In G W v).ncard ≤ W.ncard := by
  exact Set.ncard_le_ncard (fun u hu => hu.1)

/-- The second conclusion of the target, including the `min`. -/
theorem dist2In_ncard_le_min
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W) (Δ : ℕ)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (dist2In G W v).ncard ≤ min (Δ ^ 2) W.ncard := by
  exact le_min (dist2In_ncard_le_sq hv Δ hΔ) dist2In_ncard_le_ncard


/-- Boundary check at `c = 1`: every per-vertex incidence fiber has the full
empty powerset as its only possible source, hence cardinality at most `1`. -/
theorem fiber_card_le_one_of_c_eq_one
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn 1 G W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ dist2In G W v) :
    ((nbrsInFinset G W v).powerset.filter
        (fun S => S.Nonempty ∧ u ∈ commonNbrs G S)).card ≤ 1 := by
  simpa using (fiber_card_le_pow (c := 1) (by norm_num) hW hv hu)

/-- Boundary check at `Δ = 0`: the distance-two set is empty. -/
theorem dist2In_eq_empty_of_degree_bound_zero
    {G : SimpleGraph V} {W : Set V} {v : V} (hv : v ∈ W)
    (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ 0) :
    dist2In G W v = ∅ := by
  have hle : (dist2In G W v).ncard ≤ 0 := by
    simpa using dist2In_ncard_le_sq (G := G) (W := W) (v := v) hv 0 hΔ
  exact (Set.ncard_eq_zero (s := dist2In G W v)).mp (Nat.eq_zero_of_le_zero hle)

/-- The frozen target statement, assembled from the independently checked seed
and the two bounds proved in this file. -/
theorem ineq_3 {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) ≤ (dist2In G W v).ncard * 2 ^ (c - 1) ∧
      (dist2In G W v).ncard ≤ min (Δ ^ 2) W.ncard := by
  exact ⟨sum_commonNbrs_dist2In_le hc hW hv,
    dist2In_ncard_le_min hv Δ hΔ⟩

end CClosedGraphs.Improved

end Prove2SwarmSubmission

open CClosedGraphs.Improved
open Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 0 < c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ) :
    (∑ S ∈ (Finset.univ.filter (fun x => x ∈ W ∧ G.Adj v x)).powerset.filter
          (fun S => S.Nonempty),
        (commonNbrs G S ∩ dist2In G W v).ncard) ≤ (dist2In G W v).ncard * 2 ^ (c - 1) ∧
      (dist2In G W v).ncard ≤ min (Δ ^ 2) W.ncard := by
  exact Prove2SwarmSubmission.CClosedGraphs.Improved.ineq_3 hc hW hv Δ hΔ
