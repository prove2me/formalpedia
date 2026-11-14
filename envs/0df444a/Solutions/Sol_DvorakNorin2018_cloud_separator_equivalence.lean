-- Prove2me | solution 1 for DvorakNorin2018.cloud_separator_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T17:20:14.081647+00:00
-- url     : https://prove2.me/submissions/60496610-edf6-4035-a7dc-7ca9f7f18983

import Definitions.Def_DvorakNorin2018_SplitNetwork
import Theorems.Thm_VanderbeiLP_Networks_max_flow_min_cut
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
open scoped Classical BigOperators

namespace StableMSR.Recovery.CloudCut
open TreewidthApprox.Pushed

noncomputable def crossFlow {V : Type} [Fintype V]
    (flow : V → V → ℝ) (A B : Finset V) : ℝ := ∑ x ∈ A, ∑ y ∈ B, flow x y

lemma conservation_cut {V : Type} [Fintype V] [DecidableEq V]
    (supply : V → ℝ) (flow : V → V → ℝ) (R : Finset V)
    (hcons : ∀ v ∈ R, supply v + ∑ u, flow u v = ∑ u, flow v u) :
    (∑ v ∈ R, supply v) + crossFlow flow Rᶜ R = crossFlow flow R Rᶜ := by
  have heq := Finset.sum_congr rfl hcons
  rw [Finset.sum_add_distrib] at heq
  have hout : (∑ v ∈ R, ∑ u, flow v u) = crossFlow flow R R + crossFlow flow R Rᶜ := by
    unfold crossFlow
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => (Finset.sum_add_sum_compl R (fun u => flow v u)).symm)
  have hin : (∑ v ∈ R, ∑ u, flow u v) = crossFlow flow R R + crossFlow flow Rᶜ R := by
    rw [Finset.sum_comm]
    unfold crossFlow
    exact (Finset.sum_add_sum_compl R (fun u => ∑ v ∈ R, flow u v)).symm
  rw [hout, hin] at heq
  linarith

/- The supply outside a vertex cut must flow into the cut or across its boundary. -/
theorem supply_le_outgoing {V : Type} [Fintype V] [DecidableEq V]
    (supply : V → ℝ) (flow : V → V → ℝ) (R : Finset V)
    (hnonneg : ∀ x y, 0 ≤ flow x y)
    (hcons : ∀ v ∈ R, supply v + ∑ u, flow u v = ∑ u, flow v u) :
    (∑ v ∈ R, supply v) ≤ crossFlow flow R Rᶜ := by
  have h := conservation_cut supply flow R hcons
  have hn : 0 ≤ crossFlow flow Rᶜ R :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hnonneg x y))
  linarith

/- The forward implication of Dvořák–Norin Observation 5: every separator
bounding the sink side bounds the total supply of a bounded-congestion cloud. -/
theorem separator_supply_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (supply : V → ℝ) (flow : V → V → ℝ) (α : ℝ)
    (hsupply : ∀ v, 0 ≤ supply v ∧ supply v ≤ 1)
    (hflow : ∀ u v, 0 ≤ flow u v)
    (hsupport : ∀ u v, ¬ G.Adj u v → flow u v = 0)
    (hcons : ∀ v ∉ W, supply v + ∑ u, flow u v = ∑ u, flow v u)
    (hcongestion : ∀ v, supply v + ∑ u, flow u v ≤ α)
    (L S R : Finset V) (hpart : IsPartition3 Finset.univ L S R)
    (hno : NoEdge G L R) (hW : W ⊆ L ∪ S) :
    (∑ v, supply v) ≤ (L.card : ℝ) + α * S.card := by
  classical
  have hRnot : ∀ v ∈ R, v ∉ W := by
    intro v hvR hvW
    rcases Finset.mem_union.mp (hW hvW) with hvL | hvS
    · exact Finset.disjoint_left.mp hpart.2.1 hvL hvR
    · exact Finset.disjoint_left.mp hpart.2.2.1 hvS hvR
  have hR : (∑ v ∈ R, supply v) ≤ crossFlow flow R Rᶜ :=
    supply_le_outgoing supply flow R hflow (fun v hv => hcons v (hRnot v hv))
  have hRcompl : Rᶜ = L ∪ S := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_union]
    constructor
    · intro hn
      have hu : v ∈ L ∪ S ∪ R := by rw [hpart.2.2.2]; exact Finset.mem_univ v
      rcases Finset.mem_union.mp hu with h | h
      · exact Finset.mem_union.mp h
      · exact False.elim (hn h)
    · rintro (hL | hS)
      · exact fun hR => Finset.disjoint_left.mp hpart.2.1 hL hR
      · exact fun hR => Finset.disjoint_left.mp hpart.2.2.1 hS hR
  have hcross : crossFlow flow R Rᶜ = crossFlow flow R S := by
    rw [hRcompl]
    unfold crossFlow
    apply Finset.sum_congr rfl
    intro v hvR
    rw [Finset.sum_union hpart.1]
    have hz : ∑ u ∈ L, flow v u = 0 := Finset.sum_eq_zero (by
      intro u hu
      exact hsupport v u (fun h => hno u hu v hvR h.symm))
    rw [hz, zero_add]
  have hle : crossFlow flow R S ≤ ∑ v ∈ S, ∑ u, flow u v := by
    unfold crossFlow
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun v _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ R) (fun u _ _ => hflow u v))
  have hS : (∑ v ∈ S, supply v) + ∑ v ∈ R, supply v ≤ α * S.card := by
    have hc : (∑ v ∈ S, supply v) + (∑ v ∈ S, ∑ u, flow u v) ≤ α * S.card := by
      rw [← Finset.sum_add_distrib]
      calc
        _ ≤ ∑ _v ∈ S, α := Finset.sum_le_sum (fun v _ => hcongestion v)
        _ = _ := by simp [mul_comm]
    rw [hcross] at hR
    linarith
  have hL : (∑ v ∈ L, supply v) ≤ (L.card : ℝ) := by
    calc
      _ ≤ ∑ _v ∈ L, (1 : ℝ) := Finset.sum_le_sum (fun v _ => (hsupply v).2)
      _ = _ := by simp
  have htotal : (∑ v, supply v) = (∑ v ∈ L, supply v) + (∑ v ∈ S, supply v) +
      ∑ v ∈ R, supply v := by
    rw [← hpart.2.2.2]
    rw [Finset.sum_union, Finset.sum_union hpart.1]
    exact Finset.disjoint_union_left.mpr ⟨hpart.2.1, hpart.2.2.1⟩
  rw [htotal]
  linarith

end StableMSR.Recovery.CloudCut

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.SplitNetwork
open TreewidthApprox.Pushed
lemma sum_nodes {V : Type} [Fintype V] (f : Node V → ℝ) :
    (∑ x, f x) = f source + f sink + (∑ v, f (input v)) + ∑ v, f (output v) := by
  simp only [Node, Fintype.sum_sum_type, Fintype.sum_unique, source, sink, input, output]
  <;> simp only [add_assoc]
lemma capacity_nonneg {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M) (x y : Node V) :
    0 ≤ capacity G W α M x y := by
  rcases x with u | (u | (v | v)) <;> rcases y with w | (w | (z | z)) <;>
    simp only [capacity] <;> (try split_ifs) <;> positivity
lemma row_nonneg {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M) (C : Finset (Node V)) (x : Node V) :
    0 ≤ row G W α M C x := by
  unfold row
  split_ifs
  · exact Finset.sum_nonneg (fun y _ => by by_cases h : y ∉ C <;> simp only [h, ite_true, ite_false]; exact capacity_nonneg G W α M hα hM x y; rfl)
  · rfl
lemma entry_le_cut {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M) (C : Finset (Node V))
    (x y : Node V) (hx : x ∈ C) (hy : y ∉ C) : capacity G W α M x y ≤ cut G W α M C := by
  have h₁ : capacity G W α M x y ≤ row G W α M C x := by
    unfold row
    rw [if_pos hx]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun z => if z ∉ C then capacity G W α M x z else 0)
      (fun z _ => by by_cases h : z ∉ C <;> simp only [h, ite_true, ite_false]; exact capacity_nonneg G W α M hα hM x z; rfl) (Finset.mem_univ y)
    simpa only [if_pos hy] using h
  exact h₁.trans (Finset.single_le_sum (fun z _ => row_nonneg G W α M hα hM C z) (Finset.mem_univ x))
lemma source_row {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (C : Finset (Node V)) (hs : source ∈ C) :
    row G W α M C source = ((Finset.univ.filter (fun v => input v ∉ C)).card : ℝ) := by
  unfold row
  rw [if_pos hs, sum_nodes]
  simp only [capacity, source, sink, input, output]
  simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_not]
lemma sink_row {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (C : Finset (Node V)) : row G W α M C sink = 0 := by
  unfold row
  split_ifs <;> simp [sum_nodes, capacity, source, sink, input, output]
lemma input_row {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (C : Finset (Node V)) (v : V) :
    row G W α M C (input v) = if input v ∈ C ∧ output v ∉ C then α else 0 := by
  unfold row
  by_cases hi : input v ∈ C
  · rw [if_pos hi, sum_nodes]
    simp only [capacity, source, sink, input, output, ite_self, Finset.sum_const_zero, zero_add, add_zero]
    try simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
    have hif : ∀ w, (if output w ∉ C then if v = w then α else 0 else 0) =
        if v = w then (if output v ∉ C then α else 0) else 0 := by
      intro w; by_cases h : v = w <;> simp [h]
    change (∑ w, if output w ∉ C then if v = w then α else 0 else 0) = _
    simp_rw [hif]
    simp [hi, eq_comm]
  · simp [hi]
/- A low-capacity split-network cut yields a separator of no greater charge. -/
theorem separator_of_cut {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M s : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hMs : s < M) (C : Finset (Node V)) (hsource : source ∈ C) (hsink : sink ∉ C)
    (hcut : cut G W α M C ≤ s) :
    ∃ L S R : Finset V, IsPartition3 Finset.univ L S R ∧ NoEdge G L R ∧
      W ⊆ L ∪ S ∧ (L.card : ℝ) + α * S.card ≤ s := by
  classical
  let L := Finset.univ.filter (fun v => input v ∉ C)
  let S := Finset.univ.filter (fun v => input v ∈ C ∧ output v ∉ C)
  let R := Finset.univ.filter (fun v => input v ∈ C ∧ output v ∈ C)
  have hpart : IsPartition3 Finset.univ L S R := by
    refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, ?_⟩
    · intro v hv hv'; exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hv').2.1
    · intro v hv hv'; exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hv').2.1
    · intro v hv hv'; exact (Finset.mem_filter.mp hv).2.2 (Finset.mem_filter.mp hv').2.2
    · ext v; simp only [L, S, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
  have hWout : ∀ v ∈ W, output v ∉ C := by
    intro v hv hvc
    have h := entry_le_cut G W α M hα hM C (output v) sink hvc hsink
    have hc : capacity G W α M (output v) sink = M := by simp [capacity, output, sink, hv]
    rw [hc] at h
    exact (not_le_of_gt hMs) (h.trans hcut)
  have hW : W ⊆ L ∪ S := by
    intro v hv
    by_cases hi : input v ∈ C
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hWout v hv⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hno : NoEdge G L R := by
    intro v hv w hw hadj
    have hwi := (Finset.mem_filter.mp hw).2
    have hwW : w ∉ W := fun h => hWout w h hwi.2
    have h := entry_le_cut G W α M hα hM C (output w) (input v) hwi.2 (Finset.mem_filter.mp hv).2
    have hc : capacity G W α M (output w) (input v) = M := by
      simp [capacity, output, input, hadj.symm, hwW]
    rw [hc] at h
    exact (not_le_of_gt hMs) (h.trans hcut)
  have hrows : (∑ v, row G W α M C (input v)) = α * S.card := by
    simp_rw [input_row]
    change (∑ v, if input v ∈ C ∧ output v ∉ C then α else 0) = _
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    change (S.card : ℝ) * α = α * S.card
    exact mul_comm _ _
  have hnonneg : 0 ≤ ∑ v, row G W α M C (output v) :=
    Finset.sum_nonneg (fun v _ => row_nonneg G W α M hα hM C (output v))
  have hc : cut G W α M C = (L.card : ℝ) + α * S.card +
      ∑ v, row G W α M C (output v) := by
    rw [cut, sum_nodes, source_row G W α M C hsource, sink_row, hrows, add_zero]
  exact ⟨L, S, R, hpart, hno, hW, by linarith⟩
end StableMSR.Recovery.SplitNetwork
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.MatrixMaxFlow
open VanderbeiLP.Networks
noncomputable def arcs (N : Type*) [Fintype N] [DecidableEq N] : Finset (N × N) :=
  Finset.univ.filter (fun a => a.1 ≠ a.2)
lemma arcs_network (N : Type*) [Fintype N] [DecidableEq N] : IsNetwork (arcs N) := by
  intro a ha; exact (Finset.mem_filter.mp ha).2
lemma incoming {N : Type*} [Fintype N] [DecidableEq N] (f : N × N → ℝ) (k : N) :
    (∑ a ∈ (arcs N).filter (fun a => a.2 = k), f a) = ∑ u, if u = k then 0 else f (u,k) := by
  simp only [arcs, Finset.filter_filter, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  have heq : ∀ v, (if u ≠ v ∧ v = k then f (u,v) else 0) =
      if v = k then (if u = k then 0 else f (u,k)) else 0 := by
    intro v; by_cases hv : v = k <;> by_cases hu : u = k <;> simp [hv,hu]
  simp_rw [heq]
  simp
lemma outgoing {N : Type*} [Fintype N] [DecidableEq N] (f : N × N → ℝ) (k : N) :
    (∑ a ∈ (arcs N).filter (fun a => a.1 = k), f a) = ∑ u, if k = u then 0 else f (k,u) := by
  simp only [arcs, Finset.filter_filter, Finset.sum_filter, Fintype.sum_prod_type]
  have heq : ∀ u v, (if u ≠ v ∧ u = k then f (u,v) else 0) =
      if u = k then (if k = v then 0 else f (k,v)) else 0 := by
    intro u v; by_cases hu : u = k <;> by_cases hv : k = v <;> simp_all
  simp_rw [heq]
  simp
lemma capacity_cut {N : Type*} [Fintype N] [DecidableEq N] (c : N → N → ℝ) (C : Finset N) :
    cutCapacity (arcs N) (fun a => c a.1 a.2) C =
      ∑ x, if x ∈ C then ∑ y, if y ∉ C then c x y else 0 else 0 := by
  simp only [cutCapacity, arcs, Finset.filter_filter, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ C
  · rw [if_pos hx]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ C <;> by_cases hxy : x = y <;> simp_all
  · simp [hx]
/- The canonical max-flow theorem, translated to a full capacity matrix. -/
theorem exists_matrix_flow {N : Type*} [Fintype N] [DecidableEq N]
    (c : N → N → ℝ) (hn : ∀ x y, 0 ≤ c x y) (hd : ∀ x, c x x = 0)
    (source sink : N) (hst : source ≠ sink) (s : ℝ)
    (hcuts : ∀ C : Finset N, source ∈ C → sink ∉ C →
      s < ∑ x, if x ∈ C then ∑ y, if y ∉ C then c x y else 0 else 0) :
    ∃ f : N → N → ℝ, ∃ value : ℝ, s < value ∧
      (∀ x y, 0 ≤ f x y ∧ f x y ≤ c x y) ∧
      ∀ x, (∑ y, f y x) + (if x = source then value else 0) =
        (∑ y, f x y) + (if x = sink then value else 0) := by
  classical
  obtain ⟨value, hmax, hmin⟩ := max_flow_min_cut (arcs N) (arcs_network N)
    (fun a => c a.1 a.2) (fun a _ => hn _ _) source sink hst
  obtain ⟨C, hC, hval⟩ := hmin.1
  have hlt : s < value := by
    rw [← hval, capacity_cut]; exact hcuts C hC.1 hC.2
  obtain ⟨f, hf⟩ := hmax.1
  refine ⟨fun x y => if x = y then 0 else f (x,y), value, hlt, ?_, ?_⟩
  · intro x y; by_cases hxy : x = y
    · subst y; simp [hd]
    · simpa only [if_neg hxy] using hf.1 (x,y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩)
  · intro x
    have h := hf.2.2 x
    rw [incoming, outgoing] at h
    linarith
end StableMSR.Recovery.MatrixMaxFlow

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.SplitNetwork

lemma bounded_zero {V : Type} [DecidableEq V] (G : SimpleGraph V) (W : Finset V)
    (α M : ℝ) (f : Node V → Node V → ℝ)
    (hb : ∀ x y, 0 ≤ f x y ∧ f x y ≤ capacity G W α M x y)
    {x y : Node V} (hc : capacity G W α M x y = 0) : f x y = 0 :=
  le_antisymm ((hb x y).2.trans_eq hc) (hb x y).1

/- Decode the actual split-network flow into a bounded-congestion cloud. -/
theorem decode_network_flow {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M : ℝ)
    (f : Node V → Node V → ℝ) (value : ℝ)
    (hb : ∀ x y, 0 ≤ f x y ∧ f x y ≤ capacity G W α M x y)
    (hc : ∀ x, (∑ y, f y x) + (if x = source then value else 0) =
      (∑ y, f x y) + (if x = sink then value else 0)) :
    ∃ (g : V → ℝ) (h : V → V → ℝ),
      (∀ v, 0 ≤ g v ∧ g v ≤ 1) ∧ (∀ u v, 0 ≤ h u v) ∧
      (∀ u v, ¬ G.Adj u v → h u v = 0) ∧
      (∀ u ∈ W, ∀ v, h u v = 0) ∧
      (∀ v ∉ W, g v + ∑ u, h u v = ∑ u, h v u) ∧
      (∀ v, g v + ∑ u, h u v ≤ α) ∧ (∑ v, g v) = value := by
  classical
  have hz : ∀ {x y}, capacity G W α M x y = 0 → f x y = 0 :=
    fun {_ _} h => bounded_zero G W α M f hb h
  have hin (v : V) : (∑ y, f y (input v)) = f source (input v) + ∑ u, f (output u) (input v) := by
    rw [sum_nodes]
    have h₁ : f sink (input v) = 0 := hz (by rfl)
    have h₂ : (∑ u, f (input u) (input v)) = 0 := Finset.sum_eq_zero (fun u _ => hz (by rfl))
    rw [h₁, h₂]; simp
  have hout (v : V) : (∑ y, f (input v) y) = f (input v) (output v) := by
    rw [sum_nodes]
    have h₁ : f (input v) source = 0 := hz (by rfl)
    have h₂ : f (input v) sink = 0 := hz (by rfl)
    have h₃ : (∑ u, f (input v) (input u)) = 0 := Finset.sum_eq_zero (fun u _ => hz (by rfl))
    rw [h₁, h₂, h₃]; simp only [zero_add]
    apply Finset.sum_eq_single v
    · intro u _ huv
      exact hz (by simp [capacity, huv.symm])
    · simp
  have hinout (v : V) : (∑ y, f y (output v)) = f (input v) (output v) := by
    rw [sum_nodes]
    have h₁ : f source (output v) = 0 := hz (by rfl)
    have h₂ : f sink (output v) = 0 := hz (by rfl)
    have h₃ : (∑ u, f (output u) (output v)) = 0 := Finset.sum_eq_zero (fun u _ => hz (by rfl))
    rw [h₁, h₂, h₃]; simp only [zero_add, add_zero]
    apply Finset.sum_eq_single v
    · intro u _ huv
      exact hz (by simp [capacity, huv])
    · simp
  have houtout (v : V) (hv : v ∉ W) : (∑ y, f (output v) y) = ∑ u, f (output v) (input u) := by
    rw [sum_nodes]
    have h₁ : f (output v) source = 0 := hz (by rfl)
    have h₂ : f (output v) sink = 0 := hz (by simp [capacity, hv])
    have h₃ : (∑ u, f (output v) (output u)) = 0 := Finset.sum_eq_zero (fun u _ => hz (by rfl))
    rw [h₁, h₂, h₃]; simp
  have hi (v : V) : f source (input v) + ∑ u, f (output u) (input v) = f (input v) (output v) := by
    have h := hc (input v)
    simpa [hin, hout, input, output, source, sink] using h
  have ho (v : V) (hv : v ∉ W) : f (input v) (output v) = ∑ u, f (output v) (input u) := by
    have h := hc (output v)
    simpa [hinout, houtout v hv, output, input, source, sink] using h
  refine ⟨fun v => f source (input v), fun u v => f (output u) (input v), ?_,
    fun u v => (hb _ _).1, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [capacity] using hb source (input v)
  · intro u v hn
    exact hz (by simp [capacity, hn])
  · intro u hu v
    exact hz (by simp [capacity, hu])
  · intro v hv
    exact (hi v).trans (ho v hv)
  · intro v
    rw [hi v]
    simpa only [capacity, if_true] using (hb (input v) (output v)).2
  · have h := hc source
    have h₁ : (∑ y, f y source) = 0 := Finset.sum_eq_zero (fun y _ => hz (by
      rcases y with u | (u | (v | v)) <;> rfl))
    have h₂ : (∑ y, f source y) = ∑ v, f source (input v) := by
      rw [sum_nodes]
      have hss : f source source = 0 := hz (by rfl)
      have hst : f source sink = 0 := hz (by rfl)
      have hso : (∑ v, f source (output v)) = 0 := Finset.sum_eq_zero (fun v _ => hz (by rfl))
      rw [hss, hst, hso]; simp
    simpa only [h₁, h₂, source, sink, reduceCtorEq, ite_true, ite_false, zero_add, add_zero] using h.symm
end StableMSR.Recovery.SplitNetwork
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.SplitNetwork
open TreewidthApprox.Pushed
/- The complete converse in Observation 5, including the finite network and decoding. -/
theorem cloud_of_no_small_separator {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hsep : ∀ L S R : Finset V, IsPartition3 Finset.univ L S R → NoEdge G L R →
      W ⊆ L ∪ S → s < (L.card : ℝ) + α * S.card) :
    ∃ (g : V → ℝ) (f : V → V → ℝ),
      (∀ v, 0 ≤ g v ∧ g v ≤ 1) ∧ (∀ u v, 0 ≤ f u v) ∧
      (∀ u v, ¬ G.Adj u v → f u v = 0) ∧ (∀ u ∈ W, ∀ v, f u v = 0) ∧
      (∀ v ∉ W, g v + ∑ u, f u v = ∑ u, f v u) ∧
      (∀ v, g v + ∑ u, f u v ≤ α) ∧ s < ∑ v, g v := by
  classical
  let M := s + 1
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hMs : s < M := by dsimp [M]; linarith
  have hd : ∀ x : Node V, capacity G W α M x x = 0 := by
    intro x; rcases x with u | (u | (v | v)) <;> rfl
  have hcuts : ∀ C : Finset (Node V), source ∈ C → sink ∉ C → s < cut G W α M C := by
    intro C hc ht
    by_contra hn
    obtain ⟨L,S,R,hp,hno,hW,hcharge⟩ := separator_of_cut G W α M s hα hM hMs C hc ht (le_of_not_gt hn)
    exact (not_le_of_gt (hsep L S R hp hno hW)) hcharge
  obtain ⟨flow,value,hvalue,hb,hcons⟩ := MatrixMaxFlow.exists_matrix_flow
    (capacity G W α M) (capacity_nonneg G W α M hα hM) hd source sink (by intro h; cases h) s hcuts
  obtain ⟨g,f,hg,hf,hgraph,hW,hcon,hcong,htotal⟩ := decode_network_flow G W α M flow value hb hcons
  exact ⟨g,f,hg,hf,hgraph,hW,hcon,hcong,htotal.symm ▸ hvalue⟩
/- Dvořák–Norin Observation 5 in full, with the separator formulation explicit. -/
theorem cloud_separator_equivalence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (∃ (g : V → ℝ) (f : V → V → ℝ),
      (∀ v, 0 ≤ g v ∧ g v ≤ 1) ∧ (∀ u v, 0 ≤ f u v) ∧
      (∀ u v, ¬ G.Adj u v → f u v = 0) ∧ (∀ u ∈ W, ∀ v, f u v = 0) ∧
      (∀ v ∉ W, g v + ∑ u, f u v = ∑ u, f v u) ∧
      (∀ v, g v + ∑ u, f u v ≤ α) ∧ s < ∑ v, g v) ↔
    ∀ L S R : Finset V, IsPartition3 Finset.univ L S R → NoEdge G L R →
      W ⊆ L ∪ S → s < (L.card : ℝ) + α * S.card := by
  constructor
  · rintro ⟨g,f,hg,hf,hgraph,hW,hcon,hcong,hvalue⟩ L S R hp hn hside
    exact hvalue.trans_le (CloudCut.separator_supply_bound G W g f α hg hf hgraph hcon hcong L S R hp hn hside)
  · exact cloud_of_no_small_separator G W α s hα hs
end StableMSR.Recovery.SplitNetwork
open TreewidthApprox.Pushed
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (∃ (g : V → ℝ) (f : V → V → ℝ),
      (∀ v, 0 ≤ g v ∧ g v ≤ 1) ∧ (∀ u v, 0 ≤ f u v) ∧
      (∀ u v, ¬ G.Adj u v → f u v = 0) ∧ (∀ u ∈ W, ∀ v, f u v = 0) ∧
      (∀ v ∉ W, g v + ∑ u, f u v = ∑ u, f v u) ∧
      (∀ v, g v + ∑ u, f u v ≤ α) ∧ s < ∑ v, g v) ↔
    ∀ L S R : Finset V, IsPartition3 Finset.univ L S R → NoEdge G L R →
      W ⊆ L ∪ S → s < (L.card : ℝ) + α * S.card := by
  exact StableMSR.Recovery.SplitNetwork.cloud_separator_equivalence G W α s hα hs
