-- Prove2me | solution 1 for DvorakNorin2018.cloud_supply_le_separator_charge
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T16:18:27.96819+00:00
-- url     : https://prove2.me/submissions/0c77d6cf-bc1a-44d0-8a72-a68d8cb774a1

import Definitions.Def_TreewidthApprox_Pushed_Setting
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith

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

open TreewidthApprox.Pushed

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (supply : V → ℝ) (flow : V → V → ℝ) (α : ℝ)
    (hsupply : ∀ v, 0 ≤ supply v ∧ supply v ≤ 1)
    (hflow : ∀ u v, 0 ≤ flow u v)
    (hsupport : ∀ u v, ¬ G.Adj u v → flow u v = 0)
    (hsinks : ∀ u ∈ W, ∀ v, flow u v = 0)
    (hcons : ∀ v ∉ W, supply v + ∑ u, flow u v = ∑ u, flow v u)
    (hcongestion : ∀ v, supply v + ∑ u, flow u v ≤ α)
    (L S R : Finset V) (hpart : IsPartition3 Finset.univ L S R)
    (hno : NoEdge G L R) (hW : W ⊆ L ∪ S) :
    (∑ v, supply v) ≤ (L.card : ℝ) + α * S.card := by
  exact StableMSR.Recovery.CloudCut.separator_supply_bound G W supply flow α
    hsupply hflow hsupport hcons hcongestion L S R hpart hno hW
