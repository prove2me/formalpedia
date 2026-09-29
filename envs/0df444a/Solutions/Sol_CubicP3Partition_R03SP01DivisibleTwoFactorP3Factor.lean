-- Prove2me | solution 1 for CubicP3Partition.R03SP01DivisibleTwoFactorP3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:38.83339+00:00
-- url     : https://prove2.me/submissions/8efb2d58-f606-468b-bc61-7e944746a03b

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_eb25b3c47b_r03_sp01_divisible_cycle_bridge_candidate_v1

namespace CubicP3Partition

universe u

noncomputable section

set_option maxHeartbeats 1000000

/-- Bridge the canonical noncomputable degree to Mathlib's finite graph degree. -/
lemma R03SP01DegreeEqSimpleGraphDegree {X : Type u} [Fintype X]
    (H : SimpleGraph X) (x : X) [DecidableRel H.Adj] :
    CubicP3Partition.degree H x = H.degree x := by
  rw [CubicP3Partition.degree]
  rw [← H.card_neighborSet_eq_degree x]
  exact Nat.card_eq_fintype_card

/--
Candidate conditional bridge for the strengthened 2-factor route.
A connected 2-factor is a single finite cycle; if its order is divisible by
three, consecutive triples on that cycle form a non-induced P3-factor of the
ambient graph.  This is not the multi-component `HasDivisibleTwoFactor`
implication and does not assert the root theorem.
-/
theorem R03SP01ConnectedTwoFactorP3Factor
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (hconn : F.Connected)
    (hdiv : 3 ∣ Fintype.card V) :
    Nonempty (P3Factor G) := by
  classical
  have hFcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  obtain ⟨v⟩ := hconn.nonempty
  let c : F.ConnectedComponent := F.connectedComponentMk v
  have hv : v ∈ c.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hvne : (F.neighborSet v).Nonempty := by
    have hcard : (F.neighborSet v).ncard = 2 := by
      change Nat.card {w : V // F.Adj v w} = 2
      exact hTF.2 v
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨p, hp, hpverts⟩ :=
    hFcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := c) hv hvne
  have hc_univ : c.supp = Set.univ := by
    ext w
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    simp only [Set.mem_univ, iff_true]
    exact (SimpleGraph.ConnectedComponent.sound (hconn v w)).symm
  have hpverts_univ : p.toSubgraph.verts = Set.univ := hpverts.trans hc_univ
  have hsupport : p.support.toFinset = (Finset.univ : Finset V) := by
    ext w
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    rw [← p.mem_verts_toSubgraph, hpverts_univ]
    simp
  have htail_first : v ∈ p.support.tail := by
    exact p.end_mem_tail_support hp.not_nil
  have hsupport_card : p.support.toFinset.card = p.length := by
    calc
      p.support.toFinset.card = p.support.tail.toFinset.card := by
        apply congrArg Finset.card
        apply Finset.ext
        intro x
        simp only [List.mem_toFinset]
        rw [p.mem_support_iff]
        constructor
        · intro hx
          cases hx with
          | inl hx => simpa [hx] using htail_first
          | inr hx => exact hx
        · intro hx
          exact Or.inr hx
      _ = p.support.tail.length := List.toFinset_card_of_nodup hp.support_nodup
      _ = p.length := by simp [p.length_support]
  have hplen : p.length = Fintype.card V := by
    calc
      p.length = p.support.toFinset.card := hsupport_card.symm
      _ = (Finset.univ : Finset V).card := by rw [hsupport]
      _ = Fintype.card V := Finset.card_univ
  obtain ⟨k, hk⟩ := hdiv
  have hlen : p.length = k * 3 := by
    calc
      p.length = Fintype.card V := hplen
      _ = 3 * k := hk
      _ = k * 3 := Nat.mul_comm _ _
  have hham : p.IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hp, hplen⟩
  have htail_len : p.tail.support.length = k * 3 := by
    calc
      p.tail.support.length = Fintype.card V := hham.isHamiltonian_tail.length_support
      _ = 3 * k := hk
      _ = k * 3 := Nat.mul_comm _ _
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans ((finCongr htail_len.symm).trans hham.isHamiltonian_tail.getVertEquiv)
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have hi : 3 * (i : Nat) < p.tail.length := by
      rw [hham.isHamiltonian_tail.length_eq, hk]
      omega
    have hadj := p.tail.adj_getVert_succ hi
    simpa [finProdFinEquiv, finCongr,
      SimpleGraph.Walk.IsHamiltonian.getVertEquiv, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hTF.1 hadj
  · intro i
    have hi : 1 + 3 * (i : Nat) < p.tail.length := by
      rw [hham.isHamiltonian_tail.length_eq, hk]
      omega
    have hadj := p.tail.adj_getVert_succ hi
    have hidx : 1 + 3 * (i : Nat) + 1 = 2 + 3 * (i : Nat) := by
      omega
    have hadj' : F.Adj (p.tail.getVert (1 + 3 * (i : Nat)))
        (p.tail.getVert (2 + 3 * (i : Nat))) := by
      rw [← hidx]
      exact hadj
    simpa [finProdFinEquiv, finCongr,
      SimpleGraph.Walk.IsHamiltonian.getVertEquiv, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hTF.1 hadj'

theorem R03SP01GlueFiniteP3Factors
    {I : Type u} [Fintype I] {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : I → Nat)
    (place : (Σ i : I, Fin (k i) × Fin 3) ≃ V)
    (edge01 : ∀ (i : I) (j : Fin (k i)),
      G.Adj (place ⟨i, (j, 0)⟩) (place ⟨i, (j, 1)⟩))
    (edge12 : ∀ (i : I) (j : Fin (k i)),
      G.Adj (place ⟨i, (j, 1)⟩) (place ⟨i, (j, 2)⟩)) :
    Nonempty (P3Factor G) := by
  classical
  let J := Σ i : I, Fin (k i)
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let eBlock : (Fin (Fintype.card J) × Fin 3) ≃
      (Σ i : I, Fin (k i) × Fin 3) :=
    ((eJ.symm.prodCongr (Equiv.refl (Fin 3))).trans
      (R03SP01SigmaProdEquiv k))
  let globalPlace : (Fin (Fintype.card J) × Fin 3) ≃ V := eBlock.trans place
  refine ⟨{
    blockCount := Fintype.card J
    place := globalPlace
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro b
    generalize hb : eJ.symm b = z
    obtain ⟨i, j⟩ := z
    simpa [globalPlace, eBlock, R03SP01SigmaProdEquiv, hb] using edge01 i j
  · intro b
    generalize hb : eJ.symm b = z
    obtain ⟨i, j⟩ := z
    simpa [globalPlace, eBlock, R03SP01SigmaProdEquiv, hb] using edge12 i j


end
end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : HasDivisibleTwoFactor G) :
    Nonempty (P3Factor G) := by
  classical
  obtain ⟨F, hF⟩ := h
  have hFcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hF.1.2 v
  let rep : F.ConnectedComponent → V := fun c =>
    Classical.choose (SimpleGraph.ConnectedComponent.nonempty_supp c)
  have rep_mem (c : F.ConnectedComponent) : rep c ∈ c.supp := by
    exact Classical.choose_spec (SimpleGraph.ConnectedComponent.nonempty_supp c)
  have comp_card (c : F.ConnectedComponent) :
      Fintype.card c.supp = componentOrder F (rep c) := by
    let e : c.supp ≃ {w : V // F.Reachable (rep c) w} := {
      toFun := fun x => ⟨x.1,
        SimpleGraph.ConnectedComponent.exact
          ((rep_mem c).trans x.2.symm)⟩
      invFun := fun x => ⟨x.1,
        (SimpleGraph.ConnectedComponent.sound x.2).symm.trans (rep_mem c)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
    }
    calc
      Fintype.card c.supp = Fintype.card {w : V // F.Reachable (rep c) w} :=
        Fintype.card_congr e
      _ = componentOrder F (rep c) := by
        rw [componentOrder]
        exact Nat.card_eq_fintype_card.symm
  have comp_div (c : F.ConnectedComponent) : 3 ∣ Fintype.card c.supp := by
    rw [comp_card c]
    exact hF.2 (rep c)
  have local_two_factor (c : F.ConnectedComponent) :
      TwoFactor (G.induce c.supp) (F.induce c.supp) := by
    constructor
    · intro x y hxy
      exact hF.1.1 hxy
    · intro x
      have hsubset : F.neighborSet (x : V) ⊆ c.supp := by
        intro w hw
        exact c.mem_supp_of_adj_mem_supp x.property hw
      calc
        CubicP3Partition.degree (F.induce c.supp) x =
            (F.induce c.supp).degree x :=
          R03SP01DegreeEqSimpleGraphDegree _ _
        _ = F.degree (x : V) :=
          SimpleGraph.degree_induce_of_neighborSet_subset hsubset
        _ = CubicP3Partition.degree F (x : V) :=
          (R03SP01DegreeEqSimpleGraphDegree F (x : V)).symm
        _ = 2 := hF.1.2 (x : V)
  have local_connected (c : F.ConnectedComponent) :
      (F.induce c.supp).Connected := by
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using
      (SimpleGraph.ConnectedComponent.connected_toSimpleGraph c)
  let localFactor (c : F.ConnectedComponent) :
      P3Factor (G.induce c.supp) :=
    Classical.choice (R03SP01ConnectedTwoFactorP3Factor
      (G.induce c.supp) (F.induce c.supp) (local_two_factor c)
      (local_connected c) (comp_div c))
  let k : F.ConnectedComponent → Nat := fun c => (localFactor c).blockCount
  let localPlace (c : F.ConnectedComponent) :
      (Fin (k c) × Fin 3) ≃ c.supp := (localFactor c).place
  let fiberEquiv (c : F.ConnectedComponent) :
      (F.connectedComponentMk ⁻¹' ({c} : Set F.ConnectedComponent)) ≃ c.supp :=
    Equiv.setCongr (by
      ext x
      simp [SimpleGraph.ConnectedComponent.supp])
  let sigmaSupp : (Σ c : F.ConnectedComponent, c.supp) ≃ V :=
    (Equiv.sigmaCongrRight fiberEquiv).symm.trans
      (Equiv.sigmaPreimageEquiv F.connectedComponentMk)
  let sigmaLocal : (Σ c : F.ConnectedComponent,
      Fin (k c) × Fin 3) ≃ (Σ c : F.ConnectedComponent, c.supp) :=
    Equiv.sigmaCongrRight localPlace
  let sigmaPlace : (Σ c : F.ConnectedComponent,
      Fin (k c) × Fin 3) ≃ V := sigmaLocal.trans sigmaSupp
  apply R03SP01GlueFiniteP3Factors G k sigmaPlace
  · intro c j
    have hlocal := (localFactor c).edge01 j
    change G.Adj (localPlace c (j, 0)) (localPlace c (j, 1))
    exact hlocal
  · intro c j
    have hlocal := (localFactor c).edge12 j
    change G.Adj (localPlace c (j, 1)) (localPlace c (j, 2))
    exact hlocal
