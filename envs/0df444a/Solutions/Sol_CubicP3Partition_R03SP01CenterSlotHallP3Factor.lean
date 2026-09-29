-- Prove2me | solution 1 for CubicP3Partition.R03SP01CenterSlotHallP3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:28.452329+00:00
-- url     : https://prove2.me/submissions/58126491-1011-4462-a590-e848e2f9fd0d

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_adda565e91_r03_sp01_center_slot_factor_bridge_candidate_v1

universe w
namespace CubicP3Partition
noncomputable def R03SP01FactorCenterSet
    {V : Type w} [Fintype V]
    {G : SimpleGraph V} (p : P3Factor G) : Finset V := by
  classical
  exact Finset.univ.image (fun i : Fin p.blockCount =>
    p.place (i, (1 : Fin 3)))
end CubicP3Partition


namespace CubicP3Partition

universe u

set_option maxRecDepth 100000

theorem R03SP01CenterSlotCertificateP3Factor
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    (hC : R03SP01CenterSlotCertificate G C) :
    Nonempty (P3Factor G) := by
  classical
  rcases hC with ⟨n, eC, eL, hAdj⟩
  let jTo : Fin 3 → Fin 2 ⊕ Fin 1 := fun j =>
    if j = 0 then Sum.inl 0 else if j = 1 then Sum.inr 0 else Sum.inl 1
  let jInv : Fin 2 ⊕ Fin 1 → Fin 3 := fun s =>
    match s with
    | Sum.inl j => if j = 0 then 0 else 2
    | Sum.inr _ => 1
  have hjLeft : Function.LeftInverse jInv jTo := by
    intro j
    fin_cases j <;> simp [jTo, jInv]
  have hjRight : Function.RightInverse jInv jTo := by
    intro s
    cases s with
    | inl j =>
        fin_cases j <;> simp [jTo, jInv]
    | inr j =>
        fin_cases j <;> simp [jTo, jInv]
  let jEquiv : Fin 3 ≃ Fin 2 ⊕ Fin 1 :=
    { toFun := jTo
      invFun := jInv
      left_inv := hjLeft
      right_inv := hjRight }
  let Cset : Set V := (↑C : Set V)
  let place : (Fin n × Fin 3) ≃ V :=
    (Equiv.prodCongr (Equiv.refl (Fin n)) jEquiv).trans
      ((Equiv.prodSumDistrib (Fin n) (Fin 2) (Fin 1)).trans
        ((Equiv.sumCongr eL
          ((Equiv.prodUnique (Fin n) (Fin 1)).trans eC)).trans
          ((Equiv.sumComm (Csetᶜ : Set V) Cset).trans
            (Equiv.Set.sumCompl Cset))))
  have h0 (i : Fin n) : place (i, (0 : Fin 3)) = (eL (i, 0) : V) := by
    simp [place, jEquiv, jTo, Cset, Equiv.trans_apply]
    rfl
  have h1 (i : Fin n) : place (i, (1 : Fin 3)) = (eC i : V) := by
    simp [place, jEquiv, jTo, Cset, Equiv.trans_apply]
    rfl
  have h2 (i : Fin n) : place (i, (2 : Fin 3)) = (eL (i, 1) : V) := by
    simp [place, jEquiv, jTo, Cset, Equiv.trans_apply]
    rfl
  refine ⟨{
    blockCount := n
    place := place
    edge01 := ?_
    edge12 := ?_ }⟩
  · intro i
    rw [h0, h1]
    exact hAdj i 0
  · intro i
    rw [h1, h2]
    exact SimpleGraph.Adj.symm (hAdj i 1)

#print axioms R03SP01CenterSlotCertificate
#print axioms R03SP01CenterSlotCertificateP3Factor

theorem R03SP01CenterSlotCertificateAtIffHall
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    [DecidableEq V] [DecidableRel G.Adj]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2) :
    R03SP01CenterSlotCertificateAt G C n eC ↔
      R03SP01CenterSlotHallCondition G C n eC := by
  classical
  let rel : ((↑C : Set V)ᶜ : Set V) → (Fin n × Fin 2) → Prop :=
    fun a b => G.Adj (a : V) (eC b.1 : V)
  constructor
  · rintro ⟨eL, hAdj⟩
    intro A
    let S : Finset (Fin n × Fin 2) := A.image eL.symm
    have hSsub : S ⊆ Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, rel a b) := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨a, ha, ?_⟩
      simpa [rel] using hAdj ((eL.symm a).1) ((eL.symm a).2)
    have hScard : S.card = A.card := by
      dsimp [S]
      exact Finset.card_image_of_injective A eL.symm.injective
    change A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
      ∃ a ∈ A, rel a b)).card
    rw [← hScard]
    exact Finset.card_le_card hSsub
  · intro hHall
    change ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, rel a b)).card at hHall
    obtain ⟨f, hinj, hf⟩ :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall
    have hcard' : Fintype.card ((↑C : Set V)ᶜ : Set V) =
        Fintype.card (Fin n × Fin 2) := by
      simpa using hcard
    have hfbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard'⟩
    let ef : ((↑C : Set V)ᶜ : Set V) ≃ (Fin n × Fin 2) :=
      Equiv.ofBijective f hfbij
    let eL : (Fin n × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V) := ef.symm
    refine ⟨eL, ?_⟩
    intro i j
    have hrel := hf (eL (i, j))
    have heq : f (eL (i, j)) = (i, j) := ef.apply_symm_apply (i, j)
    rw [heq] at hrel
    exact hrel

#print axioms R03SP01CenterSlotCertificateAt
#print axioms R03SP01CenterSlotHallCondition
#print axioms R03SP01CenterSlotCertificateAtIffHall

/-- Convert an injective capacity-two assignment of all complementary
vertices into a center-slot certificate.  The cardinality equality upgrades
the finite injection to a bijection, so no unmatched leaf is hidden. -/
theorem R03SP01CenterSlotCertificateOfInjectiveAssignment
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (f : ((↑C : Set V)ᶜ : Set V) → (Fin n × Fin 2))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2)
    (hinj : Function.Injective f)
    (hAdj : ∀ x : ((↑C : Set V)ᶜ : Set V),
      G.Adj (x : V) (eC (f x).1 : V)) :
    R03SP01CenterSlotCertificate G C := by
  classical
  have hcard' : Fintype.card ((↑C : Set V)ᶜ : Set V) = Fintype.card (Fin n × Fin 2) := by
    simpa using hcard
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard'⟩
  let ef : ((↑C : Set V)ᶜ : Set V) ≃ (Fin n × Fin 2) := Equiv.ofBijective f hbij
  let eL : (Fin n × Fin 2) ≃ ((↑C : Set V)ᶜ : Set V) := ef.symm
  refine ⟨n, eC, eL, ?_⟩
  intro i j
  have h := hAdj (eL (i, j))
  have hf : f (eL (i, j)) = (i, j) := ef.apply_symm_apply (i, j)
  rw [hf] at h
  exact h

#print axioms R03SP01CenterSlotCertificateOfInjectiveAssignment


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    [DecidableEq V] [DecidableRel G.Adj]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2)
    (hHall : ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, G.Adj (a : V) (eC b.1 : V))).card) :
    Nonempty (P3Factor G) := by
  classical
  let rel : ((↑C : Set V)ᶜ : Set V) → (Fin n × Fin 2) → Prop :=
    fun a b => G.Adj (a : V) (eC b.1 : V)
  have hHall' : ∀ A : Finset ((↑C : Set V)ᶜ : Set V),
      A.card ≤ (Finset.univ.filter (fun b : Fin n × Fin 2 =>
        ∃ a ∈ A, rel a b)).card := by
    intro A
    simpa [rel] using hHall A
  obtain ⟨f, hinj, hf⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall'
  apply R03SP01CenterSlotCertificateP3Factor G C
  apply R03SP01CenterSlotCertificateOfInjectiveAssignment G C n eC f hcard hinj
  intro x
  exact hf x
