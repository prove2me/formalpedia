-- Prove2me | solution 1 for CubicP3Partition.R03SP01CenterSlotCertificateP3Factor
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T09:58:27.163291+00:00
-- url     : https://prove2.me/submissions/50d680a7-6034-47cc-b669-c5889bb6a933

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

end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
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
