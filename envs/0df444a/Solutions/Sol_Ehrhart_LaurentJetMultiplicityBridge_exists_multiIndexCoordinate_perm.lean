-- Prove2me | solution 1 for Ehrhart.LaurentJetMultiplicityBridge.exists_multiIndexCoordinate_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/54855009-184f-4425-ab28-78e849e34476

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.LaurentJetMultiplicityBridge
open Set Filter Module
open scoped BigOperators Topology
namespace Ehrhart.LaurentJetMultiplicityBridge
theorem _root_.solution {n : ℕ}
    (α : Fin n → ℕ)
    (q : Fin (∑ i, α i) → Fin n)
    (hq : ∀ i : Fin n,
      Fintype.card {a : Fin (∑ i, α i) // q a = i} = α i) :
    ∃ σ : Equiv.Perm (Fin (∑ i, α i)),
      ∀ a, q a =
        AdaptedBergmanBasis.multiIndexCoordinate α (σ a) := by
  classical
  let e : ∀ i : Fin n,
      {a : Fin (∑ i, α i) // q a = i} ≃
        {a : Fin (∑ i, α i) //
          AdaptedBergmanBasis.multiIndexCoordinate α a = i} :=
    fun i => Fintype.equivOfCardEq (by
      calc
        Fintype.card {a : Fin (∑ i, α i) // q a = i} =
            α i := hq i
        _ = Fintype.card (Fin (α i)) :=
            (Fintype.card_fin (α i)).symm
        _ = Fintype.card
            {a : Fin (∑ i, α i) //
              AdaptedBergmanBasis.multiIndexCoordinate α a = i} :=
            (Fintype.card_congr
              (multiIndexCoordinateFiberEquiv α i)).symm)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  intro a
  exact (Equiv.ofFiberEquiv_map e a).symm
end Ehrhart.LaurentJetMultiplicityBridge
