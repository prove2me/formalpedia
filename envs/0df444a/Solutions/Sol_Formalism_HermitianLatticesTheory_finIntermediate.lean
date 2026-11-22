-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.finIntermediate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:05.851836+00:00
-- url     : https://prove2.me/submissions/796689e4-31a3-42f6-878d-acd1e7cc7697

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : FinIntermediate := by
  intro W _ P Q hPQ hfin

  let f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q) := fun M =>
    (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))
  haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) :=
    Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q))
      (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q)))
      SetLike.coe_injective
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM N hN hMN
  have key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q →
      (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q := by
    intro M hPM _
    simp only [f]
    rw [AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']
    exact sup_eq_left.mpr fun x hx =>
      AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))
  have h1 : M.addSubgroupOf Q = N.addSubgroupOf Q := by
    rw [← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]
  have h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M := by
    intro M hMQ
    rw [AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]
  rw [← h2 M hM.2, ← h2 N hN.2, h1]
end Formalism.HermitianLatticesTheory
