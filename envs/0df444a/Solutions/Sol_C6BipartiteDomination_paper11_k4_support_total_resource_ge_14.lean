-- Prove2me | solution 1 for C6BipartiteDomination.paper11_k4_support_total_resource_ge_14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:01.101286+00:00
-- url     : https://prove2.me/submissions/6ccd7589-91ec-4e86-9f72-f92f65bbfc4c

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_k4_separate_support

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    ∃ u v, u ≠ v ∧
      16 ≤
        (vertexCharge G D u +
          ∑ q ∈ sharedCompensation G D (supportX G D w) u,
            externalCharge G D q) +
        (vertexCharge G D v +
          ∑ q ∈ sharedCompensation G D (supportX G D w) v,
            externalCharge G D q) ∧
      14 ≤
        (vertexCharge G D u +
          ∑ q ∈ sharedCompensation G D (supportX G D w) u,
            externalCharge G D q) +
        (vertexCharge G D v +
          ∑ q ∈ sharedCompensation G D (supportX G D w) v,
            externalCharge G D q) := by
  obtain ⟨u, v, hne, _, _, _, _, h8u, h8v⟩ :=
    paper11_k4_separate_support G hCan hmax hw
  refine ⟨u, v, hne, ?_, ?_⟩ <;> omega
end C6BipartiteDomination
