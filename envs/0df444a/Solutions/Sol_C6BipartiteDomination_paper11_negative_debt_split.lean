-- Prove2me | solution 1 for C6BipartiteDomination.paper11_negative_debt_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:40.150985+00:00
-- url     : https://prove2.me/submissions/3ff17282-cd68-46d3-9c23-d71682854289

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11_negative_supports_eq_k3_union_k4
import Theorems.Thm_C6BipartiteDomination_paper11_k3_k4_supports_disjoint

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11NegativeSupports G D, -externalCharge G D w) =
      (∑ w ∈ paper11K3Supports G D, -externalCharge G D w) +
      (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) := by
  rw [paper11_negative_supports_eq_k3_union_k4 G hCan hmax,
    Finset.sum_union (paper11_k3_k4_supports_disjoint G)]
end C6BipartiteDomination
