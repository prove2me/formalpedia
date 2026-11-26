-- Prove2me | solution 1 for C6BipartiteDomination.paper11OwnerResource_sum_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:20.422299+00:00
-- url     : https://prove2.me/submissions/71bb49c7-683a-430e-98df-48a8b0ddacec

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11AllCompensation_sum_eq_owner_sums

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
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      paper11OwnerResource G D hCan hmax u) =
      (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        vertexCharge G D u) +
      ∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q := by
  classical
  simp only [paper11OwnerResource, Finset.sum_add_distrib]
  exact congrArg (fun x : ℤ => (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      vertexCharge G D u) + x)
    (paper11AllCompensation_sum_eq_owner_sums G hCan hmax)
end C6BipartiteDomination
