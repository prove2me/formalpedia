-- Prove2me | solution 1 for EdenVerified.p26_finiteTimeDimension_eq_asymptotic_on_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:19:24.749801+00:00
-- url     : https://prove2.me/submissions/6d73b3c5-b08f-42ef-b9e4-3b3162722ee4

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_finiteTimeDimension_eq_asymptotic_on_periodic


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c),
    finiteTimeDimension c t p = asymptoticDimension c p :=
  @Eden.finiteTimeDimension_eq_asymptotic_on_periodic
end EdenVerified
