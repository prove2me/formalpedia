-- Prove2me | solution 1 for EdenVerified.s03_periodic_common_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:16.56002+00:00
-- url     : https://prove2.me/submissions/bfa9e443-5803-42f9-9034-cdc54e9817c6

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest
import Theorems.Thm_Eden_commonIndexLocalDimension_periodic_isGreatest
import Theorems.Thm_Eden_commonIndex_periodic_gap
import Theorems.Thm_Eden_periodic_dimension_conventions_distinct


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' periodicEquilibriumSet c) (4-2/c) ∧
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) :=
  ⟨commonIndexLocalDimension_periodic_isGreatest hc, commonIndex_periodic_gap hc,
    asymptoticDimension_periodic_isGreatest hc, periodic_dimension_conventions_distinct hc⟩
end EdenVerified
