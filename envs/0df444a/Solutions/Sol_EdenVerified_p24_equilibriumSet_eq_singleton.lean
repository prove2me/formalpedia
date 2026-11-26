-- Prove2me | solution 1 for EdenVerified.p24_equilibriumSet_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:15:27.375225+00:00
-- url     : https://prove2.me/submissions/df5024db-ac38-40ec-97d7-d2a604fd0ba2

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_equilibriumSet_eq_singleton


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : c ≠ 0),
    equilibriumSet c = {0} :=
  @Eden.equilibriumSet_eq_singleton
end EdenVerified
