-- Prove2me | solution 1 for DinitzGargGoemans.univRouteChoice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:45:47.299901+00:00
-- url     : https://prove2.me/submissions/25ff5bca-4730-441b-9893-66884e45a890

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution :
    (Finset.univ : Finset RouteChoice) = {.paid, .free} := by
  decide
end DinitzGargGoemans
