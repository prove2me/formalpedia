-- Prove2me | solution 1 for DinitzGargGoemans.univArc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:45:37.530387+00:00
-- url     : https://prove2.me/submissions/b69bcfc2-43c9-47c0-8c86-55945ba6e9ae

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
    (Finset.univ : Finset Arc) =
      {.sT1, .sT2, .sU, .uV, .uT3, .vT1, .vW, .wT2, .wT3} := by
  decide
end DinitzGargGoemans
