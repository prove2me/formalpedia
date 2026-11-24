-- Prove2me | solution 1 for FairSelling.FeigeNorkin.core8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:41.098967+00:00
-- url     : https://prove2.me/submissions/c237c8d3-37a6-4cdc-86a5-ac14dcc5cd66

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
set_option maxRecDepth 40000
namespace FairSelling.FeigeNorkin
theorem _root_.solution : ∀ a b c d e f g h : Fin 3,
    valOf fnR 0 a b c d e f g h ≤ 33 ∨ valOf fnC 1 a b c d e f g h ≤ 33 ∨
      valOf fnU 2 a b c d e f g h ≤ 33 := by decide
end FairSelling.FeigeNorkin
