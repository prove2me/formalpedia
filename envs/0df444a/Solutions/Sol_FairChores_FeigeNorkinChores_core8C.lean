-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.core8C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:27:21.604431+00:00
-- url     : https://prove2.me/submissions/8cbc9c50-7c63-451c-b693-2c840a860cf8

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
set_option maxRecDepth 40000
namespace FairChores.FeigeNorkinChores
theorem _root_.solution : ∀ a b c d e f g h : Fin 3,
    380 ≤ costOf fcR 0 a b c d e f g h ∨ 380 ≤ costOf fcC 1 a b c d e f g h ∨
      380 ≤ costOf fcU 2 a b c d e f g h := by decide
end FairChores.FeigeNorkinChores
