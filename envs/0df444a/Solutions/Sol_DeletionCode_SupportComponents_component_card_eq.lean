-- Prove2me | solution 1 for DeletionCode.SupportComponents.component_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:20.689475+00:00
-- url     : https://prove2.me/submissions/acdf079f-df95-4841-bdef-5b5667da3a1e

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Definitions.Def_DeletionCode_SupportComponents

set_option autoImplicit true
open DeletionCode DeletionCode.SupportComponents
open Windows RootSelection
namespace DeletionCode.SupportComponents
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    [Fintype (Components F L)] [Fintype (GraphComponents F L)] :
    Fintype.card (Components F L) = Fintype.card (GraphComponents F L) :=
  Fintype.card_congr (componentEquiv F L hL hstart)
end DeletionCode.SupportComponents
