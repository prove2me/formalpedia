-- Prove2me | solution 1 for DeletionCode.DescriptionCount.description_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:58:21.108416+00:00
-- url     : https://prove2.me/submissions/2fff6e5b-193a-4567-91e2-54148696925b

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_DescriptionCount

set_option autoImplicit true
open DeletionCode DeletionCode.DescriptionCount
namespace DeletionCode.DescriptionCount
theorem _root_.solution (n L ν c : ℕ) :
    Fintype.card (Description n L ν c) =
      n ^ c * (4 * L) ^ ν * ν ^ c * ((fieldBound L ν) ^ 12) ^ (4 * ν) := by
  simp [Description, Fintype.card_prod, Fintype.card_fun]
  <;> ring
end DeletionCode.DescriptionCount
