-- Prove2me | solution 1 for DeletionCode.OverlapCollision.collisionEncode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:46.29603+00:00
-- url     : https://prove2.me/submissions/31649ef1-a7b5-4507-885e-3dc8242271e5

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
import Theorems.Thm_DeletionCode_OverlapCollision_encode_injective_of_agree

set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery
namespace DeletionCode.OverlapCollision
theorem _root_.solution (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) : Function.Injective (collisionEncode n k a b hb) := by
  intro x y heq
  apply Subtype.ext
  exact encode_injective_of_agree n k a b hab hb x.val y.val x.property y.property heq
end DeletionCode.OverlapCollision
