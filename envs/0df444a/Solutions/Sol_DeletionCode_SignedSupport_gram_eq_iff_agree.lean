-- Prove2me | solution 1 for DeletionCode.SignedSupport.gram_eq_iff_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:17:37.197037+00:00
-- url     : https://prove2.me/submissions/c493c1a2-586a-40fc-9e23-75df945e5597

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution (p q : Letters) (L i j : ℕ) :
    gram p L i = gram q L j ↔ Agree p i q j L := by
  constructor
  · intro h r hr
    exact congrFun h ⟨r, hr⟩
  · intro h
    funext r
    exact h r.val r.isLt
end DeletionCode.SignedSupport
