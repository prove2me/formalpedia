-- Prove2me | solution 1 for DeletionCode.SignedSupport.gram_eq_target_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:32.428116+00:00
-- url     : https://prove2.me/submissions/43767da8-a75f-4ae4-b91e-9aceb149f73c

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ)
    (h : gram (F.path a sa) L i = gram (F.path b sb) L j) :
    SupportComponents.vertex F L a sa (i + 1) =
      SupportComponents.vertex F L b sb (j + 1) := by
  funext q
  have he := congrFun h ⟨q.val + 1, by have := q.isLt; omega⟩
  simpa only [gram, SupportComponents.vertex, Nat.add_assoc, Nat.add_comm 1 q.val] using he
end DeletionCode.SignedSupport
