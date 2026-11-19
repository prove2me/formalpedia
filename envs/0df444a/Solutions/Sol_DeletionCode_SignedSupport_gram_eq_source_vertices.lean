-- Prove2me | solution 1 for DeletionCode.SignedSupport.gram_eq_source_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:09:42.404296+00:00
-- url     : https://prove2.me/submissions/4f092ff7-8e32-47b6-88d8-acc31b906a6b

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
    SupportComponents.vertex F L a sa i = SupportComponents.vertex F L b sb j := by
  funext q
  exact congrFun h ⟨q.val, by have := q.isLt; omega⟩
end DeletionCode.SignedSupport
