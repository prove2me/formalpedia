-- Prove2me | solution 1 for DeletionCode.SignedSupport.suffix_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:03:40.627737+00:00
-- url     : https://prove2.me/submissions/1cfe782d-3d23-4a32-9f0a-c8d911f3ea10

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
    (b : B) (side : Bool) (i : ℕ) :
    gramSuffix (gram (F.path b side) L i) = SupportComponents.vertex F L b side (i + 1) := by
  funext q
  change F.path b side (i + (q.val + 1)) = F.path b side ((i + 1) + q.val)
  congr 1
  omega
end DeletionCode.SignedSupport
