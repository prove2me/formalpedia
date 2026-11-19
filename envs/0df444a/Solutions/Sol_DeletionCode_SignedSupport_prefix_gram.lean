-- Prove2me | solution 1 for DeletionCode.SignedSupport.prefix_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:18:12.085717+00:00
-- url     : https://prove2.me/submissions/8e0467a9-b118-48d7-8ae7-8b4fc5a5eae9

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
    gramPrefix (gram (F.path b side) L i) = SupportComponents.vertex F L b side i := rfl
end DeletionCode.SignedSupport
