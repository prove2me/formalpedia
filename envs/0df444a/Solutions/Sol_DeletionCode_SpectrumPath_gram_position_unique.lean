-- Prove2me | solution 1 for DeletionCode.SpectrumPath.gram_position_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:41.128451+00:00
-- url     : https://prove2.me/submissions/fde156b0-7ca6-46fc-8ced-0f108c35f445

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L a b : ℕ)
    (hunique : KUnique word n (L - 1))
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (heq : gram word L a = gram word L b) : a = b := by
  apply hunique a b (by omega) (by omega)
  intro i hi
  exact congrFun heq ⟨i, by omega⟩
end DeletionCode.SpectrumPath
