-- Prove2me | solution 1 for DeletionCode.SpectrumPath.kunique_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:23:20.701828+00:00
-- url     : https://prove2.me/submissions/9d93387b-64a5-45af-a0ce-fa06d149e6f4

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
theorem _root_.solution (word : Letters) (n k m : ℕ)
    (hunique : KUnique word n k) (hkm : k ≤ m) : KUnique word n m := by
  intro a b ha hb hagree
  apply hunique a b (by omega) (by omega)
  intro i hi
  exact hagree i (by omega)
end DeletionCode.SpectrumPath
