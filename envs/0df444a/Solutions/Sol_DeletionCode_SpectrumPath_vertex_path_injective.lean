-- Prove2me | solution 1 for DeletionCode.SpectrumPath.vertex_path_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:22:19.565222+00:00
-- url     : https://prove2.me/submissions/c7081e46-c33c-47e9-a819-cc955dfdc6eb

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
theorem _root_.solution (word : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1)) :
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) := by
  intro a b heq
  apply Fin.ext
  apply hunique a.val b.val
  · have := a.isLt
    omega
  · have := b.isLt
    omega
  · intro i hi
    exact congrFun heq ⟨i, hi⟩
end DeletionCode.SpectrumPath
