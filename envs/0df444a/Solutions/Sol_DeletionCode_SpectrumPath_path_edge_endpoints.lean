-- Prove2me | solution 1 for DeletionCode.SpectrumPath.path_edge_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:41.720341+00:00
-- url     : https://prove2.me/submissions/95fad3d9-d5f6-46f4-8ca3-af662c6f88cd

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
theorem _root_.solution (word : Letters) (L i : ℕ) :
    gramPrefix (gram word L i) = vertexAt word L i ∧
      gramSuffix (gram word L i) = vertexAt word L (i + 1) := by
  constructor
  · rfl
  · funext j
    change word (i + (j.val + 1)) = word (i + 1 + j.val)
    congr 1
    omega
end DeletionCode.SpectrumPath
