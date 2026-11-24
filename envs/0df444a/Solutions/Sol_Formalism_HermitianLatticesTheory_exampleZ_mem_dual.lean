-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:53.737242+00:00
-- url     : https://prove2.me/submissions/5a9a4216-b919-4d4d-a0ea-2bb843929fea

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : ℚ →ₗ⋆[ℚ] ℚ →ₗ[ℚ] ℚ) (L : Submodule ℤ ℚ) (x : ℚ) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule ℤ ℚ) := by
  unfold dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
end Formalism.HermitianLatticesTheory
