-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_dualAt_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:52.281653+00:00
-- url     : https://prove2.me/submissions/138a8979-24da-482e-99df-990389623d9b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_dualAt

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
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) {L M : Submodule R V}
    (hLM : L ≤ M) : dualAt h p M ≤ dualAt h p L := by
  intro x hx
  rw [locDual_mem_dualAt] at hx ⊢
  exact fun y hy => hx y (hLM hy)
end Formalism.HermitianLatticesTheory
