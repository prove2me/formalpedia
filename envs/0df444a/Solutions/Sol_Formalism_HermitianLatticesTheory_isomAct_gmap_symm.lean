-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.isomAct_gmap_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:05.687301+00:00
-- url     : https://prove2.me/submissions/63ffdb0e-fb3d-42e5-93fc-87a51d94f48e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g.symm (gmap g L) = L := by
  ext x
  simp [isomAct_mem_gmap]
end Formalism.HermitianLatticesTheory
