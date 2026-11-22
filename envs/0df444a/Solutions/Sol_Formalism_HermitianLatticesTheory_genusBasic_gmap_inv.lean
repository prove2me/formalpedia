-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_gmap_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:19.293872+00:00
-- url     : https://prove2.me/submissions/b9a8db2d-5d49-43a0-87d2-494d80890cb5

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_gmap_symm
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap


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
theorem _root_.solution (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g⁻¹ (gmap g L) = L := by
  first
  | exact isomAct_gmap_symm g L
  | (ext x; simp only [isomAct_mem_gmap]; simp)
end Formalism.HermitianLatticesTheory
