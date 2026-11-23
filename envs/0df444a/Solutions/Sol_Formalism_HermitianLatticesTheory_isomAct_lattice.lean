-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.isomAct_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:45.771984+00:00
-- url     : https://prove2.me/submissions/40d473bc-9732-4296-8356-7d56c58de5d5

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct

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
theorem _root_.solution (g : V ≃ₗ[K] V) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (gmap g L) := by
  have e : ((gmap g L : Submodule R V) : Set V) = (g : V →ₗ[K] V) '' (L : Set V) := by
    ext x
    simp [gmap]
  refine ⟨hL.fg.map _, ?_⟩
  rw [e, Submodule.span_image, hL.span_eq_top, Submodule.map_top]
  exact LinearEquiv.range g
end Formalism.HermitianLatticesTheory
