-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massBasic_self_mem_genus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:56.978712+00:00
-- url     : https://prove2.me/submissions/655ab0e7-4693-4981-8358-f68864bca579

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V)
    (hL : Submodule.IsLattice K L) : L ∈ genus h L := by
  rw [genus, Set.mem_setOf_eq]
  refine ⟨hL, ?_⟩
  intro p _
  refine ⟨1, (isom h).one_mem, ?_⟩
  ext x
  simp [gmap]
end Formalism.HermitianLatticesTheory
