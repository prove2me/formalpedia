-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:59.598093+00:00
-- url     : https://prove2.me/submissions/7b5f9da0-ccca-487f-a5ab-b8c0cedfa674

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open nonZeroDivisors
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V)
    (x y : V) : y ∈ neighbourCore h P L x ↔
      y ∈ L ∧ ∃ t ∈ conjIdeal (K := K) P, algebraMap R K t = h x y := by
  unfold neighbourCore
  simp only [Submodule.mem_inf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.mem_map, Algebra.linearMap_apply]
end Formalism.HermitianLatticesTheory
