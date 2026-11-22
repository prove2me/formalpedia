-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:17.824795+00:00
-- url     : https://prove2.me/submissions/57881178-7c16-457f-a2f9-b100319fa68a

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
theorem _root_.solution {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by
  unfold invIdeal
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]
  rfl
end Formalism.HermitianLatticesTheory
