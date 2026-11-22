-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_mem_dualAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:19.247523+00:00
-- url     : https://prove2.me/submissions/4e7fae84-5bcc-4e8e-91c0-8775401874fc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (x : V) :
    x ∈ dualAt h p L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) p := by
  simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
end Formalism.HermitianLatticesTheory
