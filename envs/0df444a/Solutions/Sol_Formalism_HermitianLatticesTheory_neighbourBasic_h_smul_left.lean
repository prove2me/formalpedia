-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourBasic_h_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:58.089717+00:00
-- url     : https://prove2.me/submissions/e01c58cf-8403-4076-a4c8-5f37a91030f6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (a : R) (x y : V) :
    h (a • x) y = star (algebraMap R K a) * h x y := by
  rw [← algebraMap_smul K a x, LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
end Formalism.HermitianLatticesTheory
