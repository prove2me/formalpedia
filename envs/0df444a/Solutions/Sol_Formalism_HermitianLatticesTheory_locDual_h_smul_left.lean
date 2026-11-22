-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_h_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:29.550733+00:00
-- url     : https://prove2.me/submissions/ea2b5472-779f-4a36-b4fc-94c9c1f3922d

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h (r • y) x = star (algebraMap R K r) * h y x := by
  rw [← algebraMap_smul K r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]
end Formalism.HermitianLatticesTheory
