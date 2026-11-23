-- Prove2me | solution 1 for Formalism.L2.G.Quad.algebraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:23.4998+00:00
-- url     : https://prove2.me/submissions/3c57c57d-c0cd-4b86-b62e-65ffe8a26164

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Quad
open QuadraticAlgebra
variable {R : Type} [CommRing R] (π : R)
namespace Formalism.L2.G.Quad
theorem _root_.solution : Function.Injective (algebraMap R (QuadraticAlgebra R π 0)) := by
  intro x y h
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg QuadraticAlgebra.re h
end Formalism.L2.G.Quad
