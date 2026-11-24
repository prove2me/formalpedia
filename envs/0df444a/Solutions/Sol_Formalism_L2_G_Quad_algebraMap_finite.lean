-- Prove2me | solution 1 for Formalism.L2.G.Quad.algebraMap_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.506686+00:00
-- url     : https://prove2.me/submissions/dd9482f7-739a-4cee-b3e1-4dc08918da9b

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
theorem _root_.solution : (algebraMap R (QuadraticAlgebra R π 0)).Finite := by
  rw [RingHom.finite_algebraMap]
  infer_instance
end Formalism.L2.G.Quad
