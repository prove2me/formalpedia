-- Prove2me | solution 1 for Formalism.L2.G.Quad.card_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.520867+00:00
-- url     : https://prove2.me/submissions/f59cca9e-645b-4012-b493-e80f9acdb333

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
theorem _root_.solution :
    Nat.card (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) =
      Nat.card (R ⧸ Ideal.span {π}) :=
  Nat.card_congr (resEquiv π).toEquiv
end Formalism.L2.G.Quad
