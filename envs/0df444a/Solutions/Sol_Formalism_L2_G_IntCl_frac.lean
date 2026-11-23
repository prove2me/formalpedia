-- Prove2me | solution 1 for Formalism.L2.G.IntCl.frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:53.852045+00:00
-- url     : https://prove2.me/submissions/90254581-f559-4156-a53e-82d1a670b0e7

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.IntCl
open IsLocalRing
variable (A K L : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
  [IsScalarTower A K L]
include K
namespace Formalism.L2.G.IntCl
theorem _root_.solution : IsFractionRing (integralClosure A L) L :=
  integralClosure.isFractionRing_of_finite_extension (A := A) (K := K) (L := L)
end Formalism.L2.G.IntCl
