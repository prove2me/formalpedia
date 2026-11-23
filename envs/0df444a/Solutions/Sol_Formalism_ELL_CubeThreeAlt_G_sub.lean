-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.G_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:38.398684+00:00
-- url     : https://prove2.me/submissions/dd598710-99ef-466b-8706-17ee2d189f40

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution (a1 a2 a3 a4 a6 z v v' : R) :
    G a1 a2 a3 a4 a6 z v - G a1 a2 a3 a4 a6 z v' = (v - v') * Hv a1 a2 a3 a4 a6 z v v' := by
  unfold Formalism.ELL.WeierstrassChordSeries.G Hv
  ring
end Formalism.ELL.CubeThreeAlt
