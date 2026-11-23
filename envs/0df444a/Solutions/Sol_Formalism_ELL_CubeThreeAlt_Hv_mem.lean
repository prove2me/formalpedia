-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.Hv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:06.389281+00:00
-- url     : https://prove2.me/submissions/ce8010df-6406-4e37-991d-0e5b2ef5f861

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
theorem _root_.solution (T : Subring R) {a1 a2 a3 a4 a6 z v v' : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T)
    (h3 : a3 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hz : z ∈ T) (hv : v ∈ T) (hv' : v' ∈ T) :
    Hv a1 a2 a3 a4 a6 z v v' ∈ T := by
  unfold Hv
  have hvv : v + v' ∈ T := T.add_mem hv hv'
  exact T.sub_mem (T.add_mem (T.add_mem (T.add_mem (T.add_mem (T.mul_mem h1 hz)
    (T.mul_mem h2 (T.pow_mem hz 2))) (T.mul_mem h3 hvv)) (T.mul_mem (T.mul_mem h4 hz) hvv))
    (T.mul_mem h6 (T.add_mem (T.add_mem (T.pow_mem hv 2) (T.mul_mem hv hv')) (T.pow_mem hv' 2)))) T.one_mem
end Formalism.ELL.CubeThreeAlt
