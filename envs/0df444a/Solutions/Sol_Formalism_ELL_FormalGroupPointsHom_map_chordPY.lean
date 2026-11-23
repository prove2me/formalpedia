-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.map_chordPY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:04.206555+00:00
-- url     : https://prove2.me/submissions/90109962-9035-4977-9893-31507f11e0ca

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution (a1 a3 z1 z2 w1 w2 c v : R) :
    f (chordPY a1 a3 z1 z2 w1 w2 c v) = chordPY (f a1) (f a3) (f z1) (f z2) (f w1) (f w2) (f c) (f v) := by
  simp only [chordPY, map_sub, map_add, map_mul, map_pow]
end Formalism.ELL.FormalGroupPointsHom
