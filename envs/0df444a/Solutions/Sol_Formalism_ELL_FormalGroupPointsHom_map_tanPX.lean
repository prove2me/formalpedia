-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.map_tanPX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:04.162193+00:00
-- url     : https://prove2.me/submissions/9a737d70-c825-4fa0-b1d0-2ee32cdc80de

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
theorem _root_.solution (a1 a2 a3 a4 z w c v : R) :
    f (tanPX a1 a2 a3 a4 z w c v) = tanPX (f a1) (f a2) (f a3) (f a4) (f z) (f w) (f c) (f v) := by
  simp only [tanPX, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
end Formalism.ELL.FormalGroupPointsHom
