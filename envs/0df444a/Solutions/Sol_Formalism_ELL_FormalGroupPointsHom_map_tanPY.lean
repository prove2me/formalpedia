-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.map_tanPY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:04.796465+00:00
-- url     : https://prove2.me/submissions/9f005100-f484-4d66-8215-789413949d40

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
    f (tanPY a1 a2 a3 a4 z w c v) = tanPY (f a1) (f a2) (f a3) (f a4) (f z) (f w) (f c) (f v) := by
  simp only [tanPY, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
end Formalism.ELL.FormalGroupPointsHom
