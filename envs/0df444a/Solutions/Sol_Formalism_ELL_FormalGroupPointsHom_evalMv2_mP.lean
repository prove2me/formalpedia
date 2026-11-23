-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.evalMv2_mP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:49.487874+00:00
-- url     : https://prove2.me/submissions/563f3af8-df3b-493a-a093-4bf728e0f8a2

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_mP

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {a1 a3 z w : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a3) (h3 : IntegralMv z) (h4 : IntegralMv w) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (mP a1 a3 z w) a b = mP (evalMv2 a1 a b) (evalMv2 a3 a b) (evalMv2 z a b) (evalMv2 w a b) :=
  map_mP (ev a b ha hb) ⟨a1, h1⟩ ⟨a3, h2⟩ ⟨z, h3⟩ ⟨w, h4⟩
end Formalism.ELL.FormalGroupPointsHom
