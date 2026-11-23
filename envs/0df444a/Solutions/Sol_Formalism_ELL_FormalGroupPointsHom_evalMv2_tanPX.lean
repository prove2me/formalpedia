-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.evalMv2_tanPX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:38.969007+00:00
-- url     : https://prove2.me/submissions/55c27d9c-d3c5-40a6-be4e-f1a3653a5aa7

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_tanPX

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
theorem _root_.solution {a1 a2 a3 a4 z w c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv a3) (h4 : IntegralMv a4) (h5 : IntegralMv z)
    (h6 : IntegralMv w) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (tanPX a1 a2 a3 a4 z w c v) a b = tanPX (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 a3 a b) (evalMv2 a4 a b) (evalMv2 z a b) (evalMv2 w a b) (evalMv2 c a b)
      (evalMv2 v a b) :=
  map_tanPX (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨a3, h3⟩ ⟨a4, h4⟩ ⟨z, h5⟩ ⟨w, h6⟩ ⟨c, h7⟩ ⟨v, h8⟩
end Formalism.ELL.FormalGroupPointsHom
