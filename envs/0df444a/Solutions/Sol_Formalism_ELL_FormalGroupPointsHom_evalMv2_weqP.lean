-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.evalMv2_weqP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:19.297099+00:00
-- url     : https://prove2.me/submissions/c9f47440-1284-4565-be8b-0275b8156523

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_weqP

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
theorem _root_.solution {a1 a2 a3 a4 a6 s v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv a3) (h4 : IntegralMv a4) (h5 : IntegralMv a6)
    (h6 : IntegralMv s) (h7 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (weqP a1 a2 a3 a4 a6 s v) a b = weqP (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 a3 a b) (evalMv2 a4 a b) (evalMv2 a6 a b) (evalMv2 s a b) (evalMv2 v a b) :=
  map_weqP (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨a3, h3⟩ ⟨a4, h4⟩ ⟨a6, h5⟩ ⟨s, h6⟩ ⟨v, h7⟩
end Formalism.ELL.FormalGroupPointsHom
