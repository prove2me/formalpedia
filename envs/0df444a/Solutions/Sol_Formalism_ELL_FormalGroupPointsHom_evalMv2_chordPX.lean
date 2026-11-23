-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.evalMv2_chordPX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:49.426506+00:00
-- url     : https://prove2.me/submissions/e7f4d1b5-4b71-4c6a-8910-7f2a0e37cdcc

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_map_chordPX

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
theorem _root_.solution {a1 a2 z1 z2 w1 w2 c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a2) (h3 : IntegralMv z1) (h4 : IntegralMv z2) (h5 : IntegralMv w1)
    (h6 : IntegralMv w2) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (chordPX a1 a2 z1 z2 w1 w2 c v) a b = chordPX (evalMv2 a1 a b) (evalMv2 a2 a b)
      (evalMv2 z1 a b) (evalMv2 z2 a b) (evalMv2 w1 a b) (evalMv2 w2 a b) (evalMv2 c a b)
      (evalMv2 v a b) :=
  map_chordPX (ev a b ha hb) ⟨a1, h1⟩ ⟨a2, h2⟩ ⟨z1, h3⟩ ⟨z2, h4⟩ ⟨w1, h5⟩ ⟨w2, h6⟩ ⟨c, h7⟩ ⟨v, h8⟩
end Formalism.ELL.FormalGroupPointsHom
