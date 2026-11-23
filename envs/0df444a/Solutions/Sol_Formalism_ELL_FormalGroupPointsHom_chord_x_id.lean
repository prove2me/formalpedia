-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.chord_x_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:24.248303+00:00
-- url     : https://prove2.me/submissions/bf8210f6-6825-4d2a-850d-105d1b3f3e5d

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_chord_slope

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
variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {z1 z2 w1 w2 c v : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) (hv : v ≠ 0) :
    (c / v - W.addX (z1 / w1) (z2 / w2) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2)))
      * (v * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2) = chordPX W.a₁ W.a₂ z1 z2 w1 w2 c v := by
  rw [chord_slope hw1 hw2 hN, WeierstrassCurve.Affine.addX, chordPX]
  generalize z1 * w2 - z2 * w1 = N at *
  field_simp
  try ring
end Formalism.ELL.FormalGroupPointsHom
