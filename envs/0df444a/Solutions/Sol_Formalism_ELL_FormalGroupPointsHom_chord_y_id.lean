-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.chord_y_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:24.261851+00:00
-- url     : https://prove2.me/submissions/bf3a7b8b-93af-4148-8b69-6afa707c76a8

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
    (-1 / v - W.negY (c / v) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2) * (c / v - z1 / w1)
      + -1 / w1)) * (v * (z1 * w2 - z2 * w1) * w1) = - chordPY W.a₁ W.a₃ z1 z2 w1 w2 c v := by
  rw [chord_slope hw1 hw2 hN, WeierstrassCurve.Affine.negY, chordPY]
  generalize z1 * w2 - z2 * w1 = N at *
  field_simp
  ring
end Formalism.ELL.FormalGroupPointsHom
