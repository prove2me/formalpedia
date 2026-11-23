-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.chord_slope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:48.425804+00:00
-- url     : https://prove2.me/submissions/f52ead65-8016-4d53-9a09-a4aa52bf6a98

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
variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {z1 z2 w1 w2 : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) :
    (-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2) = (w1 - w2) / (z1 * w2 - z2 * w1) := by
  have h : z1 / w1 - z2 / w2 = (z1 * w2 - z2 * w1) / (w1 * w2) := by field_simp
  rw [h]
  field_simp
  ring
end Formalism.ELL.FormalGroupPointsHom
