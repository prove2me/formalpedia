-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.line_fact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:26.696173+00:00
-- url     : https://prove2.me/submissions/ea74183e-10e0-4b21-af72-d14357be8277

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_G_line
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_vieta


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
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution [IsDomain R] {a1 a2 a3 a4 a6 l n a b z : R} (hab : a ≠ b)
    (ha : G a1 a2 a3 a4 a6 a (l * a + n) = 0) (hb : G a1 a2 a3 a4 a6 b (l * b + n) = 0)
    (he1 : c3 a2 a4 a6 l * (a + b + z) + c2 a1 a2 a3 a4 a6 l n = 0) (c : R) :
    G a1 a2 a3 a4 a6 c (l * c + n) = c3 a2 a4 a6 l * (c - a) * (c - b) * (c - z) := by
  obtain ⟨-, h2, h3⟩ := Formalism.ELL.WeierstrassChordSeries.vieta hab ha hb he1
  rw [Formalism.ELL.WeierstrassChordSeries.G_line]
  linear_combination c ^ 2 * he1 - c * h2 + h3
end Formalism.ELL.CubeThreeAlt
