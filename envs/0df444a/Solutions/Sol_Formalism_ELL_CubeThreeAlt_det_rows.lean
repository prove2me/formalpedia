-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.det_rows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:06.498663+00:00
-- url     : https://prove2.me/submissions/3d41b4ac-ca47-4da3-b3a2-37d6823bc018

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree

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
theorem _root_.solution (t V ww : Fin 3 → R) (h : ∀ i, t i ^ 3 = V i * ww i) :
    (Matrix.of fun i => ![t i ^ 3, t i * V i, -V i]).det
      = -(V 0 * V 1 * V 2) * ((ww 1 - ww 0) * (t 2 - t 0) - (ww 2 - ww 0) * (t 1 - t 0)) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  linear_combination (V 1 * V 2 * (t 2 - t 1)) * h 0 + (V 0 * V 2 * (t 0 - t 2)) * h 1
    + (V 0 * V 1 * (t 1 - t 0)) * h 2
end Formalism.ELL.CubeThreeAlt
