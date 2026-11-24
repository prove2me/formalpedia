-- Prove2me | solution 1 for Formalism.G0.DetDividesP.det_msMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.716014+00:00
-- url     : https://prove2.me/submissions/3952916c-efe2-4cd0-b260-50ef13829c21

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_prod_lastX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) (g : GL (Fin r) L) : (msMat g).det = X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_lastX hr]
  have h1 : (g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul]
    simp
  calc (g.1.map C).det * X * (((g⁻¹ : GL (Fin r) L)).1.map C).det
      = ((g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det) * X := by ring
    _ = X := by rw [h1, one_mul]
end Formalism.G0.DetDividesP
