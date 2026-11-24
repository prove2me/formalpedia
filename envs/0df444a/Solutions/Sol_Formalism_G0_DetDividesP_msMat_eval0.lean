-- Prove2me | solution 1 for Formalism.G0.DetDividesP.msMat_eval0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:23.852403+00:00
-- url     : https://prove2.me/submissions/93d732a9-0ca4-4922-98da-8aab022a7c03

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

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
theorem _root_.solution (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom 0) =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) * (g⁻¹ : GL (Fin r) L).1 := by
  unfold msMat
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.diagonal_map (by simp)]
  congr 2
  · ext i j; simp
  · congr 1; funext a; split_ifs <;> simp
  · ext i j; simp
end Formalism.G0.DetDividesP
