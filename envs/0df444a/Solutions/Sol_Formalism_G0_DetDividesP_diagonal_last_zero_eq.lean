-- Prove2me | solution 1 for Formalism.G0.DetDividesP.diagonal_last_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:23.001986+00:00
-- url     : https://prove2.me/submissions/6708096d-483e-4423-83cc-bee1fb61810c

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_lastIdx_iff

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
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
variable {L : Type} [Field L]
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) :
    Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) =
      1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) (Pi.single (lst hr) 1) := by
  ext a b
  simp only [Matrix.diagonal_apply, lastIdx_iff hr, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, lst]
  split_ifs <;> simp_all
end Formalism.G0.DetDividesP
