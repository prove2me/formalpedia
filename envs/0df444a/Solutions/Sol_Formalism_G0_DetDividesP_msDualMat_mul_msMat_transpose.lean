-- Prove2me | solution 1 for Formalism.G0.DetDividesP.msDualMat_mul_msMat_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:41.714747+00:00
-- url     : https://prove2.me/submissions/4f6cac64-9791-49b7-8d84-24809faaed12

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_msMat_mul_nMat
import Theorems.Thm_Formalism_G0_DetDividesP_msDualMat_eq

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
    msDualMat g * (msMat g).transpose = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
  rw [msDualMat_eq, ← Matrix.transpose_mul, msMat_mul_nMat]; simp
end Formalism.G0.DetDividesP
