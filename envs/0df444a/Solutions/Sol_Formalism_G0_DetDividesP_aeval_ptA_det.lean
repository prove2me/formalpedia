-- Prove2me | solution 1 for Formalism.G0.DetDividesP.aeval_ptA_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:27.511948+00:00
-- url     : https://prove2.me/submissions/b3b1837a-1368-439c-b943-c25ae206adb1

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_det_msMat
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_detLetters

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
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) {L : Type} [Field L] [Algebra K L] (A : Fin r → ι) (g : GL (Fin r) L)
    (x : ι × Fin r → L) :
    MvPolynomial.aeval (ptA A g x) (detLetters (K := K) A) =
      C (MvPolynomial.aeval x (detLetters (K := K) A)) * X := by
  rw [aeval_detLetters, aeval_detLetters]
  have : (Matrix.of fun l a => ptA A g x (A l, a)) =
      ((Matrix.of fun l b => x (A l, b)).map C) * (msMat g).transpose := by
    ext l a
    simp [ptA, Matrix.mul_apply, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, det_msMat hr, RingHom.map_det]
  rfl
end Formalism.G0.DetDividesP
