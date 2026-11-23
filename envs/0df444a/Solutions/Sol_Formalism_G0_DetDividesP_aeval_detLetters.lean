-- Prove2me | solution 1 for Formalism.G0.DetDividesP.aeval_detLetters
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.264979+00:00
-- url     : https://prove2.me/submissions/7a4290a7-436e-47f3-8b2f-2f364b939d2b

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
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {B : Type} [CommRing B] [Algebra K B] (A : Fin r → ι) (y : ι × Fin r → B) :
    MvPolynomial.aeval y (detLetters (K := K) A) = (Matrix.of fun l a => y (A l, a)).det := by
  unfold detLetters
  rw [AlgHom.map_det]; congr 1; ext l a; simp
end Formalism.G0.DetDividesP
