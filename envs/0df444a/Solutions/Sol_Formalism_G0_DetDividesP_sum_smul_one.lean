-- Prove2me | solution 1 for Formalism.G0.DetDividesP.sum_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:25.051803+00:00
-- url     : https://prove2.me/submissions/439a3b70-bfe8-4bbb-ba0d-904a9a51326e

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
theorem _root_.solution {R : Type} [CommSemiring R] (t : R) (v : Fin r → R) (a : Fin r) :
    (∑ c, ((t • (1 : Matrix (Fin r) (Fin r) R)) a c) * v c) = t * v a := by
  simp [Matrix.smul_apply, Matrix.one_apply]
end Formalism.G0.DetDividesP
