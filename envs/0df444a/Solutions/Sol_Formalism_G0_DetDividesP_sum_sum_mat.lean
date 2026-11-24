-- Prove2me | solution 1 for Formalism.G0.DetDividesP.sum_sum_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:25.927039+00:00
-- url     : https://prove2.me/submissions/ca44d5bf-4c57-4f02-81ce-47bc1007b38c

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
theorem _root_.solution {R : Type} [CommSemiring R] (M N : Matrix (Fin r) (Fin r) R) (v : Fin r → R) (a : Fin r) :
    (∑ b, M a b * ∑ c, N b c * v c) = ∑ c, (M * N) a c * v c := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
end Formalism.G0.DetDividesP
