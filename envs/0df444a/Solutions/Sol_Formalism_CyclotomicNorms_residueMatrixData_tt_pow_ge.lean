-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.tt_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:21.777826+00:00
-- url     : https://prove2.me/submissions/8d7becfa-508f-46a4-9f43-2105ea5c88ef

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_n

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)
namespace Formalism.CyclotomicNorms.residueMatrixData
theorem _root_.solution {m : ℕ} (hm : n ≤ m) : (TT) ^ m = 0 := by
  rw [← Nat.add_sub_cancel' hm, pow_add, tt_pow_n, zero_mul]
end Formalism.CyclotomicNorms.residueMatrixData
