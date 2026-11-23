-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:42.042072+00:00
-- url     : https://prove2.me/submissions/0bfe1762-6e87-4b9d-9837-13a38c5fbce4

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule

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
theorem _root_.solution {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) :
    P.det * Φ.det * Q.det = (TT) ^ (∑ i, k i) := by
  rw [← det_mul, ← det_mul, hD, det_diagonal, Finset.prod_pow_eq_pow_sum]
end Formalism.CyclotomicNorms.residueMatrixData
