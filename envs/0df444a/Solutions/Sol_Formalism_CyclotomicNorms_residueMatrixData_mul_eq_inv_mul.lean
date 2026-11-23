-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residueMatrixData.mul_eq_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:42.88593+00:00
-- url     : https://prove2.me/submissions/89fadafb-1536-4e11-bf18-165327f4c75d

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
theorem _root_.solution {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (hP : IsUnit P.det) :
    Φ * Q = P⁻¹ * (P * Φ * Q) := by
  rw [Matrix.mul_assoc P, ← Matrix.mul_assoc P⁻¹, nonsing_inv_mul _ hP, Matrix.one_mul]
end Formalism.CyclotomicNorms.residueMatrixData
