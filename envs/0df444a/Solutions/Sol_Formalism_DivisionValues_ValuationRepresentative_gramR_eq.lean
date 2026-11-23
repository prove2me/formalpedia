-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.gramR_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:41.599655+00:00
-- url     : https://prove2.me/submissions/8efec60e-acd9-4b82-a80a-53f298ceb1cd

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ValuationRepresentative
theorem _root_.solution {K : Type} [Field K] [StarRing K] {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) :
    gramR Γ e = ((Matrix.of e).map star * Γ * (Matrix.of e).transpose).det := by
  unfold gramR
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end Formalism.DivisionValues.ValuationRepresentative
