-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.gramR_eq_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:11.700528+00:00
-- url     : https://prove2.me/submissions/16460134-933a-4b1d-9e46-481acea94e88

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RationalHermitianForm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.RationalHermitianForm
theorem _root_.solution {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (f : Fin d → Fin d → K) :
    gramR H f = star (Matrix.of f)ᵀ.det * (Matrix.of f)ᵀ.det * H.det := by
  unfold gramR
  have h1 : (Matrix.of fun a b => star (f a) ⬝ᵥ H.mulVec (f b)) =
      ((Matrix.of f)ᵀ)ᴴ * H * (Matrix.of f)ᵀ := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    first
      | rfl
      | exact Finset.sum_comm
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  ring
end Formalism.DivisionValues.RationalHermitianForm
