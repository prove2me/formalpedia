-- Prove2me | solution 1 for Formalism.DivisionValues.R0.gramMat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:18.112917+00:00
-- url     : https://prove2.me/submissions/e1485d36-2b8a-4846-8c8a-c147c53e33f4

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef

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
open Formalism.DivisionValues.R0
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.DivisionValues.R0
theorem _root_.solution {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K) (hΓ : Γᴴ = Γ)
    (e : Fin m → Fin D → K) :
    (Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b))ᴴ =
      Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  have h1 : star (star (e j) ⬝ᵥ Γ.mulVec (e i)) = star (e i) ⬝ᵥ Γᴴ.mulVec (e j) := by
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [h1, hΓ]
end Formalism.DivisionValues.R0
