-- Prove2me | solution 1 for Formalism.DivisionValues.conjT_mul_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:15.194912+00:00
-- url     : https://prove2.me/submissions/ece3e482-f469-47f0-a5e2-11bd0260e607

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet
import Theorems.Thm_Formalism_DivisionValues_star_mulVec_dot
import Theorems.Thm_Formalism_DivisionValues_single_dot_single

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (a a' : Fin n) :
    (Aᴴ * N * A) a a' = star (fun i => A i a) ⬝ᵥ (N *ᵥ fun i => A i a') := by
  have hcol : ∀ c, A *ᵥ Pi.single c (1 : ℂ) = fun i => A i c := by
    intro c
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← single_dot_single (Aᴴ * N * A) a a', ← star_mulVec_dot, hcol, hcol]
end Formalism.DivisionValues
