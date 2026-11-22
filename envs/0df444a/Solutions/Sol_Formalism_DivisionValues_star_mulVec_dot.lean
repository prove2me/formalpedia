-- Prove2me | solution 1 for Formalism.DivisionValues.star_mulVec_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:13.528645+00:00
-- url     : https://prove2.me/submissions/fdcac409-124a-4e16-93d6-3207144fbf31

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SpecDet

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
theorem _root_.solution {d : ℕ} (A N : Matrix (Fin d) (Fin d) ℂ) (u w : Fin d → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (N *ᵥ (A *ᵥ w)) = star u ⬝ᵥ ((Aᴴ * N * A) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
end Formalism.DivisionValues
