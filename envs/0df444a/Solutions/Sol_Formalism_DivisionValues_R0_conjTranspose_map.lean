-- Prove2me | solution 1 for Formalism.DivisionValues.R0.conjTranspose_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:21.773815+00:00
-- url     : https://prove2.me/submissions/eb1c3381-47fd-48b0-a9f3-db86310d450e

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
theorem _root_.solution (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    {m n : Type} (A : Matrix m n K) : Aᴴ.map σ = (A.map σ)ᴴ := by
  ext i j
  rw [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, Matrix.map_apply, hσ]
  rfl
end Formalism.DivisionValues.R0
