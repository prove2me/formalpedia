-- Prove2me | solution 1 for Formalism.DivisionValues.cv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:46.607429+00:00
-- url     : https://prove2.me/submissions/e437f63b-f662-467d-a9e6-72a4275f164f

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
theorem _root_.solution {d : ℕ} (σ : K →+* ℂ) (φ : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    cv σ (φ *ᵥ x) = (φ.map σ) *ᵥ cv σ x := by
  ext i
  exact RingHom.map_mulVec σ φ x i
end Formalism.DivisionValues
