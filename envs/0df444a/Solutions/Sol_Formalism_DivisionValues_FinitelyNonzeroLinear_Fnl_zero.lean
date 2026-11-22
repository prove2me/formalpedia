-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.Fnl.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:23.569784+00:00
-- url     : https://prove2.me/submissions/1c7f883d-9dc3-4a03-ae6c-afa31e7c559d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist

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
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
namespace Fnl
theorem _root_.solution (ρ : Fnl j) : ρ.toFun 0 = 0 := by
  simpa using ρ.smul 0 0
end Fnl
end Formalism.DivisionValues.FinitelyNonzeroLinear
