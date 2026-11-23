-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.Fnl.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:59.661743+00:00
-- url     : https://prove2.me/submissions/2d687ac8-e1aa-4822-80ff-90d179b1ebba

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_Fnl_zero

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
theorem _root_.solution (ρ : Fnl j) {ι : Type} (s : Finset ι) (f : ι → Ω) :
    ρ.toFun (∑ i ∈ s, f i) = ∑ i ∈ s, ρ.toFun (f i) := by
  exact map_sum ({ toFun := ρ.toFun, map_zero' := ρ.zero, map_add' := ρ.add } : Ω →+ K) f s
end Fnl
end Formalism.DivisionValues.FinitelyNonzeroLinear
