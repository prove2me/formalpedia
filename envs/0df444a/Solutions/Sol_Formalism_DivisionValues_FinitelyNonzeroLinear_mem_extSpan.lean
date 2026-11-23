-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.mem_extSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:59.680176+00:00
-- url     : https://prove2.me/submissions/91fa077e-345c-4f37-9621-a59d4d62ff02

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
theorem _root_.solution {n : ℕ} {Z : Submodule K (Fin n → K)} {z : Fin n → K} (hz : z ∈ Z) :
    (fun i => j (z i)) ∈ extSpan j Z := by
  unfold extSpan
  exact Submodule.subset_span ⟨z, hz, rfl⟩
end Formalism.DivisionValues.FinitelyNonzeroLinear
