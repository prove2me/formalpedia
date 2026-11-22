-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.ext_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:35:54.393837+00:00
-- url     : https://prove2.me/submissions/52e0196b-45a9-44db-9390-19780632520e

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
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {R : Type} [CommRing R] {m n : ℕ} {A A' : Matrix (Fin m) (Fin n) R}
    (h : ∀ x, A *ᵥ x = A' *ᵥ x) : A = A' := by
  ext i k
  have := congrFun (h (Pi.single k 1)) i
  simpa [Matrix.mulVec_single_one] using this
end Formalism.DivisionValues.FinitelyNonzeroLinear
