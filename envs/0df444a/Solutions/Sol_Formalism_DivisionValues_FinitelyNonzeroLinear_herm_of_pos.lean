-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.herm_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:30.711574+00:00
-- url     : https://prove2.me/submissions/73c83058-2429-4de3-99e0-59062aaac786

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef) : Hᴴ = H := by
  ext i k
  apply v0.embedding.injective
  rw [Matrix.conjTranspose_apply, hv0 (H k i), starRingEnd_apply]
  exact hpos.isHermitian.apply i k
end Formalism.DivisionValues.FinitelyNonzeroLinear
