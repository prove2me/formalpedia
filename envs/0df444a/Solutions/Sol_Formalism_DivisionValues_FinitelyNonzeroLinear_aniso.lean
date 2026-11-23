-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.aniso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:41.986808+00:00
-- url     : https://prove2.me/submissions/22799dca-17ef-4d6d-9e23-f078b6830932

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
    {H : Matrix (Fin n) (Fin n) K} (hpos : (H.map v0.embedding).PosDef) (x : Fin n → K)
    (h : star x ⬝ᵥ H *ᵥ x = 0) : x = 0 := by
  have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
  by_contra hx
  have hx' : (fun i => v0.embedding (x i)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    exact v0.embedding.injective (by simpa using congrFun h0 i)
  have hp := hpos.dotProduct_mulVec_pos hx'
  have e : star (fun i => v0.embedding (x i)) ⬝ᵥ (H.map v0.embedding) *ᵥ
      (fun i => v0.embedding (x i)) = v0.embedding (star x ⬝ᵥ H *ᵥ x) := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.star_apply, hv0', Matrix.map_apply,
      starRingEnd_apply]
  rw [e, h, map_zero] at hp
  exact lt_irrefl _ hp
end Formalism.DivisionValues.FinitelyNonzeroLinear
