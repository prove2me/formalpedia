-- Prove2me | solution 1 for Formalism.CountingSumsFrames.whc_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:48.172115+00:00
-- url     : https://prove2.me/submissions/342729b7-581b-4017-9034-9623290e6cfc

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ M M' : Type} [AddCommMonoid M] [AddCommMonoid M'] (w : σ → M) (w' : σ → M') (ν : M')
    (D : M) {x : MvPolynomial σ ℚ_[p]} (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    weightedHomogeneousComponent w' ν x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by
  classical
  rw [mem_weightedHomogeneousSubmodule] at hx ⊢
  intro m hm
  rw [coeff_weightedHomogeneousComponent] at hm
  split_ifs at hm
  · exact hx hm
  · exact absurd rfl hm
end Formalism.CountingSumsFrames
