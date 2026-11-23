-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.herm_of_hermAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:25.214184+00:00
-- url     : https://prove2.me/submissions/84b4bea9-8539-48fe-8390-d0d6fb635357

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral

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
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
open StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ConjugateWeightGram
theorem _root_.solution {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ}
    (hR : IsHermAt v0 H X) (i j : Fin n) : H j i = star (H i j) := by
  have h1 := hR.2
  have h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding := by
    rw [← h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h3 := congrFun (congrFun h2 j) i
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h3
  apply v0.embedding.injective
  rw [hv0, ← h3, starRingEnd_apply]
end Formalism.DivisionValues.ConjugateWeightGram
