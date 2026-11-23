-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.det_ne_of_hermAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:18.881431+00:00
-- url     : https://prove2.me/submissions/c61f3c52-ddc6-474f-9968-a00740cdc41c

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
theorem _root_.solution {v0 : InfinitePlace K} {n : ℕ}
    {H : Matrix (Fin n) (Fin n) K} {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ}
    (hR : IsHermAt v0 H X) : H.det ≠ 0 := by
  intro h0
  have h1 : v0.embedding H.det = star ((X v0)⁻¹.det) * (X v0)⁻¹.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hR.2, Matrix.det_mul,
      Matrix.det_conjTranspose]
  rw [h0, map_zero] at h1
  have hz : (X v0)⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ (hR.1 v0)).ne_zero
  exact mul_ne_zero (star_ne_zero.mpr hz) hz h1.symm
end Formalism.DivisionValues.ConjugateWeightGram
