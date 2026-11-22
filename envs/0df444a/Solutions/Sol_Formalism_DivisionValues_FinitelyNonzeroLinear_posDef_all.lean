-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.posDef_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:06.482158+00:00
-- url     : https://prove2.me/submissions/30e9240c-cda8-46b7-bccf-87f8a1e2d726

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
theorem _root_.solution {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    (hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef) (σ : K →+* ℂ) :
    (H.map σ).PosDef := by
  obtain he | he := InfinitePlace.embedding_mk_eq σ
  · simpa [he] using hpos (InfinitePlace.mk σ)
  · have hP := hpos (InfinitePlace.mk σ)
    rw [he] at hP
    have e : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i k
      rw [Matrix.transpose_apply, ← hP.isHermitian.apply k i]
      simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e]
    exact hP.transpose
end Formalism.DivisionValues.FinitelyNonzeroLinear
