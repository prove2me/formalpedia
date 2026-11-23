-- Prove2me | solution 1 for Formalism.DivisionValues.frobenius_norm_rational
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:21.394866+00:00
-- url     : https://prove2.me/submissions/f6b6e4ed-c320-47cd-ab1e-7b25aac6cf4e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_star_dot_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : FnormRat := by
  unfold FnormRat
  intro K _ _ _ n X v x y
  have hx : (fun i => v.embedding (x i)) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v x := by
    funext i
    show v.embedding (x i) = v.embedding ((Pi.basisFun K (Fin n)).repr x i)
    rw [Pi.basisFun_repr]
  have hy : (fun i => v.embedding (y i)) = Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v y := by
    funext i
    show v.embedding (y i) = v.embedding ((Pi.basisFun K (Fin n)).repr y i)
    rw [Pi.basisFun_repr]
  refine ⟨?_, ?_, ?_⟩
  · simp only [fnorm, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hx]
  · simp only [fmaj, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hx, hy]
  · simp only [fnorm, fmaj]
    rw [← star_dot_self]
    rfl
end Formalism.DivisionValues
