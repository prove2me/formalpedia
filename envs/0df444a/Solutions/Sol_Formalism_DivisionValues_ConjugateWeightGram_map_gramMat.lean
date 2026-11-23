-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.map_gramMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:26.064722+00:00
-- url     : https://prove2.me/submissions/a6a0b006-5db6-4e4f-87ea-d7ae31b412da

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_gramMat_eq

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
theorem _root_.solution {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (z : Fin d → Fin n → K) (σ : K →+* ℂ)
    (hz : ∀ a i, σ (star (z a i)) = starRingEnd ℂ (σ (z a i))) :
    (gramMat H z).map σ = ((colMat z).map σ)ᴴ * (H.map σ) * (colMat z).map σ := by
  have hT : ((colMat z)ᴴ).map σ = ((colMat z).map σ)ᴴ := by
    ext a i
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply, colMat, Matrix.of_apply]
    rw [hz a i]
    rfl
  rw [gramMat_eq, Matrix.map_mul, Matrix.map_mul, hT]
end Formalism.DivisionValues.ConjugateWeightGram
