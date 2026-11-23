-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.exists_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:15.438995+00:00
-- url     : https://prove2.me/submissions/b57d3e1c-1ca6-4a33-8b3e-31e7cbab1c7a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_exists_left_inv
import Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_exists_frame

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
theorem _root_.solution {K0 : Subfield K} {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hH : IsRatHerm K0 H X)
    (z : Fin d → Fin n → K) (hzli : LinearIndependent K z) :
    ∃ XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, ∀ v, IsUnit (XT v).det ∧
      ((XT v)⁻¹)ᴴ * (XT v)⁻¹ =
        ((colMat z).map v.embedding)ᴴ * (H.map v.embedding) * (colMat z).map v.embedding := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv z hzli
  have hinj : ∀ v : InfinitePlace K, Function.Injective ((colMat z).map v.embedding).mulVec := by
    intro v x y hxy
    have h1 : (L.map v.embedding) * (colMat z).map v.embedding = 1 := by
      rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
    have := congrArg (L.map v.embedding).mulVec hxy
    simpa [Matrix.mulVec_mulVec, h1] using this
  have hHpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef := by
    intro v
    rw [← (hH.2 v).2]
    apply Matrix.PosDef.conjTranspose_mul_self
    exact Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ (hH.2 v).1))
  choose XT hXT1 hXT2 using fun v =>
    exists_frame _ ((hHpos v).conjTranspose_mul_mul_same (hinj v))
  exact ⟨XT, fun v => ⟨hXT1 v, hXT2 v⟩⟩
end Formalism.DivisionValues.ConjugateWeightGram
