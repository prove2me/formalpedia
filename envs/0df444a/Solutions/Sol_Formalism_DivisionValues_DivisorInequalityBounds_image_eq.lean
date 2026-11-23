-- Prove2me | solution 1 for Formalism.DivisionValues.DivisorInequalityBounds.image_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:23.62808+00:00
-- url     : https://prove2.me/submissions/bb0c3239-5a34-453c-bee9-4d0984e8311c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DivisorInequalityBounds
namespace Formalism.DivisionValues.DivisorInequalityBounds
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (e : Matrix (Fin n) (Fin n) K) (hee : e * e = e)
    (hcomm : ∀ T ∈ 𝒯, e * T = T * e) (χ : Matrix (Fin n) (Fin n) K → Ω) :
    (simEig j 𝒯 χ).map (e.map j).mulVecLin = simEig j 𝒯 χ ⊓ simEig j {e} (fun _ => 1) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · intro T hT
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← hcomm T hT, Matrix.map_mul,
        ← Matrix.mulVec_mulVec, hx T hT, Matrix.mulVec_smul]
    · intro T hT
      rw [Set.mem_singleton_iff.mp hT, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul,
        hee, one_smul]
  · rintro x ⟨hx, hx1⟩
    refine ⟨x, hx, ?_⟩
    rw [Matrix.mulVecLin_apply, hx1 e rfl, one_smul]
end Formalism.DivisionValues.DivisorInequalityBounds
