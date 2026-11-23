-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.comm_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:45.104437+00:00
-- url     : https://prove2.me/submissions/2ee540a6-5235-4d6b-a99c-4d255052a4f0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_fnl_mul_left
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_fnl_mul_right
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_eq_of_fnl
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key


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
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) {n : ℕ}
    {𝒯 : Set (Matrix (Fin n) (Fin n) K)} {e : Matrix (Fin n) (Fin n) K}
    (hec : ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → e * B = B * e)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ T ∈ 𝒯, M * T.map j = T.map j * M) :
    e.map j * M = M * e.map j := by
  have hMρ : ∀ ρ : Fnl j, ∀ T ∈ 𝒯, M.map ρ.toFun * T = T * M.map ρ.toFun := fun ρ T hT => by
    rw [← fnl_mul_right, ← fnl_mul_left, hM T hT]
  ext a b
  refine eq_of_fnl j _ _ fun ρ => ?_
  have key : (e.map j * M).map ρ.toFun = (M * e.map j).map ρ.toFun := by
    rw [fnl_mul_left, fnl_mul_right, hec _ (hMρ ρ)]
  have := congrArg (fun X : Matrix (Fin n) (Fin n) K => X a b) key
  exact this
end Formalism.DivisionValues.FinitelyNonzeroLinear
