-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.eq_of_fnl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:15.887862+00:00
-- url     : https://prove2.me/submissions/3841d72f-0dad-496d-83f3-639d755ead58

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_eq_zero_of_fnl

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
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω) (c c' : Ω)
    (h : ∀ ρ : Fnl j, ρ.toFun c = ρ.toFun c') : c = c' := by
  have h0 := eq_zero_of_fnl j (c - c') fun ρ => by
    have h1 := ρ.add (c - c') c'
    rw [sub_add_cancel, h ρ] at h1
    simpa using h1
  exact sub_eq_zero.mp h0
end Formalism.DivisionValues.FinitelyNonzeroLinear
