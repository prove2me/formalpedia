-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.fnl_extSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:39.525806+00:00
-- url     : https://prove2.me/submissions/1b16699d-9728-445a-9286-115c914aadc9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_Fnl_zero

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
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {n : ℕ} (Z : Submodule K (Fin n → K)) (y : Fin n → Ω)
    (hy : y ∈ extSpan j Z) : ∀ ρ : Fnl j, (fun i => ρ.toFun (y i)) ∈ Z := by
  unfold extSpan at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    intro ρ
    have e : (fun i => ρ.toFun (j (z i))) = ρ.toFun 1 • z := by
      funext i
      have h := ρ.smul (z i) 1
      rw [mul_one] at h
      rw [h, Pi.smul_apply, smul_eq_mul, mul_comm]
    show (fun i => ρ.toFun (j (z i))) ∈ Z
    rw [e]
    exact Z.smul_mem _ hz
  | zero =>
    intro ρ
    show (fun _ => ρ.toFun 0) ∈ Z
    rw [ρ.zero]
    exact Z.zero_mem
  | add x y _ _ hx hy =>
    intro ρ
    have h := Z.add_mem (hx ρ) (hy ρ)
    convert h using 1
    funext i
    exact ρ.add _ _
  | smul c x _ hx =>
    intro ρ
    exact hx ⟨fun t => ρ.toFun (c * t),
      fun t t' => by
        show ρ.toFun (c * (t + t')) = ρ.toFun (c * t) + ρ.toFun (c * t')
        rw [mul_add, ρ.add],
      fun a t => by
        show ρ.toFun (c * (j a * t)) = a * ρ.toFun (c * t)
        rw [mul_left_comm, ρ.smul]⟩
end Formalism.DivisionValues.FinitelyNonzeroLinear
