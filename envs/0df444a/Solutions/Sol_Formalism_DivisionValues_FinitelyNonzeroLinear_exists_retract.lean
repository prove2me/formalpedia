-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.exists_retract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:39.3248+00:00
-- url     : https://prove2.me/submissions/afdf9e95-de6e-4cc9-9d58-7b2cda9ae228

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
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace FinitelyNonzeroLinear
section Ext
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
private theorem exists_fnl_apply_eq_one_of_ne_zero (c : Ω) (hc : c ≠ 0) : ∃ ρ : Fnl j, ρ.toFun c = 1 := by
  letI : Algebra K Ω := j.toAlgebra
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K Ω, φ c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hc ((Module.forall_dual_apply_eq_zero_iff K c).1 h)
  refine ⟨⟨fun x => (φ c)⁻¹ * φ x, fun x y => by simp only [map_add, mul_add], fun a x => ?_⟩, ?_⟩
  · show (φ c)⁻¹ * φ (j a * x) = a * ((φ c)⁻¹ * φ x)
    rw [show j a * x = a • x from (Algebra.smul_def a x).symm, map_smul, smul_eq_mul]
    ring
  · show (φ c)⁻¹ * φ c = 1
    exact inv_mul_cancel₀ hφ
end Ext
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Herm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Herm
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Cx
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
end Cx
section Diag
variable {K : Type} [Field K] {n : ℕ}
end Diag
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Dich
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
end Dich
end FinitelyNonzeroLinear
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
variable (j)
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution : ∃ ρ : Fnl j, ∀ a, ρ.toFun (j a) = a := by
  obtain ⟨ρ, hρ⟩ := exists_fnl_apply_eq_one_of_ne_zero (j := j) (1 : Ω) one_ne_zero
  refine ⟨ρ, fun a => ?_⟩
  have h := ρ.smul a 1
  rw [mul_one, hρ, mul_one] at h
  exact h
end Formalism.DivisionValues.FinitelyNonzeroLinear
