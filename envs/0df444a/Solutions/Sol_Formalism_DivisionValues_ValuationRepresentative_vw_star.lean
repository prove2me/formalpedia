-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.vw_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:52.348443+00:00
-- url     : https://prove2.me/submissions/f2bc84de-b0ec-4f75-8e87-baadcaa78acd

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_zero
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
namespace ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vw_div (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a / b) = vw w a - vw w b := by
  rw [div_eq_mul_inv, vw_mul w a b⁻¹ ha (inv_ne_zero hb), vw_inv, sub_eq_add_neg]
end ValuationRepresentative
open ValuationRepresentative
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ValuationRepresentative
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (a : K) :
    vw w (star a) = vw (conjPl w) a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have e : ∀ z : 𝓞 K, algebraMap (𝓞 K) K z = (z : K) := fun _ => rfl
  have hy0 : (y : K) ≠ 0 := by
    rw [Ne, ← e, ← map_zero (algebraMap (𝓞 K) K)]
    exact (IsFractionRing.injective (𝓞 K) K).ne (nonZeroDivisors.ne_zero hy)
  rw [e, e]
  by_cases hx0 : (x : K) = 0
  · rw [hx0, zero_div, star_zero, vw_zero, vw_zero]
  · rw [star_div₀, vw_div w _ _ (star_ne_zero.mpr hx0) (star_ne_zero.mpr hy0),
      vw_div _ _ _ hx0 hy0, vw_star_int, vw_star_int]
end Formalism.DivisionValues.ValuationRepresentative
