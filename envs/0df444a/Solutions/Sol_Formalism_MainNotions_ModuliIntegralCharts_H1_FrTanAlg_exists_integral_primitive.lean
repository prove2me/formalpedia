-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg.exists_integral_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:59.490245+00:00
-- url     : https://prove2.me/submissions/2743c4e0-7936-489c-a0ad-c407dd07c5bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrTanAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
open Polynomial NumberField
variable (E : Type) [Field E] [NumberField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
theorem _root_.solution : ∃ θ : 𝓞 E, IntermediateField.adjoin ℚ {(θ : E)} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) α
    (Algebra.IsIntegral.isIntegral (R := ℚ) α)
  have hm0 : (((m : ℤ) : E)) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero m.prop)
  refine ⟨⟨(m : ℤ) • α, hm⟩, ?_⟩
  refine le_antisymm le_top ?_
  rw [← hα, IntermediateField.adjoin_le_iff]
  have h1 : (m : ℤ) • α ∈ IntermediateField.adjoin ℚ {(m : ℤ) • α} :=
    IntermediateField.mem_adjoin_simple_self ℚ _
  have h2 : α = (((m : ℤ) : ℚ))⁻¹ • ((m : ℤ) • α) := by
    rw [zsmul_eq_mul, Algebra.smul_def, map_inv₀, map_intCast, inv_mul_cancel_left₀ hm0]
  have h3 := SMulMemClass.smul_mem (((m : ℤ) : ℚ))⁻¹ h1
  rw [← h2] at h3
  exact Set.singleton_subset_iff.mpr h3
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanAlg
