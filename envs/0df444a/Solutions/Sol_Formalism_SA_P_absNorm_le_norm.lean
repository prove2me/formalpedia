-- Prove2me | solution 1 for Formalism.SA.P.absNorm_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:48.973133+00:00
-- url     : https://prove2.me/submissions/8c717664-26fc-4cf0-b760-0fa0242c3344

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
namespace Formalism.SA.P
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by
  have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem]; exact hl
  set c := b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l with hc
  have hbc : b * c = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l := by
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have hc1 : c ≤ 1 := by
    have h1 : c ≤ b⁻¹ * b := by
      first
        | exact mul_le_mul_right hs _
        | (rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
           exact Submodule.mul_le_mul_right (FractionalIdeal.coe_le_coe.mpr hs))
    rwa [inv_mul_cancel₀ hb] at h1
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hc1
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hbc
    exact hl0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp hbc.symm)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hc0
    rw [← hI]
    exact FractionalIdeal.coeIdeal_eq_zero.mpr rfl
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm c := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have key : FractionalIdeal.absNorm b * FractionalIdeal.absNorm c = |Algebra.norm ℚ l| := by
    rw [← map_mul, hbc, FractionalIdeal.absNorm_span_singleton (𝓞 E)]
  have h0 := FractionalIdeal.absNorm_nonneg b
  have hq : FractionalIdeal.absNorm b ≤ |Algebra.norm ℚ l| := by
    rw [← key]; nlinarith
  have hr : ((FractionalIdeal.absNorm b : ℚ) : ℝ) ≤ ((|Algebra.norm ℚ l| : ℚ) : ℝ) := by
    exact_mod_cast hq
  rwa [Rat.cast_abs] at hr
end Formalism.SA.P
