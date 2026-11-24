-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.L4_arithmetic_square
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:17.427796+00:00
-- url     : https://prove2.me/submissions/439b2198-3413-4562-8c89-32160d473ef0

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pow_two_div_sq_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DetIndexProductInequalitySq := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g e f hP₁ hP₂ hg hi₁ hi₂ hL₁ hL₂ hdet hG₁ hG₂ hgP
  have hq : 0 < g ^ (2 * f * e) := pow_pos hg _
  have hP : 0 < dPs₁ * dPs₂ := mul_pos hP₁ hP₂
  have hc : 0 ≤ (2 / g) ^ (e * f) := pow_nonneg (div_nonneg (by norm_num) hg.le) _
  have ha : 0 ≤ dLa₁ * i₁ ^ 2 := mul_nonneg hL₁ (sq_nonneg _)
  have hb : 0 ≤ dLa₂ * i₂ ^ 2 := mul_nonneg hL₂ (sq_nonneg _)
  have hab : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ G0₁ * G0₂ :=
    mul_le_mul hG₁ hG₂ hb (ha.trans hG₁)
  have hG : 0 ≤ G0₁ * G0₂ := (mul_nonneg ha hb).trans hab
  have hF : 1 ≤ 4 ^ (e * f) * (dPs₁ * dPs₂) / g ^ (2 * f * e) := by
    rw [← mul_assoc]
    first
      | exact (one_le_div hq).2 hgP
      | exact (one_le_div₀ hq).2 hgP
      | exact (le_div_iff₀ hq).2 (by rw [one_mul]; exact hgP)
  have e1 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / (dPs₁ * dPs₂) := by
    rw [show (detM * i₁ * i₂) ^ 2 = detM ^ 2 * i₁ ^ 2 * i₂ ^ 2 by ring, hdet]
    ring
  have hsq : (detM * i₁ * i₂) ^ 2 ≤ ((2 / g) ^ (e * f)) ^ 2 * (G0₁ * G0₂) := by
    rw [pow_two_div_sq_identity g e f, e1]
    have h4 : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤
        4 ^ (e * f) / g ^ (2 * f * e) * (G0₁ * G0₂) * (dPs₁ * dPs₂) :=
      calc (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ G0₁ * G0₂ := hab
        _ ≤ (G0₁ * G0₂) * (4 ^ (e * f) * (dPs₁ * dPs₂) / g ^ (2 * f * e)) :=
          le_mul_of_one_le_right hG hF
        _ = 4 ^ (e * f) / g ^ (2 * f * e) * (G0₁ * G0₂) * (dPs₁ * dPs₂) := by ring
    first
      | exact (div_le_iff₀ hP).2 h4
      | exact (div_le_iff hP).2 h4
  by_cases h : detM ≤ 0
  · have h0 : detM * i₁ * i₂ ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_iff.2 (Or.inr ⟨h, mul_nonneg hi₁ hi₂⟩)
    exact h0.trans (mul_nonneg hc (Real.sqrt_nonneg _))
  · have hL : 0 ≤ detM * i₁ * i₂ := mul_nonneg (mul_nonneg (not_le.mp h).le hi₁) hi₂
    have hs : Real.sqrt ((detM * i₁ * i₂) ^ 2) ≤
        Real.sqrt (((2 / g) ^ (e * f)) ^ 2 * (G0₁ * G0₂)) := by
      first
        | exact Real.sqrt_le_sqrt hsq
        | gcongr
    rw [Real.sqrt_sq hL, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc] at hs
    exact hs
end Formalism.HermitianLatticeCounting.P
