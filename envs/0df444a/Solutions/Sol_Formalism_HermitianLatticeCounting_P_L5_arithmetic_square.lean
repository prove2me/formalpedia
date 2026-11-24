-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.L5_arithmetic_square
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:17.680111+00:00
-- url     : https://prove2.me/submissions/72d7d80c-0a8b-40a1-8e0e-5e73d0dfc40f

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
theorem _root_.solution : DetIndexProductPlacesInequalitySq := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f
    hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hdet hd₁ hd₂ hG₁ hG₂ hT₁ hT₂ hgQ
  have hq : 0 < g ^ (2 * f * e) := pow_pos hg _
  have hc : 0 ≤ (2 / g) ^ (e * f) := pow_nonneg (div_nonneg (by norm_num) hg.le) _
  have ha : 0 ≤ dLa₁ * i₁ ^ 2 := mul_nonneg hL₁ (sq_nonneg _)
  have hb : 0 ≤ dLa₂ * i₂ ^ 2 := mul_nonneg hL₂ (sq_nonneg _)
  have hA : dLa₁ * i₁ ^ 2 * Nr₁ ≤ G0₁ := by
    have h := mul_le_mul_of_nonneg_right hG₁ hN₁.le
    rwa [div_mul_cancel₀ _ hN₁.ne'] at h
  have hB : dLa₂ * i₂ ^ 2 * Nr₂ ≤ G0₂ := by
    have h := mul_le_mul_of_nonneg_right hG₂ hN₂.le
    rwa [div_mul_cancel₀ _ hN₂.ne'] at h
  have hk₂ : 0 < Nr₂ * K₂ ^ 2 := mul_pos hN₂ (pow_pos hK₂ 2)
  have hk₁ : 0 < Nr₁ * K₁ ^ 2 := mul_pos hN₁ (pow_pos hK₁ 2)
  have hp1 : NT ≤ P₁ * (Nr₂ * K₂ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hT₁ hk₂.le
    rwa [div_mul_cancel₀ _ hk₂.ne'] at h
  have hp2 : NT ≤ P₂ * (Nr₁ * K₁ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hT₂ hk₁.le
    rwa [div_mul_cancel₀ _ hk₁.ne'] at h
  have hG1 : 0 ≤ G0₁ := le_trans (mul_nonneg ha hN₁.le) hA
  have hG2 : 0 ≤ G0₂ := le_trans (mul_nonneg hb hN₂.le) hB
  have hG : 0 ≤ G0₁ * G0₂ := mul_nonneg hG1 hG2
  have hPP : 0 < P₁ * P₂ := mul_pos hP₁ hP₂
  have hF : 1 ≤ 4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e) := by
    rw [← mul_assoc]
    first
      | exact (one_le_div hq).2 hgQ
      | exact (one_le_div₀ hq).2 hgQ
  have hNN : NT * NT ≤ (P₁ * (Nr₂ * K₂ ^ 2)) * (P₂ * (Nr₁ * K₁ ^ 2)) :=
    mul_le_mul hp1 hp2 hNT.le (le_trans hNT.le hp1)
  have key : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * (NT * NT) ≤
      (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e)) := by
    calc (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * (NT * NT)
        ≤ (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * ((P₁ * (Nr₂ * K₂ ^ 2)) * (P₂ * (Nr₁ * K₁ ^ 2))) :=
          mul_le_mul_of_nonneg_left hNN (mul_nonneg ha hb)
      _ = ((dLa₁ * i₁ ^ 2 * Nr₁) * (dLa₂ * i₂ ^ 2 * Nr₂)) * ((K₁ * K₂) ^ 2 * (P₁ * P₂)) := by ring
      _ ≤ (G0₁ * G0₂) * ((K₁ * K₂) ^ 2 * (P₁ * P₂)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hA hB (mul_nonneg hb hN₂.le) hG1)
            (mul_nonneg (sq_nonneg _) hPP.le)
      _ = (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * 1 := by ring
      _ ≤ (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e)) :=
          mul_le_mul_of_nonneg_left hF (mul_nonneg (mul_nonneg hG (sq_nonneg _)) hPP.le)
  have hR : ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂) =
      ((G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e))
        / (NT * NT)) / ((P₁ * dQ₁) * (P₂ * dQ₂)) := by
    rw [show ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 =
      ((2 / g) ^ (e * f)) ^ 2 * (K₁ * K₂) ^ 2 / (NT * NT) by ring, pow_two_div_sq_identity]
    field_simp [hP₁.ne', hP₂.ne', hQ₁.ne', hQ₂.ne', hNT.ne', hq.ne'] <;> ring
  have hL2 : (detM * i₁ * i₂) ^ 2 =
      (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * dQ₁) * (P₂ * dQ₂)) := by
    rw [show (detM * i₁ * i₂) ^ 2 = detM ^ 2 * i₁ ^ 2 * i₂ ^ 2 by ring, hdet, hd₁, hd₂]
    ring
  have hPQ : 0 < (P₁ * dQ₁) * (P₂ * dQ₂) := mul_pos (mul_pos hP₁ hQ₁) (mul_pos hP₂ hQ₂)
  have hNT2 : 0 < NT * NT := mul_pos hNT hNT
  have hk : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤
      (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e))
        / (NT * NT) := (le_div_iff₀ hNT2).2 key
  have hsq : (detM * i₁ * i₂) ^ 2 ≤ ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂) := by
    rw [hL2, hR]
    first
      | exact div_le_div_of_nonneg_right hk hPQ.le
      | exact (div_le_div_iff_of_pos_right hPQ).2 hk
      | exact div_le_div_of_le_right hk hPQ
  have hRc : 0 ≤ (2 / g) ^ (e * f) * K₁ * K₂ / NT :=
    div_nonneg (mul_nonneg (mul_nonneg hc hK₁.le) hK₂.le) hNT.le
  by_cases h : detM ≤ 0
  · have h0 : detM * i₁ * i₂ ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_iff.2 (Or.inr ⟨h, mul_nonneg hi₁ hi₂⟩)
    exact h0.trans (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _))
      hK₁.le) hK₂.le) hNT.le)
  · have hL : 0 ≤ detM * i₁ * i₂ := mul_nonneg (mul_nonneg (not_le.mp h).le hi₁) hi₂
    have hs : Real.sqrt ((detM * i₁ * i₂) ^ 2) ≤
        Real.sqrt (((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂)) := by
      first
        | exact Real.sqrt_le_sqrt hsq
        | gcongr
    rw [Real.sqrt_sq hL, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hRc] at hs
    calc detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * K₁ * K₂ / NT * Real.sqrt (G0₁ * G0₂) := hs
      _ = (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT := by ring
end Formalism.HermitianLatticeCounting.P
