-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.det_index_product_hyperbolic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:28.532972+00:00
-- url     : https://prove2.me/submissions/15e57a9b-d481-465b-8bd0-477a2f2a129d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.DetIndexProductHyperbolicInequality := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f
    hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hD₁ hD₂ hPs₁ hPs₂ hG₁ hG₂ hB₁ hB₂ hgQ
  subst hPs₁ hPs₂
  have hG₁0 : 0 ≤ G0₁ / Nr₁ := le_trans (by positivity) hG₁
  have hG₂0 : 0 ≤ G0₂ / Nr₂ := le_trans (by positivity) hG₂
  have hG₁' : 0 ≤ G0₁ := by
    have h := mul_nonneg hG₁0 hN₁.le
    rwa [div_mul_cancel₀ _ hN₁.ne'] at h
  have hG₂' : 0 ≤ G0₂ := by
    have h := mul_nonneg hG₂0 hN₂.le
    rwa [div_mul_cancel₀ _ hN₂.ne'] at h
  have hD0 : 0 ≤ detM := by
    rw [hD₁]
    positivity
  have hDD : detM * detM = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
    calc detM * detM = (dLa₁ / (P₁ * dQ₁)) * (dLa₂ / (P₂ * dQ₂)) := by rw [← hD₁, ← hD₂]
      _ = dLa₁ * dLa₂ / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
        rw [div_mul_div_comm]
        congr 1
        ring
  have hX2 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * P₂) * (dQ₁ * dQ₂)) := by
    calc (detM * i₁ * i₂) ^ 2 = (detM * detM) * i₁ ^ 2 * i₂ ^ 2 := by ring
      _ = _ := by
        rw [hDD]
        field_simp
  have hnum : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) :=
    mul_le_mul hG₁ hG₂ (by positivity) hG₁0
  have hgQ' : g ^ (2 * f * e) / 4 ^ (e * f) ≤ dQ₁ * dQ₂ := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hgQ, show (4:ℝ) ^ (e * f) * dQ₁ * dQ₂ = dQ₁ * dQ₂ * 4 ^ (e * f) by ring]
  have hden : (NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f)) ≤
      (P₁ * P₂) * (dQ₁ * dQ₂) :=
    mul_le_mul (mul_le_mul hB₁ hB₂ (by positivity) hP₁.le) hgQ' (by positivity) (by positivity)
  have hX2le : (detM * i₁ * i₂) ^ 2 ≤ (G0₁ / Nr₁) * (G0₂ / Nr₂) /
      ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f))) := by
    rw [hX2]
    exact div_le_div₀ (mul_nonneg hG₁0 hG₂0) hnum (by positivity) hden
  have hpw : ((2 / g) ^ (e * f)) ^ 2 = 4 ^ (e * f) / g ^ (2 * f * e) := by
    rw [← pow_mul, div_pow, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show e * f * 2 = 2 * (e * f) by ring, show 2 * f * e = 2 * (e * f) by ring]
  have hY2 : ((2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT) ^ 2 =
      (G0₁ / Nr₁) * (G0₂ / Nr₂) /
        ((NT / (Nr₂ * K₂ ^ 2)) * (NT / (Nr₁ * K₁ ^ 2)) * (g ^ (2 * f * e) / 4 ^ (e * f))) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, hpw, Real.sq_sqrt (mul_nonneg hG₁' hG₂')]
    field_simp
  have hY0 : 0 ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT := by positivity
  rw [← hY2] at hX2le
  exact (pow_le_pow_iff_left₀ (by positivity) hY0 two_ne_zero).mp hX2le
end Formalism.SLP.GlobalBoundRefinements.P
