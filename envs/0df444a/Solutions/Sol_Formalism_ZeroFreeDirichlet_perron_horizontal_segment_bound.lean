-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_horizontal_segment_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:13.761798+00:00
-- url     : https://prove2.me/submissions/187ecb9d-5b2b-4c92-adfa-9f8ac6b1ed15

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_perron_integrand_eq
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_sum_le_of_card_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c₁ C : ℝ)
    (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T x v σ₀ σ₁ : ℝ) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁)
    (hx1 : σ₁ ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  set s : ℂ := (x : ℂ) + (v : ℂ) * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = v := by simp [hs]
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre, hv]; exact le_trans hσ₁ hx1
  have hne : ∀ β ∈ B, s ≠ (β : ℂ) := by
    intro β _ h
    have h1 := congrArg Complex.im h
    rw [hsim, Complex.ofReal_im] at h1
    rw [h1] at hv; simp at hv; linarith
  have hsum : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 1 := by
    refine norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) 1 zero_le_one ?_
    intro β _
    rw [norm_div, norm_one]
    have h2 : (s - (β : ℂ)).im = v := by simp [hsim]
    have h1 : (1:ℝ) ≤ ‖s - (β : ℂ)‖ := by
      calc (1:ℝ) ≤ T := hT
        _ = |v| := hv.symm
        _ = |(s - (β : ℂ)).im| := by rw [h2]
        _ ≤ ‖s - (β : ℂ)‖ := Complex.abs_im_le_norm _
    rw [div_le_one (by linarith)]; exact h1
  have hD' := hD s hreg hne
  rw [hsim, hv] at hD'
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := by
    have h3 := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
    rw [add_sub_cancel_right] at h3
    linarith
  rw [norm_perron_integrand_eq χ y hy0 s, hsre]
  have hK : 0 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 := le_trans (norm_nonneg _) hN
  have hyx : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx2
  have hw1 : T ≤ ‖s‖ := by rw [← hv, ← hsim]; exact Complex.abs_im_le_norm s
  have hw2 : T ≤ ‖s - 1‖ := by
    have h4 : (s - 1).im = v := by simp [hsim]
    rw [← hv, ← h4]; exact Complex.abs_im_le_norm _
  have hden : T ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  calc ‖negLD χ s‖ * y ^ x / (‖s‖ * ‖s - 1‖)
      ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / (‖s‖ * ‖s - 1‖) :=
        div_le_div_of_nonneg_right (mul_le_mul hN hyx (by positivity) hK) (by positivity)
    _ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1) * y ^ σ₀ / T ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hK (Real.rpow_nonneg hy0.le _)) (by positivity) hden
end Formalism.ZeroFreeDirichlet
