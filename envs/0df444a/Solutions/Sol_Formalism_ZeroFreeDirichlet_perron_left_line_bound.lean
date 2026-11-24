-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_left_line_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:23.28302+00:00
-- url     : https://prove2.me/submissions/3bbe0c86-8aaa-4644-9ded-c8b3a5838e1a

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_perron_integrand_eq
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_sum_le_of_card_le_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_conductor_pos_real
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_analytic_conductor_mono

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
    (hc₁ : 0 ≤ c₁) (hC : 0 ≤ C) (B : Finset ℝ) (hB : B.card ≤ 1)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (y T u σ₁ δ ε : ℝ) (hy : 0 < y) (hu : |u| ≤ T)
    (hσ₁ : 1 - (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁) (hhalf : 1 / 2 ≤ σ₁)
    (hε : 0 < ε) (hgap : ε ≤ 1 - σ₁) (hδ : 0 < δ) (hδB : ∀ β ∈ B, δ ≤ |σ₁ - β|) :
    ‖Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) := by
  set s : ℂ := (σ₁ : ℂ) + (u : ℂ) * I with hs
  have hsre : s.re = σ₁ := by simp [hs]
  have hsim : s.im = u := by simp [hs]
  have hLu := log_conductor_pos_real q u
  have hmono := log_analytic_conductor_mono q u T hu
  have hreg : InRegion (c₁ / 2) q s := by
    unfold InRegion; rw [hsim, hsre]
    refine le_trans ?_ hσ₁
    have h1 : (c₁ / 2) / Real.log ((q : ℝ) * (T + 2)) ≤ (c₁ / 2) / Real.log ((q : ℝ) * (|u| + 2)) :=
      div_le_div_of_nonneg_left (by linarith) hLu hmono
    linarith
  have hdist : ∀ β ∈ B, δ ≤ ‖s - (β : ℂ)‖ := by
    intro β hβ
    have h1 : (s - (β : ℂ)).re = σ₁ - β := by simp [hsre]
    calc δ ≤ |σ₁ - β| := hδB β hβ
      _ = |(s - (β : ℂ)).re| := by rw [h1]
      _ ≤ ‖s - (β : ℂ)‖ := Complex.abs_re_le_norm _
  have hne : ∀ β ∈ B, s ≠ (β : ℂ) := by
    intro β hβ h
    have h1 := hdist β hβ
    rw [h, sub_self, norm_zero] at h1; linarith
  have hsum : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 1 / δ := by
    refine norm_sum_le_of_card_le_one B hB (fun β : ℝ => 1 / (s - (β : ℂ))) (1 / δ) (by positivity) ?_
    intro β hβ
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ (hdist β hβ)
  have hD' := hD s hreg hne
  rw [hsim] at hD'
  have hlogsq : Real.log ((q : ℝ) * (|u| + 2)) ^ 2 ≤ Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
    pow_le_pow_left₀ hLu.le hmono 2
  have hN : ‖negLD χ s‖ ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := by
    have h3 := norm_sub_le (negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))) (∑ β ∈ B, 1 / (s - (β : ℂ)))
    rw [add_sub_cancel_right] at h3
    have h4 : C * Real.log ((q : ℝ) * (|u| + 2)) ^ 2 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq hC
    linarith
  have hK : 0 ≤ C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ := le_trans (norm_nonneg _) hN
  rw [norm_perron_integrand_eq χ y hy s, hsre]
  have hw1 : 1 / 2 ≤ ‖s‖ := by
    calc (1:ℝ) / 2 ≤ σ₁ := hhalf
      _ ≤ |σ₁| := le_abs_self _
      _ = |s.re| := by rw [hsre]
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hw2 : ε ≤ ‖s - 1‖ := by
    have h5 : (s - 1).re = σ₁ - 1 := by simp [hsre]
    calc ε ≤ 1 - σ₁ := hgap
      _ ≤ |σ₁ - 1| := by rw [abs_sub_comm]; exact le_abs_self _
      _ = |(s - 1).re| := by rw [h5]
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hden : ε / 2 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  have hden0 : 0 < ‖s‖ * ‖s - 1‖ := by linarith
  have hyp : 0 < y ^ σ₁ := Real.rpow_pos_of_pos hy _
  have h2 : (2 / ε) * (ε / 2) = 1 := by field_simp
  rw [div_le_iff₀ hden0]
  calc ‖negLD χ s‖ * y ^ σ₁ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ :=
        mul_le_mul_of_nonneg_right hN hyp.le
    _ = (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) * (ε / 2) := by
        rw [mul_assoc _ (2 / ε), h2, mul_one]
    _ ≤ (C * Real.log ((q : ℝ) * (T + 2)) ^ 2 + 1 / δ) * y ^ σ₁ * (2 / ε) * (‖s‖ * ‖s - 1‖) :=
        mul_le_mul_of_nonneg_left hden (mul_nonneg (mul_nonneg hK hyp.le) (by positivity))
end Formalism.ZeroFreeDirichlet
