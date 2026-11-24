-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.smoothed_character_sum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:00.902012+00:00
-- url     : https://prove2.me/submissions/e77b6497-5d21-48be-aae9-cff35906a864

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExpGainFromZeroFreeRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SmoothChiOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_explicit_general
import Theorems.Thm_Formalism_ZeroFreeDirichlet_cube_mul_exp_le_poly_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_exp_gain_from_zero_free_region
import Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_error_terms_sum_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_small_scale_exp_bounds


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
theorem _root_.solution : SmoothChiOf := by
  intro hP hRS hD hRight c₁ hc₁ hc₁'
  obtain ⟨CD, hCD⟩ := hD c₁ hc₁ hc₁'
  obtain ⟨C₀, hC₀, hR⟩ := hRight
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
      16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
    have ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
    have ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))
    have ha4 : 0 ≤ 8 / c₁ := by positivity
    rw [hAdef]; linarith
  refine ⟨c₁ / 4, max (16 * A * (6 * (8 / (2 * c₁)) ^ 3)) (3 * (4 * 12 ^ 3 * A)), by positivity, ?_⟩
  intro q _ χ B y hχ hE hy hq
  have hD' : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
      ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 :=
    fun s h1 h2 => (hCD q χ B hχ hE s h1 h2).trans
      (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hℓpos : 0 < Real.log y := Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  rw [← hsdef] at hq ⊢
  have hℓ : Real.log y = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hℓpos.le).symm
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hℓpos
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (c₁ * s / 2) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-(c₁ * s / 2)) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp (by positivity)
  have hT0 : 0 < T := by linarith
  have hTX : T * X = 1 := by rw [hTdef, hXdef, ← Real.exp_add]; simp
  have hX0 : 0 < X := by rw [hXdef]; exact Real.exp_pos _
  have hX1 : X ≤ 1 := by
    rw [hXdef]; exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hc₁ hs0])
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2)) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hmain⟩ :=
    chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ B hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm

  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * (T + 2) := one_le_mul_of_one_le_of_one_le hq1 (by linarith)
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hqT1
  have hlogq : Real.log q ≤ c₁ / 4 * s := (Real.log_le_iff_le_exp (by linarith)).mpr hq
  have hlogT : Real.log (T + 2) ≤ 2 + c₁ * s / 2 := by
    rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have := mul_le_mul_of_nonneg_right h3 hT0.le
    linarith
  have hLb : L ≤ 3 * c₁ / 4 * s + 2 := by
    rw [hLdef, Real.log_mul (by linarith) (by linarith)]
    linarith
  have hs'1 : 1 ≤ s + 2 := by linarith
  have hLs' : L ≤ s + 2 := by
    have : 3 * c₁ / 4 * s ≤ s := mul_le_of_le_one_left hs0.le (by linarith)
    linarith
  have hP1 : 1 ≤ (s + 2) ^ 3 := one_le_pow₀ hs'1
  have h23 : (s + 2) ^ 2 ≤ (s + 2) ^ 3 := pow_le_pow_right₀ hs'1 (by norm_num)
  have hℓP : Real.log y ≤ (s + 2) ^ 3 := by
    rw [hℓ]
    have h1 : s ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hs0.le (by linarith) 2
    linarith
  have hL2P : L ^ 2 ≤ (s + 2) ^ 3 := by
    have h1 : L ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hL0 hLs' 2
    linarith
  have hL3P : L ^ 3 ≤ (s + 2) ^ 3 := pow_le_pow_left₀ hL0 hLs' 3
  have hLP : L ≤ (s + 2) ^ 3 := by
    have : s + 2 ≤ (s + 2) ^ 3 := le_self_pow₀ hs'1 (by norm_num)
    linarith
  have hyσ0 : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
  have hterms := perron_error_terms_sum_bound C C₀ c₁ y T X L ((s + 2) ^ 3) (y ^ σ₁) (Real.log y) hc₁ hC hC₀ hy0
    hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP
  rw [← hAdef] at hterms
  have htot := hmain.trans hterms
  have hyX : 0 ≤ y * X := by positivity
  by_cases hs : 10 ≤ s
  ·
    have hL4 : 4 * L ≤ s := by
      have := mul_le_mul_of_nonneg_right hc₁' hs0.le
      linarith
    have hLpos : 0 < L := by
      rw [hLdef]; apply Real.log_pos
      have := mul_le_mul hq1 (show (3 : ℝ) ≤ T + 2 by linarith) (by norm_num) (by linarith)
      linarith
    have hWX : T * y ^ σ₁ ≤ y * X := by
      rw [hTdef, hXdef]; exact exp_gain_from_zero_free_region y s c₁ σ₁ L hy0 hℓ hs0 hc₁ hLpos hL4 hσ₁
    have hs'2 : (s + 2) ^ 3 ≤ 8 * s ^ 3 := by
      calc (s + 2) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 8 * s ^ 3 := by ring
    have hX3 := cube_mul_exp_le_poly_bound c₁ s y X hc₁ hs0 hy0 hXdef
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * (8 * s ^ 3) * (y * X + y * X) := by gcongr
      _ = 16 * A * (s ^ 3 * X * y) := by ring
      _ ≤ 16 * A * (6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s))) := by gcongr
      _ = 16 * A * (6 * (8 / (2 * c₁)) ^ 3) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  ·
    rw [not_le] at hs
    obtain ⟨hT3', hexp⟩ := small_scale_exp_bounds c₁ s hc₁ hc₁' hs
    have hT3 : T ≤ 3 := hTdef ▸ hT3'
    have hPs : (s + 2) ^ 3 ≤ 12 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hσ₁1 : σ₁ ≤ 1 := by
      have : 0 ≤ c₁ / (4 * L) := by positivity
      linarith
    have hyσ : y ^ σ₁ ≤ y := by
      have := Real.rpow_le_rpow_of_exponent_le hy1 hσ₁1
      rwa [Real.rpow_one] at this
    have hW3 : T * y ^ σ₁ ≤ 3 * y := mul_le_mul hT3 hyσ hyσ0 (by norm_num)
    have hyX1 : y * X ≤ y := mul_le_of_le_one_right hy0.le hX1
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * 12 ^ 3 * (y + 3 * y) := by gcongr
      _ = 4 * 12 ^ 3 * A * y * 1 := by ring
      _ ≤ 4 * 12 ^ 3 * A * y * (3 * Real.exp (-(c₁ / 4) * s)) := by gcongr
      _ = 3 * (4 * 12 ^ 3 * A) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _
end Formalism.ZeroFreeDirichlet
