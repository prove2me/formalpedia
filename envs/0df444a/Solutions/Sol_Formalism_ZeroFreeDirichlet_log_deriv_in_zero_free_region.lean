-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_deriv_in_zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:39:37.897723+00:00
-- url     : https://prove2.me/submissions/d6c79957-023d-4555-9698-2ed9e111d887

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogDerivSubExceptionalZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogDerivRegionChiOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_landau_lemma_lfunction_zeros
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_analytic_conductor_ge_const
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_deriv_sub_exceptional_zeros
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_modulus_real
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zero_free_region_mono_half


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : LogDerivRegionChiOf := by
  intro hLL hG hInv hR c₁ hc₁ hc₁'
  obtain ⟨C, hC⟩ := hG
  obtain ⟨C₀, hC₀, hR⟩ := hR
  set A : ℝ := 21 * (|C| + 1) with hA
  have hA1 : 21 ≤ A := by have := abs_nonneg C; linarith
  set K₁ : ℝ := Real.log (2 * A) / Real.log 2 + 1 with hK₁
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₁0 : 1 ≤ K₁ := by
    have : 0 ≤ Real.log (2 * A) / Real.log 2 := div_nonneg (Real.log_nonneg (by linarith)) hl2.le
    linarith
  refine ⟨2880 / 11 * K₁ + 3 * K₁ / (c₁ * Real.log 2) + 480 / 11 + 4 * (20 + C₀), ?_⟩
  intro q _ χ B hχ hB s hs hsB
  obtain ⟨hBcard, hBmem, hBall⟩ := hB
  have hq := one_le_modulus_real q
  set L := Real.log ((q : ℝ) * (|s.im| + 2)) with hLdef
  have hL69 : 69 / 100 ≤ L := log_analytic_conductor_ge_const q s.im
  have hL : 1 / 2 ≤ L := by linarith
  have hLsq : 1 ≤ 4 * L ^ 2 := by nlinarith
  have hLsq' : L ≤ 2 * L ^ 2 := by nlinarith
  have hT1 : 0 ≤ 2880 / 11 * K₁ := by positivity
  have hT2 : 0 ≤ 3 * K₁ / (c₁ * Real.log 2) := by positivity
  have hβlt : ∀ β ∈ B, β < 1 := by
    intro β hβ
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using le_of_not_gt h)
      (hBmem β hβ).2.2.1
  have hσlow : 1 - c₁ / 2 / L ≤ s.re := hs
  by_cases hσ : 11 / 10 ≤ s.re
  ·
    have h1 : ‖negLD χ s‖ ≤ 10 + C₀ := by
      have := hR q χ s (by linarith)
      have : 1 / (s.re - 1) ≤ 10 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h2 : ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ 10 := by
      calc ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ ∑ β ∈ B, ‖1 / (s - (β : ℂ))‖ := norm_sum_le _ _
        _ ≤ ∑ β ∈ B, (10 : ℝ) := by
          apply Finset.sum_le_sum
          intro β hβ
          have hb := hβlt β hβ
          have hre : (s - (β : ℂ)).re = s.re - β := by simp
          have hn : 1 / 10 ≤ ‖s - (β : ℂ)‖ := by
            have := Complex.re_le_norm (s - (β : ℂ))
            linarith
          rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
          linarith
        _ = B.card * 10 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * 10 := by gcongr; exact_mod_cast hBcard
        _ = 10 := by ring
    have h3 : 0 ≤ (2880 / 11 * K₁ + 3 * K₁ / (c₁ * Real.log 2) + 480 / 11) * L ^ 2 := by positivity
    calc ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖
        ≤ ‖negLD χ s‖ + ‖∑ β ∈ B, 1 / (s - (β : ℂ))‖ := norm_add_le _ _
      _ ≤ 20 + C₀ := by linarith
      _ ≤ 4 * (20 + C₀) * L ^ 2 := by nlinarith
      _ ≤ _ := by nlinarith
  · have hσ' : s.re < 11 / 10 := lt_of_not_ge hσ
    have hshift : c₁ / 2 / L ≤ 1 / 27 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hσ1 : 26 / 27 ≤ s.re := by linarith
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := by
      intro h0
      obtain ⟨β, hβ, hsβ⟩ := hBall s (zero_free_region_mono_half hc₁ q s hs) ⟨Or.inl hχ, h0⟩
      exact hsB β hβ hsβ
    obtain ⟨Z, m, hZ, hm3, hsum, hE⟩ := landau_lemma_lfunction_zeros hLL hC hInv hχ hσ1 hσ' hfs
    have hmain := log_deriv_sub_exceptional_zeros hc₁ hχ hBcard hBmem hBall hs hσ1 hσ' hZ hm3 hsum hE
    have hKL : 0 ≤ K₁ * L := by positivity
    have h4 : 0 ≤ 4 * (20 + C₀) * L ^ 2 := by positivity
    refine le_trans hmain ?_
    nlinarith
end Formalism.ZeroFreeDirichlet
