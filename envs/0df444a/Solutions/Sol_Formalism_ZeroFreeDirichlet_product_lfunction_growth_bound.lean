-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.product_lfunction_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:57:00.877261+00:00
-- url     : https://prove2.me/submissions/5c8b1e51-1e68-49bc-ba27-a78365e06048

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqGrowth
import Theorems.Thm_Formalism_ZeroFreeDirichlet_circle_about_two_geometry
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zeta_norm_le_on_circle
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_polynomial_growth


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
theorem _root_.solution : BqGrowth := by
  obtain ⟨C, hC⟩ := lfunction_polynomial_growth
  refine ⟨14 * (9 / 2 * |C|) ^ 3, 3, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h3 s hs
  obtain ⟨hre, hn, -⟩ := circle_about_two_geometry hs
  have hz := zeta_norm_le_on_circle hs
  have L : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ 9 / 2 * |C| * q := by
    intro q _ χ hχ
    have h := hC q χ hχ s hre
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hCq : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq
    have hp : 0 ≤ |C| * q := by positivity
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖) := h
      _ ≤ |C| * q * (1 + ‖s‖) := mul_le_mul_of_nonneg_right hCq (by positivity)
      _ ≤ |C| * q * (9 / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
      _ = 9 / 2 * |C| * q := by ring
  have e1 := L q₁ χ₁ h1
  have e2 := L q₂ χ₂ h2
  have e3 := L (q₁ * q₂) ψ h3
  have hq1 : (q₁ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right q₁ (Nat.pos_of_ne_zero (NeZero.ne q₂))
  have hq2 : (q₂ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left q₂ (Nat.pos_of_ne_zero (NeZero.ne q₁))
  have ha : 0 ≤ 9 / 2 * |C| := by positivity
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold Fbq
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ₁ s‖ * ‖DirichletCharacter.LFunction χ₂ s‖ *
        ‖DirichletCharacter.LFunction ψ s‖
      ≤ 14 * (9 / 2 * |C| * q₁) * (9 / 2 * |C| * q₂) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by
        gcongr
    _ ≤ 14 * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) *
          (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by gcongr
    _ = 14 * (9 / 2 * |C|) ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 3 := by ring
end Formalism.ZeroFreeDirichlet
