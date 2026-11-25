-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.landau_lemma_lfunction_zeros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:52.10313+00:00
-- url     : https://prove2.me/submissions/c55320c6-2d1f-4a83-8e3e-fe4c2a5c3e73

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_le_of_le_exp_log_conductor
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_analytic_conductor
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_disc_center_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_modulus_real
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_ge_of_mem_closedBall
import Theorems.Thm_P2M_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall__531c6a09be92


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
theorem _root_.solution (hLL : LandauLocal3) {C : ℝ}
    (hC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖))
    (hInv : LInvBound) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10) (hfs : DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
          Real.log ((q : ℝ) * (|s.im| + 2))) := by
  set z₀ : ℂ := (21 / 20 : ℂ) + s.im * I with hz₀
  have hz₀re : z₀.re = 21 / 20 := by simp [hz₀]
  set A : ℝ := 21 * (|C| + 1) with hAdef
  have hq1 := one_le_modulus_real q
  have hX : (0 : ℝ) < (q : ℝ) * (|s.im| + 2) := by positivity
  set M : ℝ := 2 * A * ((q : ℝ) * (|s.im| + 2)) with hMdef
  have hA1 : 1 ≤ A := by
    have := abs_nonneg C
    rw [hAdef]
    nlinarith
  have hM1 : 1 ≤ M := by
    have h2 : 2 ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
    rw [hMdef]
    nlinarith
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hz₀re]; norm_num)
  have hinv := hInv q χ z₀ (by rw [hz₀re]; norm_num)
  rw [hz₀re] at hinv
  have h21 : ‖DirichletCharacter.LFunction χ z₀‖⁻¹ ≤ 21 := by
    have e : (21 / 20 : ℝ) / (21 / 20 - 1) = 21 := by norm_num
    linarith
  have hlow : 1 ≤ 21 * ‖DirichletCharacter.LFunction χ z₀‖ := by
    have hp : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    have := mul_le_mul_of_nonneg_right h21 hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at this
  have hbound : ∀ z ∈ Metric.closedBall z₀ (11 / 20),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre := re_ge_of_mem_closedBall hz
    rw [hz₀re] at hre
    have h1 := hC q χ hχ z (by linarith)
    have hn := norm_le_norm_add_of_mem_closedBall' hz
    have hn0 := norm_disc_center_le s.im
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hz1 : 1 + ‖z‖ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
    have hY : 0 ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by positivity
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ |C| * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hq0)
            (by positivity)
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hq0) hz1 (by positivity)
          positivity
      _ = (|C| + 1) * q * (2 * (|s.im| + 2)) * 1 := by ring
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) * (21 * ‖DirichletCharacter.LFunction χ z₀‖) :=
          mul_le_mul_of_nonneg_left hlow hY
      _ = M * ‖DirichletCharacter.LFunction χ z₀‖ := by
          rw [hMdef, hAdef]
          ring
  obtain ⟨Z, m, hZ, -, -, hm1, hsum, hder⟩ := hLL (DirichletCharacter.LFunction χ) z₀ (11 / 20) M
    (by norm_num) hM1 (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hf0 hbound
  have hlogM : Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * Real.log ((q : ℝ) * (|s.im| + 2)) :=
    log_le_of_le_exp_log_conductor hA1 hM1 (log_two_le_log_analytic_conductor q s.im) (Real.exp_pos _)
      (by rw [Real.exp_log hX, hMdef])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Z, m, hZ, hm1, ?_, ?_⟩
  · push_cast at hsum
    calc ∑ ρ ∈ Z, (m ρ : ℝ) ≤ Real.log M / Real.log 2 := hsum
      _ ≤ _ := div_le_div_of_nonneg_right hlogM hl2.le
  · have hs6 : s ∈ Metric.closedBall z₀ (11 / 20 / 6) := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : s - z₀ = ((s.re - 21 / 20 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hz₀]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ ≤ 72 * Real.log M / (11 / 20) := hder s hs6 hfs
      _ = 1440 / 11 * Real.log M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM (by norm_num)
end Formalism.ZeroFreeDirichlet
