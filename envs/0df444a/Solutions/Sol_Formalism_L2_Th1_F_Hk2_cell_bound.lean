-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:39.772813+00:00
-- url     : https://prove2.me/submissions/51798208-ad29-4144-beb5-3554e7dcb8f4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_hk_diff
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_kap_pos
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_kap_le_one
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_lower
import Theorems.Thm_Formalism_L2_Th1_F_Hk2_hk_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk2
namespace Formalism.L2.Th1.F.Hk2
theorem _root_.solution {τ : ℂ} (hτ : τ.im ≠ 0) {p : ℤ × ℤ} (hp : p.2 ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) :
    ‖hkCell τ s p‖ ≤ 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹ := by
  have hκ := kap_pos hτ
  have hκ1 := kap_le_one τ
  have hN : (1 : ℝ) ≤ |(p.2 : ℝ)| := by
    have : (1 : ℤ) ≤ |p.2| := Int.one_le_abs hp
    exact_mod_cast this
  have hρ : kap τ ≤ kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|) := by
    have : 0 ≤ |(p.1 : ℝ)| := abs_nonneg _
    nlinarith
  have cx : Continuous fun x : ℝ => hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ) := by
    have h := (hk_cont hτ hp p.1).comp (Continuous.prodMk (continuous_const (y := s)) continuous_id)
    simpa [Function.uncurry, Function.comp_def] using h
  have e : hkCell τ s p = ∫ x in (0 : ℝ)..1, (hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ)
      - hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ)) := by
    rw [intervalIntegral.integral_sub (by simp) (cx.intervalIntegrable 0 1)]
    simp [hkCell]
  rw [e]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := 4 * (kap τ ^ 2)⁻¹ * ((kap τ * (|(p.1 : ℝ)| + |(p.2 : ℝ)|)) ^ 3)⁻¹)
    (f := fun x : ℝ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ) - hk s ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ))
    (fun x hx => by
      rw [Set.uIoc_of_le zero_le_one] at hx
      have l0 := lower (τ := τ) p.1 p.2 hp (le_refl (0 : ℝ)) zero_le_one
      have lx := lower (τ := τ) p.1 p.2 hp hx.1.le hx.2
      simp only [Complex.ofReal_zero, add_zero] at l0
      refine hk_diff hκ hκ1 hρ l0 lx ?_ hs0 hs1
      have : (p.1 : ℂ) + (p.2 : ℂ) * τ - ((p.1 : ℂ) + (x : ℂ) + (p.2 : ℂ) * τ) = -(x : ℂ) := by ring
      rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2)
  simpa using this
end Formalism.L2.Th1.F.Hk2
