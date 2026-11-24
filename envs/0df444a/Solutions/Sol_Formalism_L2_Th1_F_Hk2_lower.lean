-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk2.lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:03.727283+00:00
-- url     : https://prove2.me/submissions/6e96f29a-5f83-4b28-a95a-ad08b84779db

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelCellContinuous

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
theorem _root_.solution {τ : ℂ} (m n : ℤ) (hn : n ≠ 0) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    kap τ * (|(m : ℝ)| + |(n : ℝ)|) ≤ ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ := by
  set W := ‖(m : ℂ) + (x : ℂ) + (n : ℂ) * τ‖ with hW
  have hY : 0 ≤ |τ.im| := abs_nonneg _
  have hA : 0 ≤ |τ.re| := abs_nonneg _
  have hN : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have h1 : |(n : ℝ)| * |τ.im| ≤ W := by
    have := Complex.abs_im_le_norm ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)
    simpa [abs_mul] using this
  have h2 : |(m : ℝ)| ≤ W + |(n : ℝ)| + |(n : ℝ)| * |τ.re| := by
    have h := Complex.abs_re_le_norm ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ)
    have e : ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ).re = (m : ℝ) + x + (n : ℝ) * τ.re := by simp
    rw [e] at h
    have e2 : (m : ℝ) = ((m : ℝ) + x + (n : ℝ) * τ.re) - x - (n : ℝ) * τ.re := by ring
    calc |(m : ℝ)| = |((m : ℝ) + x + (n : ℝ) * τ.re) - x - (n : ℝ) * τ.re| := by rw [← e2]
      _ ≤ |((m : ℝ) + x + (n : ℝ) * τ.re) - x| + |(n : ℝ) * τ.re| := abs_sub _ _
      _ ≤ |(m : ℝ) + x + (n : ℝ) * τ.re| + |x| + |(n : ℝ) * τ.re| := by
          gcongr
          exact abs_sub _ _
      _ ≤ W + |(n : ℝ)| + |(n : ℝ)| * |τ.re| := by
          rw [abs_mul, abs_of_nonneg hx0]
          gcongr
          linarith
  unfold kap
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  have k1 := mul_le_mul_of_nonneg_left h2 hY
  have k2 := mul_le_mul_of_nonneg_right h1 hA
  nlinarith
end Formalism.L2.Th1.F.Hk2
