-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.hk_int_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:12.241384+00:00
-- url     : https://prove2.me/submissions/eab6f509-4686-4283-9711-45ec26644f08

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk3
namespace Formalism.L2.Th1.F.Hk3
theorem _root_.solution {s : ℝ} (hs : 0 ≤ s) (m : ℤ) : ‖hk s (m : ℂ)‖ ≤ |(m : ℝ)| ^ (-(2 : ℝ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hk]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have h3 : |(m : ℝ)| ^ (-(2 : ℝ)) = (|(m : ℝ)| ^ 2)⁻¹ := by
      rw [Real.rpow_neg h0, Real.rpow_two]
    unfold hk
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg h0 _), h3]
    have h2 : |(m : ℝ)| ^ (-(2 * s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    exact mul_le_of_le_one_right (by positivity) h2
end Formalism.L2.Th1.F.Hk3
