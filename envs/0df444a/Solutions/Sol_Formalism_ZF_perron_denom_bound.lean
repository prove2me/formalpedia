-- Prove2me | solution 1 for Formalism.ZF.perron_denom_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:33.350795+00:00
-- url     : https://prove2.me/submissions/4326c1f4-097c-4ad1-852b-5d5517f3c7ff

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ) :
    min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) ≤ ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ := by
  set m := min ((σ₀ - 1) ^ 2) 1 with hm
  have hm0 : 0 ≤ m := le_min (sq_nonneg _) zero_le_one
  have hm1 : m ≤ 1 := min_le_right _ _
  have hm2 : m ≤ (σ₀ - 1) ^ 2 := min_le_left _ _
  have hn1 : ‖((σ₀ : ℂ) + t * I)‖ ^ 2 = σ₀ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hn2 : ‖((σ₀ : ℂ) + t * I - 1)‖ ^ 2 = (σ₀ - 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have a0 : 0 ≤ m * (1 + t ^ 2) := by positivity
  have a1 : m * (1 + t ^ 2) ≤ σ₀ ^ 2 + t ^ 2 := by nlinarith
  have a2 : m * (1 + t ^ 2) ≤ (σ₀ - 1) ^ 2 + t ^ 2 := by nlinarith
  have key : (m * (1 + t ^ 2)) ^ 2 ≤ (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [sq]
    exact mul_le_mul a1 a2 a0 (by positivity)
  have e : (‖((σ₀ : ℂ) + t * I)‖ * ‖((σ₀ : ℂ) + t * I - 1)‖) ^ 2 =
      (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [mul_pow, hn1, hn2]
  rw [norm_mul]
  exact (pow_le_pow_iff_left₀ a0 (by positivity) two_ne_zero).1 (key.trans e.symm.le)
end Formalism.ZF
