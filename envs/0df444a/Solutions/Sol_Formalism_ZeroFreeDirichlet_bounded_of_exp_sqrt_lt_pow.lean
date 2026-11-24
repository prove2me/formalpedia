-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.bounded_of_exp_sqrt_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:16.576817+00:00
-- url     : https://prove2.me/submissions/06214df3-9eaa-4b07-9b52-8ba29238e0fd

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ L : ℝ, 0 < L → Real.exp (c * Real.sqrt L) < L ^ A → L ≤ U := by
  have ho := (isLittleO_rpow_exp_pos_mul_atTop (2 * A) hc).comp_tendsto Real.tendsto_sqrt_atTop
  have hb := ho.bound (show (0:ℝ) < 1 / 2 by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max N 0, le_max_right _ _, fun L hL hlt => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hLN : N ≤ L := le_trans (le_max_left _ _) hcon.le
  have h2 : ‖Real.sqrt L ^ (2 * A)‖ ≤ 1 / 2 * ‖Real.exp (c * Real.sqrt L)‖ := hN L hLN
  have hs : Real.sqrt L ^ (2 * A) = L ^ A := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le, hs] at h2
  linarith [Real.exp_pos (c * Real.sqrt L)]
end Formalism.ZeroFreeDirichlet
