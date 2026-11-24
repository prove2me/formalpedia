-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.exponential_sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:49.162198+00:00
-- url     : https://prove2.me/submissions/6f17dc9b-eb3c-42c5-8fe6-41cda888f913

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : ExpSplit := by
  intro c v lam hc hv hl
  have hs := Real.sqrt_nonneg v
  have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv
  rcases le_total (Real.sqrt v) lam with h | h
  · have : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-c * v / (2 * lam)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hc.le hv, mul_nonneg (mul_nonneg hc.le hv) (sub_nonneg.mpr h)]
    linarith [Real.exp_pos (-c * Real.sqrt v / 2)]
  · have : Real.exp (-c * v / (lam + Real.sqrt v)) ≤ Real.exp (-c * Real.sqrt v / 2) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hc.le hs, mul_nonneg (mul_nonneg hc.le hs) (sub_nonneg.mpr h)]
    linarith [Real.exp_pos (-c * v / (2 * lam))]
end Formalism.HermitianLattices.ZeroFreeRegionGL2
