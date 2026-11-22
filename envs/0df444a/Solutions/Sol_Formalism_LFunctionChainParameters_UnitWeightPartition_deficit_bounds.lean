-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.UnitWeightPartition.deficit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:38.779816+00:00
-- url     : https://prove2.me/submissions/68aab75e-74bc-4013-a765-25470701b0d3

import Definitions.Def_Formalism_SizeWindowBrackets_ClaimGaFree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.UnitWeightPartition
open Finset
variable {ι κ : Type*} [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.UnitWeightPartition
theorem _root_.solution (f : ℕ) (T dM du : ℝ) : ClaimDe f T dM du := by
  unfold ClaimDe
  intro hdM hT hdu
  have hT1 : (1 : ℝ) < T - 1 := by linarith
  have hT1p : (0 : ℝ) < T - 1 := by linarith
  have hTp : (0 : ℝ) < T := by linarith
  have hx0 : 0 < 1 / (T - 1) := div_pos one_pos hT1p
  have hx1 : 1 / (T - 1) < 1 := by rw [div_lt_one hT1p]; exact hT1
  have hq0 : 0 < 1 - 1 / (T - 1) := by linarith
  have hq1 : 1 - 1 / (T - 1) ≤ 1 := by linarith
  have hdM0 : dM ≠ 0 := hdM.ne'
  have hr : du / dM = (1 - 1 / (T - 1)) ^ f := by
    rw [hdu, mul_div_right_comm, div_self hdM0, one_mul]
  have hpow0 : 0 < (1 - 1 / (T - 1)) ^ f := pow_pos hq0 f
  have hpow1 : (1 - 1 / (T - 1)) ^ f ≤ 1 := pow_le_one₀ hq0.le hq1
  have hbern : 1 + (f : ℝ) * (-(1 / (T - 1))) ≤ (1 + -(1 / (T - 1))) ^ f :=
    one_add_mul_le_pow (by linarith) f
  have hq : (1 : ℝ) + -(1 / (T - 1)) = 1 - 1 / (T - 1) := by ring
  rw [hq] at hbern
  have hfx : (f : ℝ) * (-(1 / (T - 1))) = -((f : ℝ) / (T - 1)) := by ring
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hfT : (f : ℝ) / (T - 1) ≤ 2 * (f : ℝ) / T := by
    rw [div_le_iff₀ hT1p, div_mul_eq_mul_div, le_div_iff₀ hTp]
    nlinarith [mul_nonneg hf0 (by linarith : (0 : ℝ) ≤ T - 2)]
  rw [hr]
  refine ⟨?_, by linarith, by linarith, by linarith⟩
  rw [hdu]
  ring
end Formalism.LFunctionChainParameters.UnitWeightPartition
