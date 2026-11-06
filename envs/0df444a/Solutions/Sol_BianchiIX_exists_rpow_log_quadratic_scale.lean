-- Prove2me | solution 1 for BianchiIX.exists_rpow_log_quadratic_scale
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:03:23.474171+00:00
-- url     : https://prove2.me/submissions/4c4d72f4-cd4d-4825-8ad1-992b062d67f7

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


/-- Any strictly higher wall power absorbs the logarithmic radial response at the tail endpoint. -/
theorem solution {p : ℝ} (hp : 2 < p) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ a ^ p ≤ a ^ 2 ∧ a ^ p * (1 + |Real.log a|) ≤ a ^ 2 := by
  have he : 0 < p - 2 := by linarith only [hp]
  have HP : Tendsto (fun a : ℝ => a ^ (p - 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow he.ne'] using
      (Real.continuousAt_rpow_const 0 (p - 2) (Or.inr he.le)).tendsto.mono_left nhdsWithin_le_nhds
  have HL := tendsto_log_mul_rpow_nhdsGT_zero he
  have HS : Tendsto (fun a : ℝ => a ^ (p - 2) + |Real.log a * a ^ (p - 2)|)
      (𝓝[>] 0) (𝓝 0) := by simpa only [abs_zero, add_zero] using HP.add HL.abs
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HE : ∀ᶠ a : ℝ in 𝓝[>] 0, a ≤ 1 ∧ a ^ (p - 2) * (1 + |Real.log a|) ≤ 1 := by
    filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin,
      HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      HS.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a ha ha1 hs
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le _)] at hs
    exact ⟨ha1.le, by nlinarith only [hs]⟩
  obtain ⟨astar, hastar, HA⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp HE
  refine ⟨astar, hastar, ?_⟩
  intro a ha
  obtain ⟨ha1, H⟩ := HA ha
  have hid : a ^ p = a ^ 2 * a ^ (p - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_add ha.1]
    congr 1
    ring
  have HB : a ^ p * (1 + |Real.log a|) ≤ a ^ 2 := by
    rw [hid]
    nlinarith only [mul_le_mul_of_nonneg_left H (sq_nonneg a)]
  refine ⟨ha1, ?_, HB⟩
  nlinarith only [HB, mul_nonneg (Real.rpow_nonneg ha.1.le p) (abs_nonneg (Real.log a))]
