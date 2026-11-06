-- Prove2me | solution 1 for BianchiIX.exists_shearTail_variation_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:52:08.6192+00:00
-- url     : https://prove2.me/submissions/95f1a12f-4ca7-4676-96c3-067472d1cb4b

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


/-- Linear moment bounds and the sharp logarithmic entrance response admit one common scale. -/
theorem solution {C q D P : ℝ}
    (hC : 0 ≤ C) (hq : 2 < q) (hP : 6 * D + 2 < P) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 / 256 ∧ 2 * a ^ (P - 6 * D - 2) ≤ 1 ∧
      ∀ L₀ J₀ J₁ : ℝ, L₀ ≤ 2 + 4 * C * q * |Real.log a| → 0 ≤ J₀ →
        J₀ ≤ 4 * a → J₁ ≤ 1 / 256 + (2 + D) * a →
        9 * J₀ ≤ Real.log 2 ∧ 2 * J₀ + 16 * J₁ ≤ 1 / 2 ∧ L₀ * J₀ ≤ 1 / 16 := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hp : 0 < P - 6 * D - 2 := by linarith only [hP]
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HP : Tendsto (fun a : ℝ => 2 * a ^ (P - 6 * D - 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne', mul_zero] using
      (((Real.continuousAt_rpow_const 0 (P - 6 * D - 2) (Or.inr hp.le)).tendsto.const_mul 2).mono_left nhdsWithin_le_nhds)
  have H0 : Tendsto (fun a : ℝ => 36 * a) (𝓝[>] 0) (𝓝 0) := by simpa using HI.const_mul 36
  have H1 : Tendsto (fun a : ℝ => (40 + 16 * D) * a) (𝓝[>] 0) (𝓝 0) := by simpa using HI.const_mul (40 + 16 * D)
  have Hlog : Tendsto (fun a : ℝ => 8 * a + 16 * C * q * |a * Real.log a|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, abs_zero, add_zero] using (HI.const_mul 8).add (HL.abs.const_mul (16 * C * q))
  have HE : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (0 < a ∧ a ≤ 1 / 256) ∧ 2 * a ^ (P - 6 * D - 2) ≤ 1 ∧
      36 * a ≤ Real.log 2 ∧ (40 + 16 * D) * a ≤ 1 / 4 ∧
      8 * a + 16 * C * q * |a * Real.log a| ≤ 1 / 16 := by
    filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from self_mem_nhdsWithin,
      HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 256)),
      HP.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      H0.eventually (gt_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
      H1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      Hlog.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))] with a ha ha1 hpow h0 h1 hl
    exact ⟨⟨ha, ha1.le⟩, hpow.le, h0.le, h1.le, hl.le⟩
  obtain ⟨astar, hastar, HA⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp HE
  refine ⟨astar, hastar, ?_⟩
  intro a ha
  obtain ⟨ha', hpow, h0, h1, hl⟩ := HA ha
  refine ⟨ha'.2, hpow, ?_⟩
  intro L₀ J₀ J₁ hL hJ₀ hJ0 hJ1
  refine ⟨by linarith only [h0, hJ0], by nlinarith only [h1, hJ0, hJ1], ?_⟩
  have H := mul_le_mul hL hJ0 hJ₀ (by positivity : 0 ≤ 2 + 4 * C * q * |Real.log a|)
  have Hid : (2 + 4 * C * q * |Real.log a|) * (4 * a) = 8 * a + 16 * C * q * |a * Real.log a| := by
    rw [abs_mul, abs_of_pos ha.1]
    ring
  exact H.trans (Hid ▸ hl)
