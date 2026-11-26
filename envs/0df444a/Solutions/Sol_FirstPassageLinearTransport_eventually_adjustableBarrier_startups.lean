-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_adjustableBarrier_startups
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:41.393841+00:00
-- url     : https://prove2.me/submissions/301b7974-9629-445d-927d-0d701dae9838

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {lambda t : ℝ} (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ M : ℕ in atTop,
      1 ≤ (1 - lambda) * t * (M : ℝ) ∧
        2 * (2 + Real.sqrt 3) ≤
          (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ)) := by
  have hmainGap : 0 < (1 - lambda) * t :=
    mul_pos (sub_pos.mpr hlambda1) ht0
  have hlambdaMul : lambda * t ≤ t := by
    have := mul_le_mul_of_nonneg_right hlambda1.le ht0.le
    simpa using this
  have hcorrGap : 0 < a0 + t - 2 * lambda * t := by
    nlinarith
  have hmainTendsto :
      Tendsto (fun M : ℕ => (1 - lambda) * t * (M : ℝ)) atTop atTop := by
    simpa [mul_assoc] using
      tendsto_natCast_atTop_atTop.const_mul_atTop hmainGap
  have hcorrExponentTendsto :
      Tendsto (fun M : ℕ =>
        (a0 + t - 2 * lambda * t) * (M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hcorrGap
  have hcorrTendsto :
      Tendsto (fun M : ℕ =>
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) atTop atTop :=
    by
      have hlogTendsto :
          Tendsto (fun M : ℕ =>
            Real.log 2 * ((a0 + t - 2 * lambda * t) * (M : ℝ)))
            atTop atTop :=
        hcorrExponentTendsto.const_mul_atTop
          (Real.log_pos (by norm_num))
      have hexp := Real.tendsto_exp_atTop.comp hlogTendsto
      exact hexp.congr' (Eventually.of_forall fun M => by
        simp [Function.comp_def,
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)])
  obtain ⟨Mmain, hMmain⟩ := tendsto_atTop_atTop.mp hmainTendsto 1
  obtain ⟨Mcorr, hMcorr⟩ := tendsto_atTop_atTop.mp hcorrTendsto
    (2 * (2 + Real.sqrt 3))
  filter_upwards [eventually_ge_atTop (max Mmain Mcorr)] with M hM
  exact ⟨hMmain M (le_trans (Nat.le_max_left _ _) hM),
    hMcorr M (le_trans (Nat.le_max_right _ _) hM)⟩
end FirstPassageLinearTransport
