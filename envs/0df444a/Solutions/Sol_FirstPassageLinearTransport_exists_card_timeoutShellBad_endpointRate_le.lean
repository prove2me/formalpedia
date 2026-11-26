-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_card_timeoutShellBad_endpointRate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:53.814214+00:00
-- url     : https://prove2.me/submissions/6bb12292-84cd-4081-a973-fc7f27862744

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_exists_timeoutOddEntropyRate_ge_endpoint_sub_div
import Theorems.Thm_FirstPassageLinearTransport_exists_card_timeoutShellBad_sharp_le

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ L m : ℕ,
        0 < L → L ≤ m →
        0 ≤ movingLowRatio K₀ L → movingLowRatio K₀ L ≤ 1 →
        2 * timeoutDisplacementLoss K₀ ≤
          firstPassageEndpointDisplacement * (L : ℝ) →
        ((timeoutShellBad K₀ L m).card : ℝ) / (2 : ℝ) ^ m ≤
          (C / Real.sqrt m) *
            Real.exp (-((m : ℝ) *
              (firstPassageEndpointRate - D / (L : ℝ)))) := by
  obtain ⟨C, hC, hsharp⟩ := exists_card_timeoutShellBad_sharp_le
  obtain ⟨D, hD, hrate⟩ :=
    exists_timeoutOddEntropyRate_ge_endpoint_sub_div hK₀
  refine ⟨C, D, hC, hD, ?_⟩
  intro L m hL hLm hr0 hr1 hscale
  have hm : 0 < m := hL.trans_le hLm
  have hfirst := hsharp K₀ L m hK₀ hL hLm hr0 hr1 hscale
  have hrate' := hrate L m hL hLm hr0 hr1 hscale
  have hexp :
      Real.exp (-((m : ℝ) * timeoutOddEntropyRate K₀ L m)) ≤
        Real.exp (-((m : ℝ) *
          (firstPassageEndpointRate - D / (L : ℝ)))) := by
    apply Real.exp_le_exp.2
    have hmR : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  exact hfirst.trans
    (mul_le_mul_of_nonneg_left hexp (div_nonneg hC.le (Real.sqrt_nonneg _)))
end FirstPassageLinearTransport
