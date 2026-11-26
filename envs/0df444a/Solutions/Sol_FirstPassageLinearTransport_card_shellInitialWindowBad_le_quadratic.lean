-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellInitialWindowBad_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:13.255452+00:00
-- url     : https://prove2.me/submissions/00beeb78-65cc-42ce-b8e2-13e79096bad6

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrierC0_pos
import Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_le_concrete
import Theorems.Thm_FirstPassageLinearTransport_shellInitialWindowBad_subset_maximal
import Theorems.Thm_FirstPassageLinearTransport_one_le_quadratic_startup_factor
import Theorems.Thm_FirstPassageLinearTransport_card_dyadicShell


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((shellInitialWindowBad M t).card : ℝ) ≤
      quadraticWindowShellConstant *
        Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by
  classical
  by_cases hlarge : 4 ≤ M ∧ 2 ≤ t * M
  · have hsubset := shellInitialWindowBad_subset_maximal
      ht0 hlarge.1 hlarge.2
    have hcard :
        (shellInitialWindowBad M t).card ≤
          (shellMaximalParityBad M (maximalBarrierHeight t M)).card :=
      Finset.card_le_card hsubset
    have hcardR :
        ((shellInitialWindowBad M t).card : ℝ) ≤
          ((shellMaximalParityBad M
            (maximalBarrierHeight t M)).card : ℝ) := by exact_mod_cast hcard
    have htail := card_shellMaximalParityBad_le_concrete (M := M) ht0.le
    calc
      _ ≤ ((shellMaximalParityBad M
          (maximalBarrierHeight t M)).card : ℝ) := hcardR
      _ ≤ 2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
          (2 : ℝ) ^ M := htail
      _ ≤ quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
          (2 : ℝ) ^ M := by
        have hK : (2 : ℝ) ≤ quadraticWindowShellConstant := by
          unfold quadraticWindowShellConstant
          have := Real.one_le_exp
            (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
              maximalBarrierC0_pos.le)
          nlinarith
        gcongr
  · have hcard :
        (shellInitialWindowBad M t).card ≤ (dyadicShell M).card := by
      apply Finset.card_le_card
      intro n hn
      exact (Finset.mem_filter.mp hn).1
    have hcardR :
        ((shellInitialWindowBad M t).card : ℝ) ≤ (2 : ℝ) ^ M := by
      rw [card_dyadicShell] at hcard
      exact_mod_cast hcard
    have hfactor := one_le_quadratic_startup_factor ht0 ht1 hlarge
    calc
      _ ≤ (2 : ℝ) ^ M := hcardR
      _ = 1 * (2 : ℝ) ^ M := by ring
      _ ≤ (quadraticWindowShellConstant *
          Real.exp (-(maximalBarrierC0 * t ^ 2 * M))) *
          (2 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring
end FirstPassageLinearTransport
