-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellMaximalParityBad_le_concrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:25.349247+00:00
-- url     : https://prove2.me/submissions/048f1730-21ac-4020-88b4-5f79eddae0d3

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_card_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_le
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_pos
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrierHeight_nonneg


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ((shellMaximalParityBad M (maximalBarrierHeight t M)).card : ℝ) ≤
      2 * Real.exp (-(maximalBarrierC0 * t ^ 2 * M)) *
        (2 : ℝ) ^ M := by
  classical
  cases M with
  | zero =>
      have hcard :
          (shellMaximalParityBad 0 (maximalBarrierHeight t 0)).card ≤ 1 := by
        calc
          _ ≤ (dyadicShell 0).card := by
            apply Finset.card_le_card
            intro n hn
            exact (Finset.mem_filter.mp hn).1
          _ = 1 := by norm_num [card_dyadicShell]
      have hcardR :
          ((shellMaximalParityBad 0
            (maximalBarrierHeight t 0)).card : ℝ) ≤ 1 := by
        exact_mod_cast hcard
      norm_num at hcardR ⊢
      linarith
  | succ M =>
      have hraw := card_shellMaximalParityBad_le
        (M := M + 1) (h := maximalBarrierHeight t (M + 1))
        (maximalBarrierHeight_nonneg ht) (Nat.succ_pos M)
      have hlog : logTwoThree ≠ 0 := ne_of_gt logTwoThree_pos
      have hexp :
          -(2 * maximalBarrierHeight t (M + 1) ^ 2 /
              ((M + 1 : ℕ) : ℝ)) =
            -(maximalBarrierC0 * t ^ 2 * ((M + 1 : ℕ) : ℝ)) := by
        unfold maximalBarrierHeight maximalBarrierC0
        have hM : (0 : ℝ) < M + 1 := by positivity
        field_simp [hlog]
      calc
        ((shellMaximalParityBad (M + 1)
          (maximalBarrierHeight t (M + 1))).card : ℝ) ≤
            (2 : ℝ) ^ (M + 1 + 1) *
              Real.exp (-(2 * maximalBarrierHeight t (M + 1) ^ 2 /
                ((M + 1 : ℕ) : ℝ))) := hraw
        _ = 2 * Real.exp
              (-(maximalBarrierC0 * t ^ 2 * ((M + 1 : ℕ) : ℝ))) *
              (2 : ℝ) ^ (M + 1) := by
          rw [hexp, pow_succ]
          ring
end FirstPassageLinearTransport
