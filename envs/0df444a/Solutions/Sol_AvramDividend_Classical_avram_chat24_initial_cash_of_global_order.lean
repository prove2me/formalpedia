-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_initial_cash_of_global_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:13:44.464304+00:00
-- url     : https://prove2.me/submissions/84a4e62d-8908-455b-b0a9-ba9322c75e8a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_positive_ruin_compensated_prefix_limit_public
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_zero_clock_cash_and_kernels_public
import Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_positive_gradient_global_order
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (w : ℝ → ℝ) (hm : MonotoneOn w (Ici 0)) (hn : ∀ y, 0 ≤ w y)
    (x : ℝ) (hx : 0 ≤ x) (δ : ℝ) (hδ : 0 ≤ δ) (d : ℝ)
    (hd : d ≤ w x - w (x - d)) : d ≤ w (x + δ) := by
  have hwx := hm hx (show 0 ≤ x + δ by linarith) (show x ≤ x + δ by linarith)
  have hwpost := hn (x - d)
  linarith
end
