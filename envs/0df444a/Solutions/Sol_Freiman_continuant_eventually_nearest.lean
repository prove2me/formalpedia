-- Prove2me | solution 1 for Freiman.continuant_eventually_nearest
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:03.978067+00:00
-- url     : https://prove2.me/submissions/c8facea5-4404-439f-ae61-adabb1476851

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_continuant_denominator_escape
import Theorems.Thm_Freiman_integerDistance_of_lt_half
import Theorems.Thm_Freiman_continuant_error_bound

open Freiman

theorem solution (b : ℕ → ℕ+) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      integerDistance ((continuantQ b n : ℝ) * cfValue b) =
      |(continuantQ b n : ℝ) * cfValue b - (continuantP b n : ℝ)| := by
  obtain ⟨N, hN⟩ := continuant_denominator_escape b 3
  refine ⟨N, ?_⟩
  intro n hn
  apply integerDistance_of_lt_half _ (continuantP b n : ℤ)
  have hq : (2:ℝ) < (continuantQ b (n+1):ℝ) := by
    have := hN (n+1) (by omega)
    exact_mod_cast (show 2 < continuantQ b (n+1) by omega)
  exact (continuant_error_bound b n).trans (one_div_lt_one_div_of_lt (by norm_num) hq)
