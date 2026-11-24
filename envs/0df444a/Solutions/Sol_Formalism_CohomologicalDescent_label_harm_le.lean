-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_harm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:53.057076+00:00
-- url     : https://prove2.me/submissions/4ce29ccf-8495-423e-b4a2-6f90cba0e711

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {l h : ℕ} (hl0 : 0 < l) (hlh : l ≤ 2 * h) :
    ((harmonic (h / l) : ℚ) : ℝ) ≤ 1 + Real.log ((h : ℝ) / (l : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast hl0
  have hhR : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rcases Nat.eq_zero_or_pos (h / l) with h0 | hpos
  · rw [h0, harmonic_zero, Rat.cast_zero]
    have hx : (0 : ℝ) < (h : ℝ) / l := div_pos hhR hl
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    have hinv : ((h : ℝ) / l)⁻¹ ≤ 2 := by
      rw [inv_div, div_le_iff₀ hhR]
      exact_mod_cast hlh
    linarith
  · have h1 := harmonic_le_one_add_log (h / l)
    have h2 : Real.log ((h / l : ℕ) : ℝ) ≤ Real.log ((h : ℝ) / l) :=
      Real.log_le_log (by exact_mod_cast hpos) Nat.cast_div_le
    linarith
end Formalism.CohomologicalDescent
