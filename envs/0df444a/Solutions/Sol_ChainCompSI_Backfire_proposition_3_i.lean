-- Prove2me | solution 1 for ChainCompSI.Backfire.proposition_3_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:25:43.493729+00:00
-- url     : https://prove2.me/submissions/ad08d024-54ce-4014-9fa5-4810d7056a74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ChainCompSI_Backfire_table_1_si

open ChainCompSI.Backfire

theorem solution (θ h h' : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) (hlo : 17 * (4 - θ) / (272 + 136 * θ + 21 * θ ^ 2) ≤ h) (hlt : h < h') (hhi : h' ≤ 1 / (4 + θ)) : (∃ E, IsEq θ h SI E) ∧ (∃ E', IsEq θ h' SI E') ∧ ∀ E E', IsEq θ h SI E → IsEq θ h' SI E' → ∀ i : Fin 2, mfrProfit θ E i < mfrProfit θ E' i := by
  have h4 : (0 : ℝ) < 4 + θ := by linarith
  have hx' : h' * (4 + θ) ≤ 1 := (le_div_iff₀ h4).1 hhi
  have hx : h * (4 + θ) ≤ 1 := by nlinarith
  obtain ⟨ex, hall⟩ := table_1_si θ h hθ hh hx
  obtain ⟨ex', hall'⟩ := table_1_si θ h' hθ (by linarith) hx'
  refine ⟨ex, ex', fun E E' hE hE' i => ?_⟩
  rw [(hall E hE i).2.2.2.2.2.2.2, (hall' E' hE' i).2.2.2.2.2.2.2]
  have hc : 0 < 272 + 136 * θ + 21 * θ ^ 2 := by positivity
  have hL : 17 * (4 - θ) ≤ h * (272 + 136 * θ + 21 * θ ^ 2) := (div_le_iff₀ hc).1 hlo
  have hM : 0 < (68 + 19 * θ) ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_right hM]
  have key : 4 * (1 + θ) * (306 - 34 * h' * (4 - θ) + h' ^ 2 * (272 + θ * (136 + 21 * θ))) -
      4 * (1 + θ) * (306 - 34 * h * (4 - θ) + h ^ 2 * (272 + θ * (136 + 21 * θ))) =
      4 * (1 + θ) * (h' - h) * ((h + h') * (272 + 136 * θ + 21 * θ ^ 2) - 34 * (4 - θ)) := by
    ring
  have hpos : 0 < 4 * (1 + θ) * (h' - h) *
      ((h + h') * (272 + 136 * θ + 21 * θ ^ 2) - 34 * (4 - θ)) := by
    have : 0 < (h + h') * (272 + 136 * θ + 21 * θ ^ 2) - 34 * (4 - θ) := by
      nlinarith [mul_lt_mul_of_pos_right hlt hc]
    have : 0 < h' - h := by linarith
    positivity
  linarith
