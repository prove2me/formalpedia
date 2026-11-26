-- Prove2me | solution 1 for FirstPassageLinearTransport.TwoRegimeRankTrace.elapsed_add_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:45:45.643413+00:00
-- url     : https://prove2.me/submissions/cd1341d9-be67-48c7-8944-19d7ead02e30

import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Theorems.Thm_FirstPassageLinearTransport_twoRegimeClockPotential_step

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
namespace TwoRegimeRankTrace
theorem _root_.solution
    {rHi rLo : ℝ} {S M elapsed q : ℕ}
    (hrHi0 : 0 ≤ rHi) (hrHi1 : rHi < 1)
    (hrLo1 : rLo < 1)
    (htrace : TwoRegimeRankTrace rHi rLo S M elapsed q) :
    (elapsed : ℝ) + twoRegimeClockPotential rHi rLo S q ≤
      (M : ℝ) / (1 - rHi) + (S : ℝ) / (1 - rLo) := by
  induction htrace with
  | @first h q hhM hq =>
      have hdHi : 0 < 1 - rHi := sub_pos.mpr hrHi1
      have hdLo : 0 < 1 - rLo := sub_pos.mpr hrLo1
      have hhMR : (h : ℝ) ≤ (M : ℝ) := by exact_mod_cast hhM
      by_cases hqHigh : S ≤ q
      · unfold twoRegimeClockPotential
        rw [if_pos hqHigh]
        have hlocal : (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
            (M : ℝ) / (1 - rHi) := by
          calc
            (h : ℝ) + (q : ℝ) / (1 - rHi) ≤
                (M : ℝ) + (rHi * (M : ℝ)) / (1 - rHi) :=
              add_le_add hhMR ((div_le_div_iff_of_pos_right hdHi).2 hq)
            _ = (M : ℝ) / (1 - rHi) := by
              field_simp [hdHi.ne']
              ring
        linarith
      · unfold twoRegimeClockPotential
        rw [if_neg hqHigh]
        have htime : (h : ℝ) ≤ (M : ℝ) / (1 - rHi) := by
          have hMdiv : (M : ℝ) ≤ (M : ℝ) / (1 - rHi) := by
            apply (le_div_iff₀ hdHi).2
            nlinarith [show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M]
          exact hhMR.trans hMdiv
        have hqS : (q : ℝ) / (1 - rLo) ≤
            (S : ℝ) / (1 - rLo) :=
          (div_le_div_iff_of_pos_right hdLo).2 (by
            exact_mod_cast (Nat.lt_of_not_ge hqHigh).le)
        linarith
  | @next elapsed qPrev m h q htrace hmPrev hhm hq ih =>
      have hstep := twoRegimeClockPotential_step
        hrHi0 hrHi1 hrLo1 hmPrev hhm hq
      push_cast
      linarith
end TwoRegimeRankTrace
end FirstPassageLinearTransport
