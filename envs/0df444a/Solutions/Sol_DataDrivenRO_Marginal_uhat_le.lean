-- Prove2me | solution 1 for DataDrivenRO.Marginal.uhat_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:07:45.325983+00:00
-- url     : https://prove2.me/submissions/2f77e9a7-0d8c-429a-8ba6-f5d443890e94

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

open DataDrivenRO.Marginal in
theorem solution {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ) (i : Fin d) :
    uhat S lo hi i (N + 1 - sIndex N d ε α) ≤ uhat S lo hi i (sIndex N d ε α) := by
  generalize sIndex N d ε α = s at hs ⊢
  unfold uhat
  by_cases ha : N + 1 - s = 0
  · have hb0 : s ≠ 0 := by omega
    have hb : N < s := by omega
    rw [dif_pos ha, dif_neg hb0, dif_pos hb]
    exact hlohi i
  · have hb0 : s ≠ 0 := by omega
    have hb : ¬ N < s := by omega
    have ha' : ¬ N < N + 1 - s := by omega
    rw [dif_neg ha, dif_neg ha', dif_neg hb0, dif_neg hb]
    unfold orderStat
    apply Tuple.monotone_sort
    show N + 1 - s - 1 ≤ s - 1
    omega
