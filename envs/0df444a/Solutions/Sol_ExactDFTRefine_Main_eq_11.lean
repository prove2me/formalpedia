-- Prove2me | solution 1 for ExactDFTRefine.Main.eq_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:12:07.549893+00:00
-- url     : https://prove2.me/submissions/49634ad0-ed69-4deb-8cd5-a6604f9fab3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments
import Theorems.Thm_ExactDFTRefine_Main_eq_8_9
import Theorems.Thm_ExactDFTRefine_Main_eq_2

open ExactDFTRefine.Main

theorem solution :
    (239134 : ℝ) ≤ gam * (145 * Lbound / Ebound) ∧
    (10928 : ℝ) * 21 ≤ eta * (145 * Lbound / Ebound) ∧
    moment 1 blocksP / ((20 : ℝ) ^ Cpar * moment tpar targetsT) ≤ gam ∧
    21 * (Multiset.card targetsT : ℝ) / ((20 : ℝ) ^ Cpar * moment tpar targetsT) ≤ eta := by
  obtain ⟨hE, hid, hQ⟩ := eq_8_9
  obtain ⟨hP, hT, hcard⟩ := eq_2
  have hR : 0 < (145 : ℝ) * Lbound / Ebound := by
    norm_num [Lbound, Ebound]
  have hQpos : 0 < (20 : ℝ) ^ Cpar * moment tpar targetsT := lt_of_lt_of_le hR hQ
  have hgam : 0 ≤ gam := by norm_num [gam]
  have heta : 0 ≤ eta := by norm_num [eta]
  have hratP : (239134 : ℝ) ≤ gam * (145 * Lbound / Ebound) := by
    norm_num [gam, Lbound, Ebound]
  have hratT : (10928 : ℝ) * 21 ≤ eta * (145 * Lbound / Ebound) := by
    norm_num [eta, Lbound, Ebound]
  refine ⟨hratP, hratT, ?_, ?_⟩
  · rw [hP]
    exact (div_le_iff₀ hQpos).2
      (le_trans hratP (mul_le_mul_of_nonneg_left hQ hgam))
  · rw [hcard]
    push_cast
    exact (div_le_iff₀ hQpos).2 (by
      simpa [mul_comm] using
        (le_trans hratT (mul_le_mul_of_nonneg_left hQ heta)))
