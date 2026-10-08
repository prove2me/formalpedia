-- Prove2me | solution 1 for BigDataNV.Reg.lemma5_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:00:02.291921+00:00
-- url     : https://prove2.me/submissions/3d6caacb-c245-4e6e-a644-96ffa3e608e4

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

set_option autoImplicit false

open BigDataNV.Reg in
theorem nvCost_eq_4e2b188a (b h q d : ℝ) :
    nvCost b h q d = b * max (d - q) 0 + h * max (q - d) 0 := by
  simp only [nvCost, InventoryControl.newsboyLoss]
  ring

open BigDataNV.Reg in
theorem solution (b h Dbar : ℝ) (hb : 0 < b) (hh : 0 < h) (hD : 0 ≤ Dbar) :
    (∀ q ∈ Set.Icc 0 Dbar, ∀ d ∈ Set.Icc 0 Dbar, |nvCost b h q d| ≤ max b h * Dbar) ∧
    IsGreatest {c : ℝ | ∃ q ∈ Set.Icc 0 Dbar, ∃ d ∈ Set.Icc 0 Dbar, c = |nvCost b h q d|}
      (max b h * Dbar) := by
  have key : ∀ q ∈ Set.Icc 0 Dbar, ∀ d ∈ Set.Icc 0 Dbar, |nvCost b h q d| ≤ max b h * Dbar := by
    rintro q ⟨hq0, hq1⟩ d ⟨hd0, hd1⟩
    have hbm : b ≤ max b h := le_max_left _ _
    have hhm : h ≤ max b h := le_max_right _ _
    rw [nvCost_eq_4e2b188a]
    rcases le_total q d with hqd | hqd
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ d - q), max_eq_right (by linarith : q - d ≤ 0)]
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    · rw [max_eq_right (by linarith : d - q ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ q - d)]
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
  refine ⟨key, ?_, ?_⟩
  · rcases le_total b h with hbh | hbh
    · refine ⟨Dbar, ⟨hD, le_rfl⟩, 0, ⟨le_rfl, hD⟩, ?_⟩
      rw [nvCost_eq_4e2b188a]
      rw [max_eq_right hbh, max_eq_right (by linarith : (0:ℝ) - Dbar ≤ 0), sub_zero,
        max_eq_left hD, abs_of_nonneg (by nlinarith)]
      ring
    · refine ⟨0, ⟨le_rfl, hD⟩, Dbar, ⟨hD, le_rfl⟩, ?_⟩
      rw [nvCost_eq_4e2b188a]
      rw [max_eq_left hbh, max_eq_right (by linarith : (0:ℝ) - Dbar ≤ 0), sub_zero,
        max_eq_left hD, abs_of_nonneg (by nlinarith)]
      ring
  · rintro c ⟨q, hq, d, hd, rfl⟩
    exact key q hq d hd
