-- Prove2me | solution 1 for AvramDividend.Classical.avram_a34_original_finitecap_zero_contact_one_sided_caplinear_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:11:31.237626+00:00
-- url     : https://prove2.me/submissions/060ae7a1-f545-4b18-a192-a6923ad49d0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a32_compact_translation_vanishing_radius
open Set Filter AvramDividend.Classical
theorem solution
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw0 : 0 ≤ w 0)
    (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y δ : ℕ → ℝ)
    (hy : ∀ m, y m ∈ Set.Icc 0 b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    Tendsto (fun m => max (V (y m + δ m) - V (y m)) 0)
      atTop (nhds (0 : ℝ))  := by
  dsimp
  let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
  let U : ℝ → ℝ := fun z => V (max z 0)
  have hUC : UniformContinuousOn V (Icc 0 (b + 1)) := by
    simpa only [V] using
      (avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
        w hwcont b (b + 1) hb)
  have hMap : MapsTo (fun z : ℝ => max z 0)
      (Icc ((0 : ℝ) - 1) (b + 1)) (Icc 0 (b + 1)) := by
    intro z hz
    refine ⟨le_max_right _ _, ?_⟩
    exact max_le (le_trans hz.2 le_rfl) (by linarith)
  have hU : ContinuousOn U (Icc ((0 : ℝ) - 1) (b + 1)) := by
    exact hUC.continuousOn.comp
      ((continuous_id.max continuous_const).continuousOn) hMap
  have hT := avram_ga_a32_compact_translation_vanishing_radius
    U 0 b 1 (by norm_num) hU y δ hy hδ
  have hT' : Tendsto
      (fun m => V (max (y m + δ m) 0) - V (y m))
      atTop (nhds (0 : ℝ)) := by
    convert hT using 1
    funext m
    simp only [U]
    rw [max_eq_left (hy m).1]
  have hMax : Continuous (fun z : ℝ => max z 0) :=
    continuous_id.max continuous_const
  have hTpos : Tendsto
      (fun m => max (V (max (y m + δ m) 0) - V (y m)) 0)
      atTop (nhds (0 : ℝ)) := by
    have ht := hMax.continuousAt.tendsto.comp hT'
    simpa [Function.comp_def] using ht
  have hCompare (m : ℕ) :
      V (y m + δ m) ≤ V (max (y m + δ m) 0) := by
    by_cases hz : y m + δ m < 0
    · have hzb : y m + δ m ≤ b := (le_of_lt hz).trans hb
      have hval : V (y m + δ m) = 0 := by
        simp [V, hzb, hwneg _ hz]
      have hmax : max (y m + δ m) 0 = 0 :=
        max_eq_right (le_of_lt hz)
      have hzero : V 0 = w 0 := by simp [V, hb]
      rw [hval, hmax, hzero]
      exact hw0
    · rw [max_eq_left (le_of_not_gt hz)]
  have hLow (m : ℕ) :
      0 ≤ max (V (y m + δ m) - V (y m)) 0 :=
    le_max_right _ _
  have hHigh (m : ℕ) :
      max (V (y m + δ m) - V (y m)) 0 ≤
        max (V (max (y m + δ m) 0) - V (y m)) 0 := by
    exact max_le_max
      (sub_le_sub_right (hCompare m) (V (y m))) le_rfl
  exact squeeze_zero hLow hHigh hTpos
