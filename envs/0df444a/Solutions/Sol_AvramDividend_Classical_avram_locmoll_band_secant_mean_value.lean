-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:41:22.0418+00:00
-- url     : https://prove2.me/submissions/5a625743-6884-42eb-8f10-415329ca27aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (a b : ℝ) (hab : b ≤ a) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    ∃ c ∈ Icc b a, deriv g c = Q a b := by 
  dsimp only
  by_cases he : a = b
  · subst b
    exact ⟨a, ⟨le_rfl, le_rfl⟩, by simp⟩
  · obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope g
      (lt_of_le_of_ne hab (Ne.symm he)) hg.continuous.continuousOn
      (hg.differentiable (by norm_num)).differentiableOn
    exact ⟨c, ⟨hc.1.le, hc.2.le⟩, by simpa only [if_neg he] using heq⟩
