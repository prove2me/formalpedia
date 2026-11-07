-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_turn16_factorised_ode_upper_exponential_comparison_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:25:36.187389+00:00
-- url     : https://prove2.me/submissions/975bc197-ff7c-4b99-b50a-e010f28ae279

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_positive_ray_growth
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_compact_interval_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn17_ray_compact_glue
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (rpos rneg : ℝ) (hrpos : 0 < rpos) (hrneg : rneg < 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hODE : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      iteratedDeriv 2 w y - (rpos + rneg) * deriv w y + rpos * rneg * w y ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, w y ≤ K * Real.exp (rpos * y) := by
  obtain ⟨K, hK, hRay⟩ :=
    AvramDividend.Classical.avram_p4_f4_turn17_positive_ray_growth
      rpos rneg hrpos hrneg w C hTop hw0 hw_cont hw_neg hw_smooth hODE
  obtain ⟨M, hM, hCompact⟩ :=
    AvramDividend.Classical.avram_p4_f4_turn17_compact_interval_bound
      w hw_cont
  exact AvramDividend.Classical.avram_p4_f4_turn17_ray_compact_glue
    rpos (le_of_lt hrpos) w hw_neg K M hK hM hRay hCompact
