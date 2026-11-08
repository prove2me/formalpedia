-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_mark_allpath_positive_ruin_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:57:12.617203+00:00
-- url     : https://prove2.me/submissions/d1b415c7-aafe-4fde-8967-7b25f343ef54

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_local_reserve_of_continuity_nonnegative_mark
import Theorems.Thm_AvramDividend_Classical_avram_e0_ruinTime_positive_of_local_nonnegative_reserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Every path has a positive local survival interval after an affordable initial payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKstrict : ∀ ω, K ω < x)
    (hzero : ∀ ω, X.X 0 ω = 0)
    (hcont : ∀ ω, ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0) :
    ∀ ω, (0 : ℝ≥0∞) <
      ruinTime X x (fun t η => if t = 0 then 0 else K η) ω := by
  intro ω
  obtain ⟨δ, hδ, hlocal⟩ :=
    avram_e0_initial_step_local_reserve_of_continuity_nonnegative_mark
      X x K ω (hKnonneg ω) (hzero ω) (hcont ω) (hKstrict ω)
  exact avram_e0_ruinTime_positive_of_local_nonnegative_reserve
    X x (fun t η => if t = 0 then 0 else K η) ω δ hδ hlocal
