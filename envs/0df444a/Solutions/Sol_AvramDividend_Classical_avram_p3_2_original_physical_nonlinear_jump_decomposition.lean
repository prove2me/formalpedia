-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_nonlinear_jump_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:28:15.10046+00:00
-- url     : https://prove2.me/submissions/4e459b33-bc8d-4c95-8eb1-6fd8dd0a7da3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_simultaneous_nonlinear_jump_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact physical C1 jump decomposition at the original controlled
prestate: the Lévy jump occurs first, then the right-dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    w (x + X.X t ω - rightLimit D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) =
      (w (x + X.X t ω - D t ω) -
        w (x + Function.leftLim
          (fun s : ℝ≥0 => X.X s ω) t - D t ω)) +
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω)) := by
  rw [avram_p3_2_original_controlled_left_prestate_explicit_source_eq
    X x D hD ω t ht
    (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
    ((avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 t)]
  exact avram_p3_2_original_simultaneous_nonlinear_jump_split
    X x D w ω t (Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)
