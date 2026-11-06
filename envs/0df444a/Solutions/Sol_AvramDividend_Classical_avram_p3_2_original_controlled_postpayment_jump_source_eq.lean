-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_controlled_postpayment_jump_source_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:56:24.230123+00:00
-- url     : https://prove2.me/submissions/d24b4eeb-21f1-4eb5-b218-dd64043b31e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original simultaneous Lévy and dividend jump at positive time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (lX : ℝ)
    (hXleft : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 lX)) :
    (x + X.X t ω - rightLimit D t ω) -
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      (X.X t ω - lX) - (rightLimit D t ω - D t ω) := by
  rw [avram_p3_2_original_controlled_left_prestate_explicit_source_eq
    X x D hD ω t ht lX hXleft]
  ring
