-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_controlled_left_prestate_explicit_source_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:06:17.934028+00:00
-- url     : https://prove2.me/submissions/fb68a05c-ec51-4086-878e-baa69f6ca7dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Explicit original controlled prestate at a positive predictable left jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (lX : ℝ)
    (hXleft : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 lX)) :
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + lX - D t ω := by
  have hDleft :=
    avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht
  haveI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  exact leftLim_eq_of_tendsto
    ((tendsto_const_nhds.add hXleft).sub hDleft)
