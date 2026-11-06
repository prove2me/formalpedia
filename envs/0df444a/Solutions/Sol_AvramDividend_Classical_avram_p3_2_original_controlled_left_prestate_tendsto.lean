-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_controlled_left_prestate_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:45:17.317006+00:00
-- url     : https://prove2.me/submissions/69b58911-6192-419a-a94e-00db0b2ced97

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original controlled source has its predictable left prestate from
the actual Levy left limit and the prepayment dividend value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) (𝓝[<] t)
      (𝓝 (Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t)) := by
  rcases X.leftLim ω t ht with ⟨lX, hXleft⟩
  have hDleft :=
    avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht
  have hSource : Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (𝓝[<] t) (𝓝 (x + lX - D t ω)) :=
    (tendsto_const_nhds.add hXleft).sub hDleft
  haveI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hLimit : Function.leftLim
      (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t =
      x + lX - D t ω := by
    exact leftLim_eq_of_tendsto hSource
  rw [hLimit]
  exact hSource
