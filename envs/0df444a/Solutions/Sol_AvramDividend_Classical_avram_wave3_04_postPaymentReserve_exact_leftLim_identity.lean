-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_exact_leftLim_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:04:02.412782+00:00
-- url     : https://prove2.me/submissions/2fd1ee5d-98ad-45ae-9f23-1a625d5c4918

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original-law left-limit reserve: at positive times the left
limit of the post-payment surplus uses X's strict left limit and D(t). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω := by
  letI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  obtain ⟨u, hu⟩ := X.leftLim ω t ht
  have huX : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = u :=
    leftLim_eq_of_tendsto hu
  have hDleft := avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht
  have hU : Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (𝓝[<] t) (𝓝 (x + u - D t ω)) := by
    convert (tendsto_const_nhds.add hu).sub hDleft using 1
  have huU : Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        x + u - D t ω :=
    leftLim_eq_of_tendsto hU
  rw [huU, huX]
