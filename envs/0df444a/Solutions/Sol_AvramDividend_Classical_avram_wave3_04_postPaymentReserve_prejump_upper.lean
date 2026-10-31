-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_postPaymentReserve_prejump_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:35:20.846846+00:00
-- url     : https://prove2.me/submissions/61f7602a-f387-418d-b86e-704a7aa9e380

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The controlled càdlàg reserve has an exact left limit and the
pre-payment reserve after a spectrally negative jump lies below it. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ l : ℝ,
      Tendsto
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l) ∧
      x + X.X t ω - D t ω ≤ l := by
  obtain ⟨u, hu⟩ := X.leftLim ω t ht
  refine ⟨x + u - D t ω, ?_, ?_⟩
  · have hDleft := avram_wave3_04_rightLimit_leftLimit_eq_dividend
      D hD ω t ht
    convert (tendsto_const_nhds.add hu).sub hDleft using 1
  · have hno := X.noPosJumps ω t u ht hu
    linarith
