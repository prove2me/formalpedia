-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp23_original_ubv_prepayment_leftlim_le_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:47:56.849955+00:00
-- url     : https://prove2.me/submissions/35848719-e11f-4219-91c8-8b3433c974d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    ∀ (t : ℝ≥0), t ≤ T → ∀ ω : Ω,
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ≤
        x + runningSup X T ω := by
  intro t ht ω
  let f : ℝ≥0 → ℝ :=
    fun s => x + X.X s ω - rightLimit D s ω
  obtain ⟨hMono, hXle⟩ := runningSup_monotone_and_path_le X ω
  have hBound : ∀ s : ℝ≥0,
      s ≤ T → f s ≤ x + runningSup X T ω := by
    intro s hs
    have hXs : X.X s ω ≤ runningSup X T ω :=
      (hXle s).trans (hMono hs)
    have hDs : 0 ≤ rightLimit D s ω :=
      avram_ga_a35_original_dividend_rightLimit_nonnegative
        D hD s ω
    dsimp [f]
    linarith only [hXs, hDs]
  have hEventually :
      ∀ᶠ s in 𝓝[≤] t,
        f s ∈ Iic (x + runningSup X T ω) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hBound s (hs.trans ht)
  have hCluster :
      MapClusterPt (f.leftLim t) (𝓝[≤] t) f :=
    mapClusterPt_leftLim f t
  have hFinal :
      f.leftLim t ∈ Iic (x + runningSup X T ω) :=
    isClosed_Iic.mem_of_mapClusterPt hCluster hEventually
  exact hFinal
