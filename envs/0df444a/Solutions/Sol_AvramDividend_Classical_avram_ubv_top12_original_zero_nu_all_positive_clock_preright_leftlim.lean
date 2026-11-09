-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_zero_nu_all_positive_clock_preright_leftlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:41:21.755075+00:00
-- url     : https://prove2.me/submissions/5a88e4ae-dab0-48df-a177-b29f0478b5e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Global zero-jump continuity permits left-contact at every positive
    random clock on one original-measure full-measure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
        riskProcess X x D t ω := by
  filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν] with ω hXcont
  intro t ht
  have hXlim :
      Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 (X.X t ω)) :=
    hXcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hDlim :
      Tendsto (fun s : ℝ≥0 => D s ω) (𝓝[<] t) (𝓝 (D t ω)) :=
    (hD.2.2.1 ω t).mono Set.Iio_subset_Iic_self
  have hUlim :
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - D s ω)
        (𝓝[<] t) (𝓝 (x + X.X t ω - D t ω)) :=
    (tendsto_const_nhds.add hXlim).sub hDlim
  haveI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  simpa only [riskProcess] using (leftLim_eq_of_tendsto hUlim)
