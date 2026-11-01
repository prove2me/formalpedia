-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_original_prepost_reserve_same_leftlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:23:28.383324+00:00
-- url     : https://prove2.me/submissions/3b38c9b4-1ecb-4299-917b-606dac96cec8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Function.leftLim
        (fun s : ℝ≥0 => riskProcess X x D s ω) t =
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t := by
  letI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  obtain ⟨u, hu⟩ := X.leftLim ω t ht
  have huX : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = u :=
    leftLim_eq_of_tendsto hu
  have hfilter : (𝓝[<] t) ≤ (𝓝[Iic t] t) :=
    nhdsWithin_mono t (by intro s hs; exact le_of_lt (Set.mem_Iio.mp hs))
  have hDleft : Tendsto (fun s : ℝ≥0 => D s ω)
      (𝓝[<] t) (𝓝 (D t ω)) :=
    (hD.2.2.1 ω t).mono_left hfilter
  have hRisk : Tendsto
      (fun s : ℝ≥0 => riskProcess X x D s ω)
      (𝓝[<] t) (𝓝 (x + u - D t ω)) := by
    change Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - D s ω)
      (𝓝[<] t) (𝓝 (x + u - D t ω))
    convert (tendsto_const_nhds.add hu).sub hDleft using 1
  have hRiskLim :
      Function.leftLim
          (fun s : ℝ≥0 => riskProcess X x D s ω) t =
        x + u - D t ω :=
    leftLim_eq_of_tendsto hRisk
  rw [hRiskLim,
    avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD ω t ht, huX]