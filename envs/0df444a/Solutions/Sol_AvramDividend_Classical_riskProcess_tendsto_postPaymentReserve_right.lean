-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_tendsto_postPaymentReserve_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:53:08.829955+00:00
-- url     : https://prove2.me/submissions/351f7a04-50e9-41ec-8c46-39f6e1c11e0a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
      (𝓝[>] t)
      (𝓝 (x + X.X t ω - rightLimit D t ω)) := by
  have hX : Tendsto (fun s : ℝ≥0 => X.X s ω)
      (𝓝[>] t) (𝓝 (X.X t ω)) :=
    ((X.rightCont ω t).mono Ioi_subset_Ici_self).tendsto
  have hmon : Monotone (fun s : ℝ≥0 => D s ω) :=
    hD.2.1 ω
  have heq : Function.rightLim (fun s : ℝ≥0 => D s ω) t =
      rightLimit D t ω := by
    have hsInf :
        Function.rightLim (fun s : ℝ≥0 => D s ω) t =
          sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) :=
      hmon.rightLim_eq_sInf
    unfold rightLimit
    calc
      Function.rightLim (fun s : ℝ≥0 => D s ω) t =
          sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) := hsInf
      _ = ⨅ s : Ioi t, D s.1 ω := by
        simp only [iInf, Set.image_eq_range]
  have hDlim : Tendsto (fun s : ℝ≥0 => D s ω)
      (𝓝[>] t) (𝓝 (rightLimit D t ω)) := by
    rw [← heq]
    exact hmon.tendsto_rightLim t
  have hconst : Tendsto (fun _ : ℝ≥0 => x)
      (𝓝[>] t) (𝓝 x) := tendsto_const_nhds
  have hsum : Tendsto (fun s : ℝ≥0 => x + X.X s ω)
      (𝓝[>] t) (𝓝 (x + X.X t ω)) := hconst.add hX
  have hsub : Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - D s ω)
      (𝓝[>] t) (𝓝 (x + X.X t ω - rightLimit D t ω)) :=
    hsum.sub hDlim
  simpa only [riskProcess] using hsub
