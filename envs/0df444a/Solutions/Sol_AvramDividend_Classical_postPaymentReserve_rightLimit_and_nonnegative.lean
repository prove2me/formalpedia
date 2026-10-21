-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_rightLimit_and_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:48:50.533929+00:00
-- url     : https://prove2.me/submissions/397cf2ee-d6e9-46f4-9853-1e4886e32d4c

import Mathlib
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
    Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω) (𝓝[>] t)
      (𝓝 (x + X.X t ω - rightLimit D t ω)) ∧
    ((∀ᶠ s in 𝓝[>] t, 0 ≤ riskProcess X x D s ω) →
      0 ≤ x + X.X t ω - rightLimit D t ω) := by
  have hmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.2.1 ω
  have heq :
      Function.rightLim (fun s : ℝ≥0 => D s ω) t =
        rightLimit D t ω := by
    have hinf :
        Function.rightLim (fun s : ℝ≥0 => D s ω) t =
          sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) :=
      hmono.rightLim_eq_sInf
    unfold rightLimit
    calc
      Function.rightLim (fun s : ℝ≥0 => D s ω) t =
          sInf ((fun s : ℝ≥0 => D s ω) '' Ioi t) := hinf
      _ = ⨅ s : Ioi t, D s.1 ω := by
        simp only [iInf, Set.image_eq_range]
  have hDlim : Tendsto (fun s : ℝ≥0 => D s ω)
      (𝓝[>] t) (𝓝 (rightLimit D t ω)) := by
    have hlim := hmono.tendsto_rightLim t
    rw [heq] at hlim
    exact hlim
  have hXlim : Tendsto (fun s : ℝ≥0 => X.X s ω)
      (𝓝[>] t) (𝓝 (X.X t ω)) :=
    ((X.rightCont ω t).mono Ioi_subset_Ici_self).tendsto
  have hU : Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
      (𝓝[>] t) (𝓝 (x + X.X t ω - rightLimit D t ω)) := by
    dsimp [riskProcess]
    exact (tendsto_const_nhds.add hXlim).sub hDlim
  refine ⟨hU, ?_⟩
  intro hnonneg
  exact isClosed_Ici.mem_of_tendsto hU hnonneg
