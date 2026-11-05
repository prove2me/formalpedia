-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:28:59.823061+00:00
-- url     : https://prove2.me/submissions/b2bcadc0-0455-402c-bb59-05b72b290266

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At a strictly surviving deterministic horizon, the discounted and killed
original prepayment HJB terminal converges from the left. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 =>
        if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω) else 0)
        (𝓝[<] t)
        (𝓝 (Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω))) := by
  filter_upwards [avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
    X D hD x w hw t ht] with ω hW
  intro hSurv
  have hExp : ContinuousAt
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) t := by
    fun_prop
  have hExpLeft : Tendsto
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))))
      (𝓝[<] t) (𝓝 (Real.exp (-(q * (t : ℝ))))) :=
    hExp.tendsto.mono_left nhdsWithin_le_nhds
  have hRaw := hExpLeft.mul (hW hSurv)
  apply hRaw.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hst : s < t := Set.mem_Iio.mp hs
  have hsSurv : (s : ℝ≥0∞) < ruinTime X x D ω := by
    have hst' : (s : ℝ≥0∞) < (t : ℝ≥0∞) := by exact_mod_cast hst
    exact lt_trans hst' hSurv
  simp [hsSurv]
