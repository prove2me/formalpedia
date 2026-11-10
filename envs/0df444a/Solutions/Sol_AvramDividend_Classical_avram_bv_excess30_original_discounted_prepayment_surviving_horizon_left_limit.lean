-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:02:23.896405+00:00
-- url     : https://prove2.me/submissions/0848829f-fbdc-4059-9b49-1f27e7535024

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original surviving deterministic horizon is reached from the strict left in prepayment value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ((T : ℝ≥0∞) < ruinTime X x D ω) →
      Filter.Tendsto
        (fun s : ℝ≥0 =>
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω))
        (𝓝[<] T)
        (𝓝 (Real.exp (-(q * (T : ℝ))) *
          w (riskProcess X x D T ω)))  := by
  filter_upwards [avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
    X T hT] with ω hNo
  intro hstop
  have hXeq :
      X.X T ω = Function.leftLim (fun s : ℝ≥0 => X.X s ω) T :=
    sub_eq_zero.mp hNo
  have hXlim :
      Tendsto (fun s : ℝ≥0 => X.X s ω)
        (𝓝[<] T) (𝓝 (X.X T ω)) := by
    simpa only [hXeq] using
      (tendsto_leftLim_of_tendsto (X.leftLim ω T hT))
  have hDlim :
      Tendsto (fun s : ℝ≥0 => D s ω)
        (𝓝[<] T) (𝓝 (D T ω)) := by
    exact (hD.2.2.1 ω T).mono Set.Iio_subset_Iic_self
  have hRisk :
      Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
        (𝓝[<] T) (𝓝 (riskProcess X x D T ω)) := by
    simpa only [riskProcess] using
      (tendsto_const_nhds.add hXlim).sub hDlim
  have hNon : 0 ≤ riskProcess X x D T ω :=
    riskProcess_nonneg_before_ruin X x D ω T hstop
  have hNear : ∀ᶠ s : ℝ≥0 in (𝓝[<] T),
      0 ≤ riskProcess X x D s ω := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hlt : (s : ℝ≥0∞) < (T : ℝ≥0∞) := by
      exact_mod_cast hs
    exact riskProcess_nonneg_before_ruin X x D ω s (hlt.trans hstop)
  have hRiskWithin :
      Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
        (𝓝[<] T) (𝓝[Ici 0] (riskProcess X x D T ω)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨hRisk, hNear⟩
  have hwAt : ContinuousWithinAt w (Ici 0)
      (riskProcess X x D T ω) :=
    hw (riskProcess X x D T ω) (Set.mem_Ici.mpr hNon)
  have hW : Tendsto (fun s : ℝ≥0 => w (riskProcess X x D s ω))
      (𝓝[<] T) (𝓝 (w (riskProcess X x D T ω))) :=
    hwAt.tendsto.comp hRiskWithin
  have hc : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) := by
    fun_prop
  have he : Tendsto (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))))
      (𝓝[<] T) (𝓝 (Real.exp (-(q * (T : ℝ))))) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact he.mul hW