-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:07:57.629253+00:00
-- url     : https://prove2.me/submissions/467748ed-fb01-4047-a28b-b4df0d004179

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At a deterministic strictly positive horizon the original controlled
pre-rightpayment reserve has no left jump, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
        riskProcess X x D t ω := by
  filter_upwards [avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
    X t ht] with ω hNo
  have hXeq :
      X.X t ω = Function.leftLim (fun s : ℝ≥0 => X.X s ω) t :=
    sub_eq_zero.mp hNo
  have hXlim :
      Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 (X.X t ω)) := by
    simpa only [hXeq] using
      (tendsto_leftLim_of_tendsto (X.leftLim ω t ht))
  have hDlim :
      Tendsto (fun s : ℝ≥0 => D s ω) (𝓝[<] t) (𝓝 (D t ω)) := by
    exact (hD.2.2.1 ω t).mono Set.Iio_subset_Iic_self
  have hUlim :
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - D s ω)
        (𝓝[<] t) (𝓝 (x + X.X t ω - D t ω)) := by
    exact (tendsto_const_nhds.add hXlim).sub hDlim
  haveI : (𝓝[<] t).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  simpa only [riskProcess] using (leftLim_eq_of_tendsto hUlim)
