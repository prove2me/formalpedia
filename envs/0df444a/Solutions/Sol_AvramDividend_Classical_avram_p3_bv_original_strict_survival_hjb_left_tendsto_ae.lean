-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:36:29.362101+00:00
-- url     : https://prove2.me/submissions/f1df9399-b9a7-44aa-b29f-d5830d0de54c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_controlled_fixed_horizon_left_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original controlled HJB value is left-continuous at a deterministic
strict-survival horizon, including reserve zero and finite-cap contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 => w (riskProcess X x D s ω))
        (𝓝[<] t) (𝓝 (w (riskProcess X x D t ω))) := by
  filter_upwards [avram_p3_bv_original_controlled_fixed_horizon_left_tendsto_ae
    X D hD x t ht] with ω hU
  intro hSurv
  have htPos : riskProcess X x D t ω ∈ Ici (0 : ℝ) :=
    Set.mem_Ici.mpr
      (riskProcess_nonnegative_strictly_before_ruin X x D ω t hSurv)
  have hNear : ∀ᶠ s in 𝓝[<] t,
      riskProcess X x D s ω ∈ Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hst : s < t := Set.mem_Iio.mp hs
    have hst' : (s : ℝ≥0∞) < (t : ℝ≥0∞) := by exact_mod_cast hst
    exact Set.mem_Ici.mpr
      (riskProcess_nonnegative_strictly_before_ruin X x D ω s
        (lt_trans hst' hSurv))
  have hWithin : Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
      (𝓝[<] t) (𝓝[Ici (0 : ℝ)] (riskProcess X x D t ω)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun s : ℝ≥0 => riskProcess X x D s ω) hU hNear
  have hW : Tendsto w
      (𝓝[Ici (0 : ℝ)] (riskProcess X x D t ω))
      (𝓝 (w (riskProcess X x D t ω))) :=
    hw (riskProcess X x D t ω) htPos
  exact Filter.Tendsto.comp hW hWithin
