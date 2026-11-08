-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian19_original_initial_step_reserve_nonneg_positive_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:56:24.819822+00:00
-- url     : https://prove2.me/submissions/1dcf0244-6370-4260-891b-87e2678c91c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Positive initial capital supplies the missing time-zero reserve bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      rightLimit (fun s η => if s = 0 then 0 else K η) t ω = K ω)
    (hzero : X.X 0 ω = 0)
    (hcont : ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0)
    (hgap : K ω < x) (hx : 0 ≤ x) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
      0 ≤ riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω := by
  have hc : ContinuousAt (fun t : ℝ≥0 => x + X.X t ω - K ω) 0 :=
    (continuousAt_const.add hcont).sub continuousAt_const
  have hstart : 0 < x + X.X (0 : ℝ≥0) ω - K ω := by
    rw [hzero]
    linarith
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝 (0 : ℝ≥0),
      0 < x + X.X t ω - K ω :=
    hc.eventually (Ioi_mem_nhds hstart)
  obtain ⟨δ, hδ, hnear⟩ := NNReal.nhds_zero_basis.eventually_iff.mp hev
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  by_cases hz : t = 0
  · subst t
    simpa [riskProcess, hzero] using hx
  · have hp : 0 ≤ x + X.X t ω - K ω := le_of_lt (hnear ht)
    simpa [riskProcess, hz] using hp
