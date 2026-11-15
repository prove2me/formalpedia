-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a330_integrable_nonnegative_finite_sum_implies_integrable_each_measurable_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:17:48.542199+00:00
-- url     : https://prove2.me/submissions/2d1e9d69-2bad-4618-bb65-4a7a523061cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (f : ℕ → Ω → ℝ)
    (hfMeas : ∀ i ∈ S, Measurable (f i))
    (hfPos : ∀ i ∈ S, ∀ ω, 0 ≤ f i ω)
    (hSum : Integrable (fun ω => ∑ i ∈ S, f i ω) P) :
    ∀ i ∈ S, Integrable (f i) P := by
  intro i hi
  have hsub (ω : Ω) : f i ω ≤ ∑ j ∈ S, f j ω :=
    Finset.single_le_sum (fun j hj => hfPos j hj ω) hi
  apply Integrable.mono' hSum ((hfMeas i hi).aestronglyMeasurable)
  filter_upwards [] with ω
  have hsum : 0 ≤ ∑ j ∈ S, f j ω :=
    Finset.sum_nonneg (fun j hj => hfPos j hj ω)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (hfPos i hi ω),
    abs_of_nonneg hsum] using hsub ω
