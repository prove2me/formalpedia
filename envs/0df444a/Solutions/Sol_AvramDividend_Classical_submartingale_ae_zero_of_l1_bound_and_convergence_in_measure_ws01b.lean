-- Prove2me | solution 1 for AvramDividend.Classical.submartingale_ae_zero_of_l1_bound_and_convergence_in_measure_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:46:00.754394+00:00
-- url     : https://prove2.me/submissions/df297e80-1230-44ec-9dea-88e8b3df9ab7

import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

open MeasureTheory Filter Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓖 : Filtration ℕ mΩ}
    (f : ℕ → Ω → ℝ) (R : NNReal)
    (hSub : Submartingale f 𝓖 P)
    (hBound : ∀ n : ℕ, eLpNorm (f n) (1 : ENNReal) P ≤ ENNReal.ofNNReal R)
    (hMeas : ∀ n : ℕ, AEStronglyMeasurable (f n) P)
    (hMeasure : TendstoInMeasure P f atTop (fun _ : Ω => (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (0 : ℝ)) := by
  have h1 := hSub.ae_tendsto_limitProcess hBound
  obtain ⟨ns, hns, h2⟩ := hMeasure.exists_seq_tendsto_ae
  filter_upwards [h1, h2] with ω hω1 hω2
  have h3 := hω1.comp hns.tendsto_atTop
  have : 𝓖.limitProcess f P ω = 0 := tendsto_nhds_unique h3 hω2
  rwa [this] at hω1
