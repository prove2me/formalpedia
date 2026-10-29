-- Prove2me | solution 1 for AvramDividend.Classical.bv_grid_right_approx_future_vector_law_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:53.420753+00:00
-- url     : https://prove2.me/submissions/a4ca6bbd-f651-4745-9aeb-4663f731bc52

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation
import Theorems.Thm_AvramDividend_Classical_bv_finite_vector_common_law_limit_ws01c
open Filter MeasureTheory Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (J : Finset ℝ≥0)
    (grid : ℕ → Ω → ℝ≥0) (raw : Ω → ℝ≥0)
    (hGridTends : ∀ ω, Tendsto (fun n => grid n ω) atTop (𝓝 (raw ω)))
    (hGridAbove : ∀ ω n, raw ω ≤ grid n ω)
    (hGridMeas : ∀ n, Measurable (fun ω : Ω =>
      fun j : J => X.X (grid n ω + j.1) ω - X.X (grid n ω) ω))
    (hRawMeas : Measurable (fun ω : Ω =>
      fun j : J => X.X (raw ω + j.1) ω - X.X (raw ω) ω))
    (hOrigMeas : Measurable (fun ω : Ω =>
      fun j : J => X.X j.1 ω))
    (hGridLaw : ∀ n,
      Measure.map (fun ω : Ω =>
        fun j : J => X.X (grid n ω + j.1) ω - X.X (grid n ω) ω) P =
      Measure.map (fun ω : Ω => fun j : J => X.X j.1 ω) P) :
    Measure.map (fun ω : Ω =>
      fun j : J => X.X (raw ω + j.1) ω - X.X (raw ω) ω) P =
    Measure.map (fun ω : Ω => fun j : J => X.X j.1 ω) P := by
  have := X.isProbability
  refine bv_finite_vector_common_law_limit_ws01c P
    (fun n ω => fun j : J => X.X (grid n ω + j.1) ω - X.X (grid n ω) ω)
    (fun ω => fun j : J => X.X (raw ω + j.1) ω - X.X (raw ω) ω)
    (fun ω => fun j : J => X.X j.1 ω)
    (fun n => (hGridMeas n).aemeasurable) hRawMeas.aemeasurable hOrigMeas.aemeasurable hGridLaw ?_
  refine Filter.Eventually.of_forall fun ω => tendsto_pi_nhds.2 fun j => ?_
  exact chat08_stopped_levy_increment_tendsto_of_right_approximation X grid raw j.1 hGridTends hGridAbove ω
