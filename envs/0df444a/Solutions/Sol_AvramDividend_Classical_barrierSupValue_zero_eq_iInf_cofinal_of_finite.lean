-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_zero_eq_iInf_cofinal_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:52:16.534569+00:00
-- url     : https://prove2.me/submissions/c24c9268-5cf1-49d0-8930-87d7091061a2

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hfinite : barrierSupValue X 1 q ≠ ⊤)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n)
    (hrlim : Filter.Tendsto r Filter.atTop (nhds (0 : ℝ))) :
    barrierSupValue X 0 q = ⨅ n : ℕ, barrierSupValue X (r n) q := by
  refine le_antisymm (le_iInf fun n =>
    AvramDividend.Classical.barrierSupValue_mono_barrier X _ _ q (hrpos n).le) ?_
  rw [AvramDividend.Classical.barrierSupValue_zero_eq_iInf_reciprocal_of_finite X q hfinite]
  refine le_iInf fun k => ?_
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨n, hn⟩ := (hrlim.eventually (Iio_mem_nhds hk)).exists
  exact (iInf_le _ n).trans (AvramDividend.Classical.barrierSupValue_mono_barrier X _ _ q (le_of_lt hn))
