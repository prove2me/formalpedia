-- Prove2me | solution 2 for AvramDividend.Classical.barrierSupValue_zero_eq_iInf_cofinal_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:52:31.852073+00:00
-- url     : https://prove2.me/submissions/3a9b5892-62cd-42cf-b3fa-1b67760c0371

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Any positive sequence converging to zero computes the same reflected dividend limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hfinite : barrierSupValue X 1 q ≠ ⊤)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (nhds (0 : ℝ))) :
    barrierSupValue X 0 q = ⨅ n : ℕ, barrierSupValue X (r n) q := by
  have hrec : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : (⨅ m : ℕ, barrierSupValue X (r m) q) ≤
      ⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q := by
    refine le_iInf fun n => ?_
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨m, hm⟩ := (hrlim.eventually (Iio_mem_nhds hn)).exists
    exact (iInf_le _ m).trans
      (barrierSupValue_mono_barrier X (r m) (1 / ((n : ℝ) + 1)) q hm.le)
  have hge : (⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q) ≤
      ⨅ m : ℕ, barrierSupValue X (r m) q := by
    refine le_iInf fun m => ?_
    obtain ⟨n, hn⟩ := (hrec.eventually (Iio_mem_nhds (hrpos m))).exists
    exact (iInf_le _ n).trans
      (barrierSupValue_mono_barrier X (1 / ((n : ℝ) + 1)) (r m) q hn.le)
  calc
    barrierSupValue X 0 q =
        ⨅ n : ℕ, barrierSupValue X (1 / ((n : ℝ) + 1)) q :=
      barrierSupValue_zero_eq_iInf_reciprocal_of_finite X q hfinite
    _ = ⨅ n : ℕ, barrierSupValue X (r n) q := le_antisymm hge hle
