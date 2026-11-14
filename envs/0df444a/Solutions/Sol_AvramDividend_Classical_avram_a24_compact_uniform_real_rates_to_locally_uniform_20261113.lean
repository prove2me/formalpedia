-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_compact_uniform_real_rates_to_locally_uniform_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:58:21.387431+00:00
-- url     : https://prove2.me/submissions/7a379fbe-5284-466e-ad8d-19200ce5c265

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

/-- Uniform real error bounds on every compact nonnegative horizon imply locally uniform convergence on each right half-line. -/
theorem solution
    (F : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ)
    (hRate : ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ u : ℝ≥0, u ≤ (K : ℝ≥0) →
        |F n u - g u| ≤ ε) :
    ∀ t : ℝ≥0, TendstoLocallyUniformlyOn F g atTop (Ici t) := by
  intro t
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨K, hK⟩ := exists_nat_gt x
  let V : Set ℝ≥0 := Iio (K : ℝ≥0)
  have hV : V ∈ 𝓝[Ici t] x :=
    nhdsWithin_le_nhds (Iio_mem_nhds hK)
  obtain ⟨N, hN⟩ := hRate K (ε / 2) (by linarith)
  refine ⟨V, hV, Filter.eventually_atTop.2 ⟨N, ?_⟩⟩
  intro n hn u hu
  have hBound := hN n hn u (le_of_lt hu)
  rw [Real.dist_eq, abs_sub_comm]
  linarith
