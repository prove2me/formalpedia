-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_canonical_near_zero_jumps_preserve_compact_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:05:11.859051+00:00
-- url     : https://prove2.me/submissions/87bd67db-65d7-4606-9755-c1108c4a069b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section

/-- On any fixed compact positive interior strip, the canonical sufficiently
small negative Lévy jump bands preserve (0,C), separating the near-zero
Taylor regime from the finite-intensity ruin/exit jumps. -/
theorem solution
    (C a v δ : ℝ) (ha : 0 ≤ a) (hδ : 0 < δ) (hv : v < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ u : ℝ, u ∈ Icc (a + δ) v →
      ∀ z : ℝ, z ∈ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) 0 →
        u + z ∈ Ioo 0 C := by
  have hlim : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 (hlim.eventually_lt_const hδ)
  refine ⟨N, ?_⟩
  intro n hn u hu z hz
  have hsmall := hN n hn
  have hzlow : -((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) < z := by
    simpa only [neg_div] using hz.1
  exact ⟨by linarith [hzlow, hsmall, hu.1], by linarith [hu.2, hz.2]⟩
