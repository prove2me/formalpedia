-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_uniform_grid_physical_pair_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:08:09.593207+00:00
-- url     : https://prove2.me/submissions/2f1d815f-458e-4406-9355-22c03c5c523a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_finite_borel_uniform_grid_quadratic_rate_limit
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_grid_pair_rate_sum_exact
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_grid_rate_triangle
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hν : X.ν B < ⊤) :
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let A : ℕ → ℝ≥0∞ := fun k =>
      ∫⁻ ω, ∑ i : Fin k,
        N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) ω *
        N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
          ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)) ω ∂P
    Tendsto A atTop
      (𝓝 ((((T : ℝ≥0∞) * X.ν B) ^ 2) / 2)) := by
  intro N A
  have hRate :=
    avram_a20_finite_borel_uniform_grid_quadratic_rate_limit (X.ν) B T hν
  have hCalc (k : ℕ) (hk : 0 < k) :
      A k = ENNReal.ofReal
        (((k : ℝ) * ((k : ℝ) - 1) / 2) *
          (((T : ℝ) * (X.ν B).toReal) ^ 2 / (k : ℝ) ^ 2)) := by
    let s : Fin k → ℝ≥0 := fun i =>
      ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    obtain ⟨hst, htT, hs, ht⟩ :=
      avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
    let a : ℝ≥0 := (X.ν B).toNNReal
    have ha : (a : ℝ≥0∞) = X.ν B :=
      ENNReal.coe_toNNReal (ne_of_lt hν)
    have haReal : (a : ℝ) = (X.ν B).toReal := by
      have hh := congrArg ENNReal.toReal ha
      simpa only [ENNReal.coe_toReal] using hh
    calc
      A k = ∑ i : Fin k, (s i : ℝ≥0∞) * X.ν B *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
          simpa only [A, N, s, t] using
            (avram_a20_original_borel_grid_pair_rate_sum_exact
              X k s t hst B hB)
      _ = ∑ i : Fin k, (s i : ℝ≥0∞) * (a : ℝ≥0∞) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞)) := by
          rw [ha]
      _ = ENNReal.ofReal
        (((k : ℝ) * ((k : ℝ) - 1) / 2) *
          (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2)) := by
          simpa only [s, t] using
            (avram_p4_f_assembly_original_ennreal_grid_rate_triangle
              T a k hk)
      _ = ENNReal.ofReal
        (((k : ℝ) * ((k : ℝ) - 1) / 2) *
          (((T : ℝ) * (X.ν B).toReal) ^ 2 / (k : ℝ) ^ 2)) := by
          rw [haReal]
  refine hRate.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (hCalc k (by omega)).symm
