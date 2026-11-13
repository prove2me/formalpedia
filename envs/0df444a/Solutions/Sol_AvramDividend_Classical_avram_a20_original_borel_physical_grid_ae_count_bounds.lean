-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_physical_grid_ae_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:39:42.648228+00:00
-- url     : https://prove2.me/submissions/2df94727-3549-4834-b378-375eaa6b8bf9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_marked_times_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_grid_ae_eventual_pair_count
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω => {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ∑ i : Fin k,
        N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) ω *
        N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
          ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)) ω
    (∀ᵐ ω ∂P, ∀ k, A k ω ≤ (K ω : ℝ≥0∞)) ∧
    (∀ᵐ ω ∂P, ∀ᶠ k in atTop, A k ω = (K ω : ℝ≥0∞)) := by
  intro S K N A
  have hFin : ∀ᵐ ω ∂P, (S ω).Finite := by
    simpa only [S] using
      (avram_a20_original_borel_physical_marked_times_finite_ae
        X hFinite T B hB hNeg)
  constructor
  · filter_upwards [hFin] with ω hω
    simpa only [S, K, N, A] using
      (avram_a20_original_borel_physical_grid_ae_eventual_pair_count
        X ω T hT B hB hω).1
  · filter_upwards [hFin] with ω hω
    simpa only [S, K, N, A] using
      (avram_a20_original_borel_physical_grid_ae_eventual_pair_count
        X ω T hT B hB hω).2
