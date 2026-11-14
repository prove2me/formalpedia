-- Prove2me | solution 1 for AvramDividend.Classical.avram_b201_original_true_marked_grid_real_poisson_dom_from_measurable_full_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:25:56.64581+00:00
-- url     : https://prove2.me/submissions/9d61a4cb-25c3-4dfe-83d2-b6f7a6a60964

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
import Theorems.Thm_AvramDividend_Classical_avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original full negative source count finiteness transfers pathwise marked count to real ae domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (J : Ω → Finset ℕ)
    (hJ : ∀ᵐ ω ∂P, ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hRange : ∀ ω i, i ∈ J ω → grid ω (i + 1) ≤ T)
    (hCountMeas : AEMeasurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))) P) :
    ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by
  have hBound : ∀ ω : Ω, (fun _ : Ω => T) ω ≤ (n : ℝ≥0) := by
    intro ω
    exact hT
  have hFiniteAE :=
    avram_b195_original_fullnegative_poisson_count_finite_ae_from_source_L1
      X hFinite n (fun _ : Ω => T) hBound
      (by simpa only using hCountMeas)
  filter_upwards [hJ, hFiniteAE] with ω hωJ hωFinite
  have hCards :=
    avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
      X ω T (grid ω) (hMono ω) (J ω) hωJ (hRange ω)
  have hReal := ENNReal.toReal_mono (ne_of_lt hωFinite) hCards
  simpa only [ENNReal.toReal_natCast, Nat.cast_id] using hReal
