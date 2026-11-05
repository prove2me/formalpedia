-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_one_grid_cell_pair_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:36:04.081196+00:00
-- url     : https://prove2.me/submissions/7ceadd64-75ea-4594-aaf0-2e94d2687a48

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_crossing_pair_card

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The two original window counts multiply to the literal source crossing-pair count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    N 0 s * N s t =
      (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card : ℝ≥0∞) := by
  classical
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  let N : ℝ≥0 → ℝ≥0 → ℝ≥0∞ := fun a b =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  let hF := avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  let F : Finset ℝ≥0 := hF.toFinset
  change N 0 s * N s t =
    (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card : ℝ≥0∞)
  have h0s : (0 : ℝ≥0) ≤ s := by positivity
  have h0 : N 0 s =
      ((F.filter (fun u => 0 < u ∧ u ≤ s)).card : ℝ≥0∞) := by
    simpa only [N, B, F, hF] using
      (avram_p2_e_compensator_original_window_count_finset_filter
        X ω 0 s T h0s (le_trans hst htT) n)
  have h1 : N s t =
      ((F.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by
    simpa only [N, B, F, hF] using
      (avram_p2_e_compensator_original_window_count_finset_filter
        X ω s t T hst htT n)
  have hPast : F.filter (fun u => 0 < u ∧ u ≤ s) =
      F.filter (fun u => u ≤ s) := by
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hFu, ⟨_, hus⟩⟩
      exact ⟨hFu, hus⟩
    · rintro ⟨hFu, hus⟩
      have hu0 : 0 < u := ((Set.Finite.mem_toFinset hF).mp hFu).1
      exact ⟨hFu, hu0, hus⟩
  have hp : (F.filter (fun u => u ≤ s)).card *
      (F.filter (fun u => s < u ∧ u ≤ t)).card =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card := by
    simpa only [F, hF] using
      (avram_p2_e_compensator_original_grid_crossing_pair_card X ω T s t n)
  calc
    N 0 s * N s t =
        ((F.filter (fun u => 0 < u ∧ u ≤ s)).card : ℝ≥0∞) *
          ((F.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by
            rw [h0, h1]
    _ = ((F.filter (fun u => u ≤ s)).card : ℝ≥0∞) *
        ((F.filter (fun u => s < u ∧ u ≤ t)).card : ℝ≥0∞) := by rw [hPast]
    _ = (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 ≤ s ∧ s < p.2 ∧ p.2 ≤ t)).card : ℝ≥0∞) := by
          exact_mod_cast hp
