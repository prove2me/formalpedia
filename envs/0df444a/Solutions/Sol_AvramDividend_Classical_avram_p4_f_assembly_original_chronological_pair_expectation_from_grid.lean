-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_expectation_from_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:01:38.157631+00:00
-- url     : https://prove2.me/submissions/081d2abd-0acb-47c4-a077-86852c2cade0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_all_finer_pair_set_equiv
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : ℝ≥0∞) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℝ≥0∞ := fun ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    (∀ k, Measurable (A k)) →
    (∀ k ω, A k ω ≤ K ω) →
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop (𝓝 r) →
    (∫⁻ ω, K ω ∂P) = r := by
  classical
  dsimp only
  intro hAm hBound hRate
  let F : Ω → Finset ℝ≥0 := fun ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let K : Ω → ℝ≥0∞ := fun ω =>
    ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
  let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
  change (∫⁻ ω, K ω ∂P) = r
  apply avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze P A K r hAm hBound
  · intro ω
    obtain ⟨k₀, hk₀, hEqual⟩ :=
      avram_p4_f_assembly_original_marked_all_finer_pair_set_equiv X ω T hT n
    filter_upwards [eventually_ge_atTop k₀] with k hk
    exact congrArg (fun E : Finset (ℝ≥0 × ℝ≥0) => (E.card : ℝ≥0∞))
      (hEqual k hk).symm
  · exact hRate