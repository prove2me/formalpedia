-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_uniform_compensated_drift_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:48:46.591778+00:00
-- url     : https://prove2.me/submissions/5e630d95-0d8a-4295-b7ca-67dd7ee90910

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- With the actual original jump representation, the jump-compensated
physical-grid increment is precisely the drift cell and vanishes uniformly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hpath : ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) =
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    (∀ n i, Y (u n (i + 1)) - Y (u n i) =
      X.drift * (T / ((n : ℝ) + 2))) ∧
    (∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ i,
        |Y (u n (i + 1)) - Y (u n i)| < δ) := by
  dsimp only
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  have hY (t : ℝ≥0) : Y t = (t : ℝ) * X.drift := by
    dsimp [Y, J]
    linarith [hpath t]
  have hcell (n i : ℕ) :
      Y (u n (i + 1)) - Y (u n i) =
        X.drift * (T / ((n : ℝ) + 2)) := by
    rw [hY (u n (i + 1)), hY (u n i)]
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  refine ⟨hcell, ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |X.drift| * T / δ < (N : ℝ) :=
    exists_nat_gt _
  filter_upwards [eventually_ge_atTop N] with n hn
  intro i
  rw [hcell n i]
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hN' : |X.drift| * T < δ * (N : ℝ) :=
    by nlinarith [(div_lt_iff₀ hδ).mp hN]
  have hnum : |X.drift| * T < δ * ((n : ℝ) + 2) := by
    nlinarith
  calc
    |X.drift * (T / ((n : ℝ) + 2))| =
        |X.drift| * T / ((n : ℝ) + 2) := by
          rw [abs_mul, abs_div, abs_of_nonneg (le_of_lt hT),
            abs_of_nonneg (le_of_lt hden)]
          ring
    _ < δ := (div_lt_iff₀ hden).2 hnum
