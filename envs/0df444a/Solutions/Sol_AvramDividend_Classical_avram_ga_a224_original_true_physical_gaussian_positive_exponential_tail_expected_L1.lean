-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a224_original_true_physical_gaussian_positive_exponential_tail_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:11:51.852819+00:00
-- url     : https://prove2.me/submissions/82953613-82fc-48a8-98bc-1d72975d9558

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (hn : 0 < n) (θ δ : ℝ)
    (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let t : ℕ → ℕ → ℝ≥0 := fun m i => s m i + Δ m
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m,
        let Z : ℝ := ((X.X (t m i) ω - X.X (s m i) ω) -
          ((t m i - s m i : ℝ≥0) : ℝ) * X.c) / X.σ
        if δ ≤ Z then Real.exp (θ * Z) else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro Δ s t
  have hs (m i : ℕ) : s m i ≤ t m i := by
    dsimp [s,t]
    exact le_add_of_nonneg_right (by positivity)
  have hw (m i : ℕ) :
      (((t m i - s m i : ℝ≥0) : ℝ)) =
        (n : ℝ) / ((m : ℝ) + 1) := by
    dsimp [s,t,Δ]
    rw [add_tsub_cancel_left]
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one]
  exact avram_ga_a221_original_gaussian_uniform_physical_positive_exponential_tail_L1
    X hν hσ n hn s t (fun m i _ => hs m i)
    (fun m i _ => hw m i) θ δ hθ hδ
