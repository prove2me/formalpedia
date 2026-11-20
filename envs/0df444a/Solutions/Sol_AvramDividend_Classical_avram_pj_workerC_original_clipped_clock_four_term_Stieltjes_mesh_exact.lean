-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:52:29.330865+00:00
-- url     : https://prove2.me/submissions/723d41ec-d7af-4d33-a701-eecd5db94164

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ρ : Ω → ℝ≥0)
    (n m : ℕ) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by
  intro Δ u E Y Z
  have hMono : Monotone u := by
    simpa [u, Δ] using
      (AvramDividend.Classical.avram_p3_2_physical_stopped_grid_monotone
        (n : ℝ≥0) (ρ ω) m)
  have hZero : u 0 = 0 := by simp [u, Δ]
  have hTerminal :=
    (AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_endpoints_monotone
      (n : ℝ≥0) m).2.1
  have hEnd : u (m + 1) = ρ ω := by
    change min (((min (m + 1) (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω) = ρ ω
    have hT : (((min (m + 1) (m + 1) : ℕ) : ℝ≥0) * Δ) =
        (n : ℝ≥0) := by
      simpa [Δ] using hTerminal
    rw [hT]
    exact min_eq_right (hρbound ω)
  refine ⟨hEnd, ?_⟩
  exact
    AvramDividend.Classical.avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
      X x q D hD w ω u hMono hZero (m + 1)

