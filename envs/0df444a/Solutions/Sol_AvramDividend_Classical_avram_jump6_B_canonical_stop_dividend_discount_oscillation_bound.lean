-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_stop_dividend_discount_oscillation_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T18:56:00.424774+00:00
-- url     : https://prove2.me/submissions/fab5cd25-9b4e-433e-8949-e27e7910574c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (v i : ℝ))) -
       Real.exp (-(q * (v (i+1) : ℝ)))) *
      (rightLimit D (v (i+1)) ω - rightLimit D (v i) ω)) ≤
      q * (Δ : ℝ) * (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by
  let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
  have hStep (i : ℕ) : v i ≤ v (i + 1) ∧
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ) := by
    simpa [v, Δ] using
      (avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
        (1 : ℕ) j t i)
  have hMono : Monotone v := monotone_nat_of_le_succ
    (fun i => (hStep i).1)
  have hMesh : ∀ i < m, ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ) := by
    intro i _
    exact (hStep i).2
  exact avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
    D hD ω q hq v hMono m (Δ : ℝ)
    (by positivity) hMesh
