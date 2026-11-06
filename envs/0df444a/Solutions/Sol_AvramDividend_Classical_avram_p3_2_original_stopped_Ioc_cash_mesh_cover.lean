-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_stopped_Ioc_cash_mesh_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:06:20.035232+00:00
-- url     : https://prove2.me/submissions/d92be730-2005-42b0-89a1-1f1d92298ea0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_monotone_Ioc_mesh_cover

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For the actual original X/D ruin-clipped physical time mesh,
adjacent half-open dividend cells cover precisely the stopped horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (⋃ i ∈ Finset.range n,
      Ioc (u i : ℝ) (u (i + 1) : ℝ)) = Ioc 0 (u n : ℝ) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  have hu : Monotone u :=
    avram_p3_2_physical_stopped_grid_monotone T τ m
  have huReal : Monotone (fun j : ℕ => (u j : ℝ)) := by
    intro i j hij
    exact_mod_cast hu hij
  have hCover :=
    avram_p3_2_physical_monotone_Ioc_mesh_cover
      (fun j : ℕ => (u j : ℝ)) huReal n
  have hu0 : u 0 = 0 := by
    simp [u]
  simpa only [hu0, NNReal.coe_zero] using hCover
