-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_clipped_stieltjes_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:40:20.400876+00:00
-- url     : https://prove2.me/submissions/31ed6699-2753-4064-91e9-213bb8f5f3b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gledger90_masked_monotone_grid_Ioc_cash_partition
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
    (ω : Ω) (q : ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    (∑ i ∈ Finset.range m,
      ∫⁻ r in S ∩ Ioc (v i : ℝ) (v (i+1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) =
      (∫⁻ r in S ∩ Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) := by
  dsimp
  let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
  have hgrid :=
    avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
      1 j t
  have hm : Monotone v := by
    apply monotone_nat_of_le_succ
    intro i
    simpa only [v, Δ, Nat.cast_one] using (hgrid i).1
  have hvr : Monotone (fun i : ℕ => (v i : ℝ)) := by
    intro a b hab
    exact_mod_cast hm hab
  have hpartition :=
    avram_gledger90_masked_monotone_grid_Ioc_cash_partition
      (dividendMeasure D ω)
      (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
      S hS (fun i : ℕ => (v i : ℝ)) hvr m
  simpa only [v, Δ] using hpartition
