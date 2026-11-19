-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_canonical_full_stieltjes_cash_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:12:09.062203+00:00
-- url     : https://prove2.me/submissions/fbc70cd9-1a75-4c6c-a3cd-4eec4c9549d9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
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
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    let μ := dividendMeasure D ω
    (∑ i ∈ Finset.range m,
      ENNReal.ofReal (Real.exp (-(q * (v (i+1) : ℝ)))) *
        μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) ≤
      (∫⁻ r in Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) ∧
    (∫⁻ r in Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) ≤
      (∑ i ∈ Finset.range m,
        ENNReal.ofReal (Real.exp (-(q * (v (i+1) : ℝ)))) *
          μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) +
      ENNReal.ofReal (q * (Δ : ℝ)) *
        (∑ i ∈ Finset.range m, μ (Ioc (v i : ℝ) (v (i+1) : ℝ))) := by
  let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
  let μ : Measure ℝ := dividendMeasure D ω
  have hStep (i : ℕ) : v i ≤ v (i + 1) ∧
      ((v (i + 1) : ℝ) - (v i : ℝ)) ≤ (Δ : ℝ) := by
    simpa [v, Δ] using
      (avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
        (1 : ℕ) j t i)
  have hMono : Monotone v :=
    monotone_nat_of_le_succ (fun i => (hStep i).1)
  have hMonoReal : Monotone (fun i => (v i : ℝ)) := by
    intro i k hik
    exact_mod_cast hMono hik
  have hPartition :
      (∑ i ∈ Finset.range m,
        ∫⁻ r in Ioc (v i : ℝ) (v (i+1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) =
      (∫⁻ r in Ioc (v 0 : ℝ) (v m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂μ) := by
    simpa [μ] using
      (avram_gledger90_masked_monotone_grid_Ioc_cash_partition
        μ (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
        Set.univ MeasurableSet.univ (fun i => (v i : ℝ))
        hMonoReal m)
  have hQuadrature :=
    avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
      D hD ω q (Δ : ℝ) hq (by positivity)
      (Finset.range m) v (fun i => v (i+1))
      (fun i hi => (hStep i).1)
      (fun i hi => (hStep i).2)
  rw [hPartition] at hQuadrature
  simpa [μ, v, Δ] using hQuadrature
