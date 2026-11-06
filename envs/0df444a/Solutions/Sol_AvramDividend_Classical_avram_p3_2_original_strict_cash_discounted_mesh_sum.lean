-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_strict_cash_discounted_mesh_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:12:21.27274+00:00
-- url     : https://prove2.me/submissions/0b694901-7a46-491c-8a22-a7a785cc36f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact finite physical mesh accounting for original pre-ruin cash
strictly before the horizon T. Every stopped Ioc cell is a disjoint
piece of the whole clipped interval, with the T atom excluded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m n : ℕ) (f : ℝ → ℝ≥0∞) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let B : Set ℝ :=
      paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ)
    (∫⁻ t in B ∩ Ioc (0 : ℝ) (u n : ℝ),
      f t ∂(dividendMeasure D ω)) =
      ∑ i ∈ Finset.range n,
        (∫⁻ t in B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂(dividendMeasure D ω)) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let B : Set ℝ :=
    paymentTimes (ruinTime X x D ω) ∩ Iio (T : ℝ)
  let μ : Measure ℝ := dividendMeasure D ω
  let ν : Measure ℝ := μ.restrict B
  have hu : Monotone u :=
    avram_p3_2_physical_stopped_grid_monotone T τ m
  have huR : Monotone (fun j : ℕ => (u j : ℝ)) := by
    intro i j hij
    exact_mod_cast hu hij
  have hu0 : u 0 = 0 := by
    simp [u]
  have hSum :=
    avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum
      ν (fun j : ℕ => (u j : ℝ)) huR n f
  have hAssoc (A : Set ℝ) (hA : MeasurableSet A) :
      ν.restrict A = μ.restrict (B ∩ A) := by
    dsimp [ν]
    rw [Measure.restrict_restrict hA, inter_comm]
  change (∫⁻ t, f t ∂μ.restrict (B ∩ Ioc 0 (u n : ℝ))) =
    ∑ i ∈ Finset.range n,
      (∫⁻ t, f t ∂μ.restrict
        (B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ)))
  calc
    _ = (∫⁻ t in Ioc 0 (u n : ℝ), f t ∂ν) := by
      rw [hAssoc (Ioc 0 (u n : ℝ)) measurableSet_Ioc]
    _ = ∑ i ∈ Finset.range n,
        (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂ν) := by
      simpa only [hu0, NNReal.coe_zero] using hSum
    _ = ∑ i ∈ Finset.range n,
        (∫⁻ t in B ∩ Ioc (u i : ℝ) (u (i + 1) : ℝ),
          f t ∂μ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun ρ : Measure ℝ => ∫⁻ t, f t ∂ρ)
        (hAssoc (Ioc (u i : ℝ) (u (i + 1) : ℝ)) measurableSet_Ioc)
