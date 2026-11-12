-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger130_finite_partition_cash_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:53:35.619608+00:00
-- url     : https://prove2.me/submissions/e19a976e-3568-4642-bffa-64f4d9e9a425

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger108_zero_atom_interior_final_real_cash_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (S : Set ℝ)
    (hS : MeasurableSet S) (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ)
    (hcell : ∀ i < k, Ioc (v i) (v (i + 1)) ⊆ S)
    (hfinite : (∫⁻ s in S ∩ Iio ρ, f s ∂μ) < ⊤)
    (U : Set ℝ)
    (hfinal : S ∩ Ioo (v k) ρ ⊆ U)
    (hUfin : (∫⁻ s in U, f s ∂μ) ≠ ⊤) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal ≤
      (∫⁻ s in S ∩ {0}, f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ).toReal) +
      (∫⁻ s in U, f s ∂μ).toReal := by
  have hpart := avram_gledger108_zero_atom_interior_final_real_cash_partition
    μ f S hS hSnonneg v hv hv0 k ρ hvk hstop hfinite
  have hcells : (∑ i ∈ Finset.range k,
      (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ).toReal) =
      (∑ i ∈ Finset.range k,
      (∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ).toReal) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Set.inter_eq_right.mpr (hcell i (Finset.mem_range.mp hi))]
  have htail := ENNReal.toReal_mono hUfin
    (lintegral_mono_set (μ := μ) (f := f) hfinal)
  rw [hpart, hcells]
  linarith
