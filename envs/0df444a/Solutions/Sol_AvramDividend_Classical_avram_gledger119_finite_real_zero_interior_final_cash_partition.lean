-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger119_finite_real_zero_interior_final_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:47:17.425262+00:00
-- url     : https://prove2.me/submissions/37d6d308-0fa7-4c80-9f1c-4535ab2a381d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger95_zero_atom_interior_final_cash_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Exact finite real cash ledger for the original first-crossing stopped grid. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSnonneg : ∀ s ∈ S, 0 ≤ s)
    (v : ℕ → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (ρ : ℝ) (hvk : v k < ρ)
    (hstop : v (k + 1) = ρ)
    (hAtom : (∫⁻ s in S ∩ {0}, f s ∂μ) ≠ ⊤)
    (hCells : ∀ i ∈ Finset.range k,
      (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) ≠ ⊤)
    (hFinal : (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ) ≠ ⊤) :
    (∫⁻ s in S ∩ Iio ρ, f s ∂μ).toReal =
      (∫⁻ s in S ∩ {0}, f s ∂μ).toReal +
      (∑ i ∈ Finset.range k,
        (∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ).toReal) +
      (∫⁻ s in S ∩ Ioo (v k) ρ, f s ∂μ).toReal := by
  have hpart := avram_gledger95_zero_atom_interior_final_cash_partition
    μ f S hS hSnonneg v hv hv0 k ρ hvk hstop
  have hsumFin : (∑ i ∈ Finset.range k,
      ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) ≠ ⊤ :=
    ne_of_lt ((ENNReal.sum_lt_top).2 (by
      intro i hi
      exact lt_top_iff_ne_top.mpr (hCells i hi)))
  have hAB : (∫⁻ s in S ∩ {0}, f s ∂μ) +
      (∑ i ∈ Finset.range k,
        ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) ≠ ⊤ :=
    (ENNReal.add_ne_top).2 ⟨hAtom, hsumFin⟩
  rw [hpart, ENNReal.toReal_add hAB hFinal,
    ENNReal.toReal_add hAtom hsumFin, ENNReal.toReal_sum hCells]
