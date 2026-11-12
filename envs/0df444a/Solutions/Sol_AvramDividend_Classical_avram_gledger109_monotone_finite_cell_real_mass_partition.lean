-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger109_monotone_finite_cell_real_mass_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:28:06.303193+00:00
-- url     : https://prove2.me/submissions/f6b187fd-6482-418e-9283-9eb956be2e87

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_avram_gledger88_monotone_grid_Ioc_cash_exact_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A finite monotone mesh partitions its real-valued Stieltjes mass
    without duplicating any half-open endpoint payment. -/
theorem solution
    (μ : Measure ℝ) (v : ℕ → ℝ) (hv : Monotone v) (k : ℕ)
    (hfinite : μ (Ioc (v 0) (v k)) < ⊤) :
    (∑ i ∈ Finset.range k,
      (μ (Ioc (v i) (v (i + 1)))).toReal) =
      (μ (Ioc (v 0) (v k))).toReal := by
  have hpart :
      (∑ i ∈ Finset.range k, μ (Ioc (v i) (v (i + 1)))) =
        μ (Ioc (v 0) (v k)) := by
    simpa using
      (avram_gledger88_monotone_grid_Ioc_cash_exact_partition
        μ (fun _ => (1 : ℝ≥0∞)) v hv k)
  have hsumfinite :
      (∑ i ∈ Finset.range k, μ (Ioc (v i) (v (i + 1)))) < ⊤ := by
    rw [hpart]
    exact hfinite
  have hcell : ∀ i ∈ Finset.range k,
      μ (Ioc (v i) (v (i + 1))) ≠ ⊤ := by
    intro i hi
    have hle :
        μ (Ioc (v i) (v (i + 1))) ≤
          ∑ j ∈ Finset.range k, μ (Ioc (v j) (v (j + 1))) :=
      Finset.single_le_sum (s := Finset.range k)
        (f := fun j => μ (Ioc (v j) (v (j + 1))))
        (fun j hj => bot_le) hi
    exact ne_of_lt (lt_of_le_of_lt hle hsumfinite)
  have hreal :
      (∑ i ∈ Finset.range k, μ (Ioc (v i) (v (i + 1)))).toReal =
        ∑ i ∈ Finset.range k, (μ (Ioc (v i) (v (i + 1)))).toReal :=
    ENNReal.toReal_sum (s := Finset.range k)
      (f := fun i => μ (Ioc (v i) (v (i + 1)))) hcell
  rw [← hreal, hpart]
