-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_killed_mesh_cell_integral_eq_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:37:54.118033+00:00
-- url     : https://prove2.me/submissions/c82c372d-9eb4-4385-8dba-17fe10cb1602

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_right_mesh_cell_endpoint_identity
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal Classical

/-- The killed sampled discount is constant on each half-open payment cell,
so its actual Stieltjes integral is that weight times the cell's measure. -/
theorem solution (μ : Measure ℝ) (q : ℝ) (τ : ℝ≥0∞)
    (n k : ℕ) :
    (∫⁻ r in Ioc ((k : ℝ) / ((n : ℝ) + 1))
        (((k : ℝ) + 1) / ((n : ℝ) + 1)),
      (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
       if ENNReal.ofReal e < τ then
         ENNReal.ofReal (Real.exp (-(q * e))) else 0) ∂μ) =
    (if ENNReal.ofReal (((k : ℝ) + 1) / ((n : ℝ) + 1)) < τ then
      ENNReal.ofReal (Real.exp (-(q * (((k : ℝ) + 1) / ((n : ℝ) + 1)))))
      else 0) *
      μ (Ioc ((k : ℝ) / ((n : ℝ) + 1))
        (((k : ℝ) + 1) / ((n : ℝ) + 1))) := by
  let a : ℝ := (k : ℝ) / ((n : ℝ) + 1)
  let b : ℝ := ((k : ℝ) + 1) / ((n : ℝ) + 1)
  let v : ℝ≥0∞ :=
    if ENNReal.ofReal b < τ then
      ENNReal.ofReal (Real.exp (-(q * b))) else 0
  have hconst : ∀ᵐ r ∂(μ.restrict (Ioc a b)),
      (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
       if ENNReal.ofReal e < τ then
         ENNReal.ofReal (Real.exp (-(q * e))) else 0) = v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr : r ∈ Ioc ((k : ℝ) / ((n : ℝ) + 1))
        (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
      simpa [a, b] using hr
    have he := avram_root29_05_right_mesh_cell_endpoint_identity n k r hr
    dsimp [v, b]
    rw [he]
  change (∫⁻ r in Ioc a b,
      (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
       if ENNReal.ofReal e < τ then
         ENNReal.ofReal (Real.exp (-(q * e))) else 0) ∂μ) =
      v * μ (Ioc a b)
  calc
    _ = ∫⁻ r in Ioc a b, v ∂μ :=
      lintegral_congr_ae hconst
    _ = v * μ (Ioc a b) := by simp [lintegral_const]
