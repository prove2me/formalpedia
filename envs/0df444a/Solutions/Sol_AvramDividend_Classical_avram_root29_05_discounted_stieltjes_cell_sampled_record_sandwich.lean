-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_discounted_stieltjes_cell_sampled_record_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:07:18.147048+00:00
-- url     : https://prove2.me/submissions/63099e6b-13a4-4155-8881-8f3a84535aea

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_rightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_cantorSchedule_rationalGrid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Both deterministic discount weights bracket the *actual* Stieltjes
dividend paid in a rational cell by its countable sampled record increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (n k : ℕ) (hn : 0 < n) :
    let t : ℕ → ℝ≥0 := fun j => (j : ℝ≥0) * (n : ℝ≥0)⁻¹
    let sampledRecord : ℕ → ℝ := fun j =>
      ⨆ s : {s : ℝ≥0 //
        s ∈ Set.range (fun i : ℕ =>
          ((Nat.unpair i).2 : ℝ≥0) *
            (((((Nat.unpair i).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ∧ s ≤ t j},
        X.X s.1 ω
    let cash : ℝ≥0∞ :=
      ∫⁻ r, if r ∈ Set.Ioc (t k : ℝ) (t (k + 1) : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)
    ENNReal.ofReal (Real.exp (-(q * (t (k + 1) : ℝ)))) *
        ENNReal.ofReal (sampledRecord (k + 1) - sampledRecord k) ≤ cash ∧
      cash ≤ ENNReal.ofReal (Real.exp (-(q * (t k : ℝ)))) *
        ENNReal.ofReal (sampledRecord (k + 1) - sampledRecord k) := by
  have hw : Antitone (fun r : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * r)))) := by
    intro s t hst
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hst)]
  have hb := runningSup_discounted_interval_bounds_rightLim X ω
    (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r)))) hw
    ((((k : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ))
    (((((k + 1 : ℕ) : ℝ≥0) * (n : ℝ≥0)⁻¹) : ℝ))
  simp only [runningSup_realTime_rightLim_eq, ← NNReal.coe_mul, Real.toNNReal_coe] at hb
  rw [runningSup_eq_cantorSchedule_rationalGrid X ω n (k + 1) hn] at hb
  rw [runningSup_eq_cantorSchedule_rationalGrid X ω n k hn] at hb
  exact hb
