-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_laplace_transform_atom_zero_limit_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:21:13.158985+00:00
-- url     : https://prove2.me/submissions/6fac4de3-776d-49b6-9c06-1cc664a2fd8f

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology

/-- Dominated convergence identifies the zero atom of a nonnegative random variable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (D : Ω → ℝ)
    (hMeas : Measurable D)
    (hNonneg : ∀ᵐ ω ∂μ, 0 ≤ D ω) :
    Tendsto (fun n : ℕ => ∫ ω, Real.exp ((n : ℝ) * (-D ω)) ∂μ)
      atTop (𝓝 (∫ ω, if D ω = 0 then (1 : ℝ) else 0 ∂μ)) := by
  have hMeasExp (n : ℕ) :
      AEStronglyMeasurable
        (fun ω => Real.exp ((n : ℝ) * (-D ω))) μ :=
    ((measurable_const.mul hMeas.neg).exp).aestronglyMeasurable
  have hBound (n : ℕ) :
      ∀ᵐ ω ∂μ, ‖Real.exp ((n : ℝ) * (-D ω))‖ ≤ (1 : ℝ) := by
    filter_upwards [hNonneg] with ω hω
    have hn : (n : ℝ) * (-D ω) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (neg_nonpos.mpr hω)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_one_iff).2 hn
  have hPoint :
      ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => Real.exp ((n : ℝ) * (-D ω))) atTop
        (𝓝 (if D ω = 0 then (1 : ℝ) else 0)) := by
    filter_upwards [hNonneg] with ω hω
    by_cases hd : D ω = 0
    · simpa [hd] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · have hpos : 0 < D ω := lt_of_le_of_ne hω (Ne.symm hd)
      have hmul :
          Tendsto (fun n : ℕ => (n : ℝ) * (-D ω)) atTop atBot :=
        Filter.Tendsto.atTop_mul_const_of_neg (neg_lt_zero.mpr hpos)
          tendsto_natCast_atTop_atTop
      simp only [if_neg hd]
      exact Real.tendsto_exp_atBot.comp hmul
  exact tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n ω => Real.exp ((n : ℝ) * (-D ω)))
    (f := fun ω => if D ω = 0 then (1 : ℝ) else 0)
    (fun _ : Ω => (1 : ℝ))
    hMeasExp (integrable_const _) hBound hPoint
