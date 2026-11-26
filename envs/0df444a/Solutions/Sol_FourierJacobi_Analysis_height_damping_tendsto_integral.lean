-- Prove2me | solution 1 for FourierJacobi.Analysis.height_damping_tendsto_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:12.116204+00:00
-- url     : https://prove2.me/submissions/a3ff05a9-a221-4076-a102-021b17f67428

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_Damping

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis
open MeasureTheory Filter
open scoped Topology
namespace FourierJacobi.Analysis
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : Integrable f μ)
    {height : X → ℕ} (hh : Measurable height)
    {T : ℕ → ℝ} (hT₀ : ∀ n, 0 ≤ T n) (hT₁ : ∀ n, T n ≤ 1)
    (hTlim : Tendsto T atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (T n ^ height x) • f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (hh.const_pow (T n)).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hT₀ n) _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (hT₀ n) (hT₁ n))
  · filter_upwards [] with x
    simpa using (hTlim.pow (height x)).smul_const (f x)
end FourierJacobi.Analysis
