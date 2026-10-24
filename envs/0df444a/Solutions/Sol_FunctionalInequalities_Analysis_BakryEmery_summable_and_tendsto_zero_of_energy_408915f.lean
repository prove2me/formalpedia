-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:49:50.588287+00:00
-- url     : https://prove2.me/submissions/77b2e949-3900-4d09-844e-fdfc3abd5bef

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
variable (m : Measure E) [m.IsAddHaarMeasure]
/-- Telescoping (45): `L₀ ≥ L_N + ∑_{i<N} χ_i + a ∑_{i<N} v_i`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.telescope_energy {L χ v : ℕ → ℝ} {a : ℝ}
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) (N : ℕ) :
    L N + ∑ i ∈ Finset.range N, χ i + a * ∑ i ∈ Finset.range N, v i ≤ L 0 := by
    induction N with
    | zero =>
        simp
    | succ N ih =>
        simp only [Finset.sum_range_succ]
        linarith [h45 N]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **BKL Corollary 3.5** (the summation argument): if (45) holds for every `i` with nonnegative
`L_i = ‖ℒh_i‖²`, `χ_i` and `v_i = ‖∇h_i‖²`, and `a > 0`, then `∑ v_i < ∞` and `v_N → 0`. -/
theorem solution {L χ v : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hL : ∀ i, 0 ≤ L i) (hχ : ∀ i, 0 ≤ χ i) (hv : ∀ i, 0 ≤ v i)
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) :
    Summable v ∧ Summable χ ∧ Tendsto v atTop (𝓝 0) := by
    have hv_bound : ∀ N, (∑ i ∈ Finset.range N, v i) ≤ L 0 / a := by
      intro N
      have htel := FunctionalInequalities.Analysis.BakryEmery.telescope_energy h45 N
      have hχsum : 0 ≤ ∑ i ∈ Finset.range N, χ i :=
        Finset.sum_nonneg (fun i _ => hχ i)
      have hprod : a * (∑ i ∈ Finset.range N, v i) ≤ L 0 := by
        linarith [hL N, htel, hχsum]
      apply (le_div_iff₀ ha).2
      calc
        (∑ i ∈ Finset.range N, v i) * a =
            a * (∑ i ∈ Finset.range N, v i) := by ring
        _ ≤ L 0 := hprod
    have hχ_bound : ∀ N, (∑ i ∈ Finset.range N, χ i) ≤ L 0 := by
      intro N
      have htel := FunctionalInequalities.Analysis.BakryEmery.telescope_energy h45 N
      have hLnon : 0 ≤ L N := hL N
      have hvsum : 0 ≤ ∑ i ∈ Finset.range N, v i :=
        Finset.sum_nonneg (fun i _ => hv i)
      have hprod : 0 ≤ a * (∑ i ∈ Finset.range N, v i) :=
        mul_nonneg (le_of_lt ha) hvsum
      linarith
    have hsumv : Summable v :=
      summable_of_sum_range_le hv hv_bound
    have hsumχ : Summable χ :=
      summable_of_sum_range_le hχ hχ_bound
    exact ⟨hsumv, hsumχ, hsumv.tendsto_atTop_zero⟩
