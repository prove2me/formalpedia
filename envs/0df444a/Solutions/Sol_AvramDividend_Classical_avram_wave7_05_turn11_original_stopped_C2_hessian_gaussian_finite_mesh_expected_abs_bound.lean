-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_expected_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:17:56.699056+00:00
-- url     : https://prove2.me/submissions/0d3492ff-4923-48a6-b78b-59d988e390c6

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped Gaussian Hessian finite mesh expectation envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : Finset ℕ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ n, H n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ n ω, |H n ω| ≤ K)
    (h : ℕ → ℝ≥0)
    (hTotal : (∑ i ∈ S, (h i : ℝ)) ≤ (T : ℝ)) :
    Integrable (fun ω => ∑ i ∈ S,
      (h i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H i ω)) P ∧
    |∫ ω, ∑ i ∈ S,
      (h i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H i ω) ∂P| ≤
      ((X.σ : ℝ) ^ 2 / 2) * K * (T : ℝ) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let a : ℝ := (X.σ : ℝ) ^ 2 / 2
  let Q : Ω → ℝ := fun ω =>
    ∑ i ∈ S, (h i : ℝ) * (a * H i ω)
  change Integrable Q P ∧ |∫ ω, Q ω ∂P| ≤ a * K * (T : ℝ)
  have hOne :=
    avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
      X x D hD w C hw q T S τ hτ H hHsource K hK hHbound h hTotal
  have hI : Integrable Q P := hOne.1
  have hB : ∀ ω, |Q ω| ≤ a * K * (T : ℝ) := hOne.2
  refine ⟨hI, ?_⟩
  have hAe : ∀ᵐ ω ∂P, ‖Q ω‖ ≤ a * K * (T : ℝ) :=
    Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hB ω)
  have hNorm := MeasureTheory.norm_integral_le_of_norm_le_const hAe
  simpa [Real.norm_eq_abs] using hNorm
