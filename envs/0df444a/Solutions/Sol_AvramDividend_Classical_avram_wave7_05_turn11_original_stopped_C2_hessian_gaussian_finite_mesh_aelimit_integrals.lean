-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_aelimit_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:15:06.770649+00:00
-- url     : https://prove2.me/submissions/041ed818-5a1f-4608-8e00-7f444df2cbde

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped Gaussian Hessian drift passage along a finite mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : ℕ → Finset ℕ)
    (τ : ℕ → ℕ → Ω → ℝ≥0)
    (hτ : ∀ n i, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (H : ℕ → ℕ → Ω → ℝ)
    (hHsource : ∀ n i, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ n i ω, |H n i ω| ≤ K)
    (h : ℕ → ℕ → ℝ≥0)
    (hTotal : ∀ n, (∑ i ∈ S n, (h n i : ℝ)) ≤ (T : ℝ))
    (L : Ω → ℝ) :
    (∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ S n,
      (h n i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H n i ω))
      atTop (nhds (L ω))) →
    Tendsto (fun n => ∫ ω, ∑ i ∈ S n,
      (h n i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H n i ω) ∂P)
      atTop (nhds (∫ ω, L ω ∂P)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let a : ℝ := (X.σ : ℝ) ^ 2 / 2
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, (h n i : ℝ) * (a * H n i ω)
  change (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    Tendsto (fun n => ∫ ω, Q n ω ∂P)
      atTop (nhds (∫ ω, L ω ∂P))
  intro hConv
  have hCell (n : ℕ) :
      Integrable (Q n) P ∧ ∀ ω, |Q n ω| ≤ a * K * (T : ℝ) := by
    have hOne :=
      avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
        X x D hD w C hw q T (S n) (τ n) (hτ n)
        (H n) (hHsource n) K hK (hHbound n) (h n) (hTotal n)
    exact hOne
  have hMeas : ∀ n, AEStronglyMeasurable (Q n) P :=
    fun n => (hCell n).1.aestronglyMeasurable
  have hDom : Integrable (fun _ : Ω => a * K * (T : ℝ)) P :=
    integrable_const _
  have hBound : ∀ n, ∀ᵐ ω ∂P, ‖Q n ω‖ ≤ a * K * (T : ℝ) := by
    intro n
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using (hCell n).2 ω)
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => a * K * (T : ℝ)) hMeas hDom hBound hConv
