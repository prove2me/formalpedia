-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:03:41.678668+00:00
-- url     : https://prove2.me/submissions/d6fa209e-7671-4401-b1fb-c078f1ac241b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Actual controlled reserve derivative: pointwise localisation implies square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (G : ℕ → Ω → ℝ)
    (hGsource : ∀ n, G n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ n ω, |G n ω| ≤ K) :
    ∀ n, Integrable (fun ω => G n ω * G n ω) P ∧
      (∫ ω, G n ω * G n ω ∂P) ≤ K ^ 2 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro n
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T (τ n) (hτ n)
  dsimp only at hPred
  have hMeas : Measurable (G n) := by
    rw [hGsource n]
    exact hPred.2.2.1
  have hsq : ∀ ω : Ω, (G n ω) ^ 2 ≤ K ^ 2 := by
    intro ω
    have hlow : 0 ≤ |G n ω| := abs_nonneg _
    have hdiff : 0 ≤ (K - |G n ω|) * (K + |G n ω|) :=
      mul_nonneg (sub_nonneg.mpr (hGbound n ω)) (add_nonneg hK hlow)
    have habs : (|G n ω|) ^ 2 = (G n ω) ^ 2 := sq_abs _
    nlinarith
  have hdom : ∀ ω : Ω, ‖G n ω * G n ω‖ ≤ K ^ 2 := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _)]
    simpa only [pow_two] using hsq ω
  have hpoint : ∀ ω : Ω, G n ω * G n ω ≤ K ^ 2 := by
    intro ω
    simpa only [pow_two] using hsq ω
  have hInt : Integrable (fun ω => G n ω * G n ω) P :=
    (integrable_const (K ^ 2)).mono'
      (hMeas.mul hMeas).aestronglyMeasurable
      (Filter.Eventually.of_forall hdom)
  refine ⟨hInt, ?_⟩
  calc
    (∫ ω, G n ω * G n ω ∂P) ≤ ∫ _ω : Ω, K ^ 2 ∂P :=
      integral_mono hInt (integrable_const _) hpoint
    _ = K ^ 2 := by simp
