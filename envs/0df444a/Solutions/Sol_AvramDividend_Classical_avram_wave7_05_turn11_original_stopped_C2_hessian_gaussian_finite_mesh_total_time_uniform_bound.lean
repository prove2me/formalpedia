-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_original_stopped_C2_hessian_gaussian_finite_mesh_total_time_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:08:42.510119+00:00
-- url     : https://prove2.me/submissions/d88baeb4-88b7-4aed-ab48-5b7d5dd20391

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-! Original stopped C2 Hessian Gaussian bracket mesh domination. -/
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
    ∀ ω, |∑ i ∈ S,
      (h i : ℝ) * (((X.σ : ℝ) ^ 2 / 2) * H i ω)| ≤
      ((X.σ : ℝ) ^ 2 / 2) * K * (T : ℝ) := by
  classical
  let a : ℝ := (X.σ : ℝ) ^ 2 / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hCell (i : ℕ) : Integrable (fun ω => a * H i ω) P := by
    have hOne :=
      avram_wave7_05_turn10_original_stopped_C2_hessian_gaussian_halfbracket_integral_expectation_bound
        X x D hD w C hw q T τ hτ H hHsource K hK hHbound i
    exact hOne.1
  have hAll : ∀ i ∈ S,
      Integrable (fun ω => (h i : ℝ) * (a * H i ω)) P := by
    intro i _
    exact (hCell i).const_mul (h i : ℝ)
  constructor
  · exact integrable_finset_sum S hAll
  · intro ω
    have hh (i : ℕ) : 0 ≤ (h i : ℝ) := by exact_mod_cast (h i).property
    have hb (i : ℕ) :
        |(h i : ℝ) * (a * H i ω)| ≤ (h i : ℝ) * (a * K) := by
      calc
        |(h i : ℝ) * (a * H i ω)| =
            (h i : ℝ) * (a * |H i ω|) := by
              rw [abs_mul, abs_mul, abs_of_nonneg (hh i), abs_of_nonneg ha]
        _ ≤ (h i : ℝ) * (a * K) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hHbound i ω) ha) (hh i)
    change |∑ i ∈ S, (h i : ℝ) * (a * H i ω)| ≤
      a * K * (T : ℝ)
    calc
      |∑ i ∈ S, (h i : ℝ) * (a * H i ω)| ≤
          ∑ i ∈ S, |(h i : ℝ) * (a * H i ω)| :=
        Finset.abs_sum_le_sum_abs (fun i => (h i : ℝ) * (a * H i ω)) S
      _ ≤ ∑ i ∈ S, (h i : ℝ) * (a * K) :=
        Finset.sum_le_sum (fun i _ => hb i)
      _ = (∑ i ∈ S, (h i : ℝ)) * (a * K) := by rw [Finset.sum_mul]
      _ ≤ (T : ℝ) * (a * K) :=
        mul_le_mul_of_nonneg_right hTotal (mul_nonneg ha hK)
      _ = a * K * (T : ℝ) := by ring
