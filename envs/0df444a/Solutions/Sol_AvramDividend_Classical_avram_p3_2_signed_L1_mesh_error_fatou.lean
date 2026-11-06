-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_signed_L1_mesh_error_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:32:57.807966+00:00
-- url     : https://prove2.me/submissions/bdc42be3-2a46-401d-9253-d44b5d24ce84

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_vanishing_error_signed_fatou_original_grid
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A signed, integrable original-grid error with vanishing expectation
can be centred into the mean-nonpositive residual before Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ) (F R Err : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P) (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧ (∫ ω, R n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (Err n) P)
    (hErrMean : Tendsto (fun n => ∫ ω, Err n ω ∂P)
      atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω + Err n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by
  let μ : ℕ → ℝ := fun n => ∫ ω, Err n ω ∂P
  let R' : ℕ → Ω → ℝ := fun n ω => R n ω + Err n ω - μ n
  have hR' (n : ℕ) :
      Integrable (R' n) P ∧ (∫ ω, R' n ω ∂P) ≤ 0 := by
    have hRInt : Integrable (R n) P := (hR n).1
    have hEInt : Integrable (Err n) P := hErrInt n
    have hAdd : Integrable (fun ω => R n ω + Err n ω) P :=
      hRInt.add hEInt
    have hNewInt : Integrable (R' n) P :=
      hAdd.sub (integrable_const (μ n))
    refine ⟨hNewInt, ?_⟩
    have hIntegral :
        (∫ ω, R' n ω ∂P) = (∫ ω, R n ω ∂P) := by
      change (∫ ω, R n ω + Err n ω - μ n ∂P) =
        ∫ ω, R n ω ∂P
      rw [integral_sub hAdd (integrable_const (μ n))]
      rw [integral_add hRInt hEInt]
      simp [μ]
    rw [hIntegral]
    exact (hR n).2
  have hBound' (n : ℕ) :
      ∀ᵐ ω ∂P, F n ω ≤ K + R' n ω + μ n := by
    filter_upwards [hBound n] with ω hω
    change F n ω ≤ K + (R n ω + Err n ω - μ n) + μ n
    linarith
  have hμ : Tendsto μ atTop (nhds (0 : ℝ)) := hErrMean
  exact
    AvramDividend.Classical.avram_p3_2_vanishing_error_signed_fatou_original_grid
      P K Y F R' μ hYInt hYNonneg hFMeas hFInt hFNonneg
      hR' hμ hBound' hFatou
