-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_finite_grid_stopping_square_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:10:55.861687+00:00
-- url     : https://prove2.me/submissions/9b3b4096-429a-4d96-b1ed-ba9b1bc7b0c0

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv,
LSV/LocalizedStoppingL2Convergence.lean continuous_martingale_stopping_square_le,
and LSV/LocalizedOptionalSamplingL1.lean finite-grid stopped conditional expectation,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719.
Upstream CC BY 4.0, attribution to original source authors.
The stop is restricted to countable range, using Mathlib's finite/countable-grid
conditional sampling identity; the stronger arbitrary-stop limit is not asserted.
-/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ μ)
    (t : ℝ≥0) (hM2 : MemLp (M t) 2 μ)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ)
    (hτle : ∀ ω, τ ω ≤ (t : WithTop ℝ≥0))
    (hτcount : (range τ).Countable) :
    MemLp (stoppedValue M τ) 2 μ ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂μ) ≤
        ∫ ω, (M t ω)^2 ∂μ := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτle hτcount
  have hce : MemLp (μ[M t | hτ.measurableSpace]) 2 μ :=
    MemLp.condExp (m := hτ.measurableSpace) (by norm_num) hM2
  refine ⟨(memLp_congr_ae he).2 hce, ?_⟩
  have hi : Integrable (fun ω => ‖M t ω‖^(2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hM2.integrable_sq
  have hh := integral_norm_condExp_rpow_le (m := hτ.measurableSpace)
    (by norm_num : (1 : ℝ) ≤ 2) hi
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hh
  rw [integral_congr_ae (he.mono (fun _ h =>
    congrArg (fun x : ℝ => x^2) h))]
  exact hh

