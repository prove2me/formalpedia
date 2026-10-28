-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_integrable_tsum_of_summable_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:09:41.365444+00:00
-- url     : https://prove2.me/submissions/de9cb4a5-b211-4ab9-9568-dd6ba50a7a7d

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- A pointwise nonnegative renewal-power sum is integrable if its masses sum. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ)
    (hFi : ∀ n : ℕ, Integrable (F n) μ)
    (hpos : ∀ n : ℕ, ∀ x : α, 0 ≤ F n x)
    (hpoint : ∀ x : α, Summable (fun n : ℕ => F n x))
    (hmass : Summable (fun n : ℕ => ∫ x : α, F n x ∂μ)) :
    Integrable (fun x : α => ∑' n : ℕ, F n x) μ := by
  have hmasspos (n : ℕ) : 0 ≤ ∫ x : α, F n x ∂μ :=
    integral_nonneg (hpos n)
  have hfinite :
      (∑' n : ℕ, ENNReal.ofReal (∫ x : α, F n x ∂μ)) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hmasspos hmass]
    simp
  have hlintegral :
      (∫⁻ x : α, ENNReal.ofReal (∑' n : ℕ, F n x) ∂μ) =
        ∑' n : ℕ, ENNReal.ofReal (∫ x : α, F n x ∂μ) := by
    calc
      (∫⁻ x : α, ENNReal.ofReal (∑' n : ℕ, F n x) ∂μ) =
          ∫⁻ x : α, ∑' n : ℕ, ENNReal.ofReal (F n x) ∂μ := by
        congr 1
        funext x
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => hpos n x) (hpoint x)
      _ = ∑' n : ℕ, ∫⁻ x : α, ENNReal.ofReal (F n x) ∂μ := by
        apply lintegral_tsum
        intro n
        exact (hFi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ = ∑' n : ℕ, ENNReal.ofReal (∫ x : α, F n x ∂μ) := by
        congr 1
        funext n
        exact (ofReal_integral_eq_lintegral_ofReal (hFi n)
          (Filter.Eventually.of_forall (hpos n))).symm
  have hmeas : AEMeasurable (fun x : α => ∑' n : ℕ, F n x) μ :=
    AEMeasurable.tsum (fun n => (hFi n).aemeasurable)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  change (∫⁻ x : α, ‖∑' n : ℕ, F n x‖ₑ ∂μ) < ⊤
  have hnorm (x : α) :
      ‖∑' n : ℕ, F n x‖ₑ = ENNReal.ofReal (∑' n : ℕ, F n x) := by
    rw [Real.enorm_eq_ofReal_abs]
    exact congrArg ENNReal.ofReal
      (abs_of_nonneg (tsum_nonneg (fun n => hpos n x)))
  simp_rw [hnorm]
  rw [hlintegral]
  exact hfinite
