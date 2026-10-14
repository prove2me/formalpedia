-- Prove2me | solution 1 for CauchyRiemannIndex.tendsto_eLpNorm_zero_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T23:21:49.587377+00:00
-- url     : https://prove2.me/submissions/8fb95f81-81b6-4321-9cc2-a2a78c1c6edf

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENNReal.Holder

namespace CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]

lemma enorm_le_enorm_of_le' {a : E} {b : ℝ} (h : ‖a‖ ≤ b) : ‖a‖ₑ ≤ ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (h.trans (le_abs_self b))

/-- Dominated convergence in `L^p`, `p < ∞`. -/
lemma tendsto_eLpNorm_zero_of_dominated {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {F : ℕ → α → E}
    {bound : α → ℝ} (hb : MemLp bound p μ) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hle : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (F k) p μ) atTop (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp]
  have h1 : Tendsto (fun k => ∫⁻ x, ‖F k x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖bound x‖ₑ ^ p.toReal)
      (fun k => ((hF k).enorm.pow_const _)) (fun k => ?_) ?_ ?_
    · filter_upwards [hle k] with x hx
      gcongr
      exact enorm_le_enorm_of_le' hx
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hb.2).ne
    · filter_upwards [hlim] with x hx
      have : Tendsto (fun k => ‖F k x‖ₑ) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : E)).comp hx
      have h2 := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp this
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hr] using h2
  rw [lintegral_zero] at h1
  have h3 := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h1
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hr)] using h3

/-- A positive measurable weight in `L^p` of a σ-finite measure. -/
lemma exists_pos_weight (μ : Measure α) [SigmaFinite μ] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) :
    ∃ w : α → ℝ, (∀ x, 0 < w x) ∧ Measurable w ∧ MemLp w p μ := by
  obtain ⟨g, gpos, gmeas, gint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine ⟨fun x => (g x : ℝ) ^ (1 / p.toReal), fun x => Real.rpow_pos_of_pos (gpos x) _,
    (measurable_coe_nnreal_real.comp gmeas).pow_const _, ?_⟩
  refine ⟨((measurable_coe_nnreal_real.comp gmeas).pow_const _).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp]
  have e : ∀ x, ‖(g x : ℝ) ^ (1 / p.toReal)‖ₑ ^ p.toReal = (g x : ℝ≥0∞) := by
    intro x
    have h0 : (0 : ℝ) ≤ (g x : ℝ) ^ (1 / p.toReal) := Real.rpow_nonneg (g x).coe_nonneg _
    rw [Real.enorm_of_nonneg h0]
    rw [ENNReal.ofReal_rpow_of_nonneg h0 hr.le]
    rw [← Real.rpow_mul (g x).coe_nonneg, one_div_mul_cancel hr.ne', Real.rpow_one, ENNReal.ofReal_coe_nnreal]
  simp_rw [e]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (gint.trans ENNReal.one_lt_top).ne

end CauchyRiemannIndex.LpDual

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {F : ℕ → α → E}
    {bound : α → ℝ} (hb : MemLp bound p μ) (hF : ∀ k, AEStronglyMeasurable (F k) μ)
    (hle : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (F k) p μ) atTop (𝓝 0) :=
  CauchyRiemannIndex.LpDual.tendsto_eLpNorm_zero_of_dominated hp0 hp hb hF hle hlim
