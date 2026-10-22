-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_kernel_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:19:00.865402+00:00
-- url     : https://prove2.me/submissions/39b74635-3040-4d73-bef4-100486cfa04f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_continuous_time
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_antitone
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal
open AvramDividend.Classical

/-- The Gaussian Esscher double-tail kernel is continuous at every positive time. -/
theorem solution (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ => ∫⁻ z : ℝ,
      (if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) t := by
  let K : ℝ → ℝ → ENNReal := fun u z =>
    if 0 < u ∧ u < z then
      ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
    else 0
  have hδ : 0 < t / 2 := half_pos ht
  have hδt : t / 2 < t := by linarith
  have hmeas (u : ℝ) : Measurable (K u) := by
    have h1 : MeasurableSet {z : ℝ | 0 < u} := by
      by_cases hu : 0 < u <;> simp [hu]
    have h2 : MeasurableSet {z : ℝ | u < z} :=
      measurableSet_lt measurable_const measurable_id
    have hs : MeasurableSet {z : ℝ | 0 < u ∧ u < z} := h1.inter h2
    have hk : Measurable (fun z : ℝ =>
      ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))) := by
      fun_prop
    exact hk.ite hs measurable_const
  have hevent : ∀ᶠ u in 𝓝 t, t / 2 ≤ u := by
    filter_upwards [isOpen_Ioi.mem_nhds hδt] with u hu
    exact hu.le
  have hbound : ∀ᶠ u in 𝓝 t, ∀ᵐ z : ℝ ∂μ, K u z ≤ K (t / 2) z := by
    filter_upwards [hevent] with u hu
    exact Filter.Eventually.of_forall (fun z =>
      gaussian_double_tail_atom_antitone φ (t / 2) u z hδ hu)
  have hfin : (∫⁻ z : ℝ, K (t / 2) z ∂μ) ≠ ∞ :=
    ne_of_lt (gaussian_double_tail_kernel_finite_positive
      μ φ hφ hlevy (t / 2) hδ)
  have hlim : ∀ᵐ z : ℝ ∂μ,
      Tendsto (fun u : ℝ => K u z) (𝓝 t) (𝓝 (K t z)) :=
    Filter.Eventually.of_forall (fun z =>
      gaussian_double_tail_atom_continuous_time φ z t ht)
  change Tendsto (fun u : ℝ => ∫⁻ z : ℝ, K u z ∂μ)
    (𝓝 t) (𝓝 (∫⁻ z : ℝ, K t z ∂μ))
  exact tendsto_lintegral_filter_of_dominated_convergence
    (l := 𝓝 t) (F := K) (f := K t) (K (t / 2))
    (Filter.Eventually.of_forall hmeas) hbound hfin hlim
