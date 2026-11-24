-- Prove2me | solution 1 for GaussianPerimeter.lintegral_le_liminf_of_eventually_le_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:12:32.29072+00:00
-- url     : https://prove2.me/submissions/2b13a7bd-9eb1-43e5-861c-5f7e295da295

module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.LiminfLimsup
public import Definitions.Def_GaussianPerimeter_Basic

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n))
    (hg : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (F x)))
    (hgf : ∀ x, ∀ᶠ n in atTop, g n x ≤ f n x) :
    (∫⁻ x, F x ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  refine le_trans (lintegral_mono fun x => ?_) (lintegral_liminf_le hf)
  rw [← (hg x).liminf_eq]
  exact liminf_le_liminf (hgf x)
end GaussianPerimeter
