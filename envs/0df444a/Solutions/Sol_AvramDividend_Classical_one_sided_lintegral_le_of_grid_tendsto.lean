-- Prove2me | solution 1 for AvramDividend.Classical.one_sided_lintegral_le_of_grid_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:02:24.934847+00:00
-- url     : https://prove2.me/submissions/c3cc747b-e146-4f89-9dfe-28ba822f341f

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Order.LiminfLimsup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (B : ℝ≥0∞)
    (hB : ∀ n, (∫⁻ ω, f n ω ∂P) ≤ B) :
    (∫⁻ ω, g ω ∂P) ≤ B := by
  have hbounded : (atTop : Filter ℕ).IsBoundedUnder (· ≥ ·)
      (fun n : ℕ => ∫⁻ ω, f n ω ∂P) := by
    apply Filter.isBoundedUnder_of
    exact ⟨0, fun _ => bot_le⟩
  have hliminf : (liminf
      (fun n : ℕ => ∫⁻ ω, f n ω ∂P) atTop) ≤ B := by
    refine Filter.liminf_le_of_le (hf := hbounded) ?_
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact le_trans hn (hB n)
  calc
    (∫⁻ ω, g ω ∂P) =
        (∫⁻ ω, liminf (fun n : ℕ => f n ω) atTop ∂P) := by
      apply lintegral_congr
      intro ω
      exact (Filter.Tendsto.liminf_eq (hlim ω)).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ ω, f n ω ∂P) atTop :=
      lintegral_liminf_le (μ := P) hf
    _ ≤ B := hliminf
