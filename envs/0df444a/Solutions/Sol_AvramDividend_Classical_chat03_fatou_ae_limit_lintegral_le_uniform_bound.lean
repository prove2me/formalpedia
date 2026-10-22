-- Prove2me | solution 1 for AvramDividend.Classical.chat03_fatou_ae_limit_lintegral_le_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T10:00:36.087831+00:00
-- url     : https://prove2.me/submissions/0152d113-1a01-4a18-94bf-8e5c23d2ed07

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.LiminfLimsup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-!
Fatou's lemma preserves any uniform upper bound on the nonnegative
Lebesgue integrals under almost-everywhere convergence.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (G : Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hFm : ∀ n, AEMeasurable (F n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (hB : ∀ n, (∫⁻ ω, F n ω ∂P) ≤ B) :
    (∫⁻ ω, G ω ∂P) ≤ B := by
  have hliminf :
      ∀ᵐ ω ∂P, liminf (fun n => F n ω) atTop = G ω := by
    filter_upwards [hconv] with ω hω
    exact hω.liminf_eq
  calc
    (∫⁻ ω, G ω ∂P) =
        (∫⁻ ω, liminf (fun n => F n ω) atTop ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [hliminf] with ω hω
      exact hω.symm
    _ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop :=
      lintegral_liminf_le' hFm
    _ ≤ B := by
      apply Filter.liminf_le_of_le (hf := by isBoundedDefault)
      intro b hb
      obtain ⟨n, hbn, hnB⟩ :=
        (hb.and (Filter.Eventually.of_forall hB)).exists
      exact hbn.trans hnB
