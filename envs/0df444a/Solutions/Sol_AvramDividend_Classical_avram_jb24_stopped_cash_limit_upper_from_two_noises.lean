-- Prove2me | solution 1 for AvramDividend.Classical.avram_jb24_stopped_cash_limit_upper_from_two_noises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:30:55.280269+00:00
-- url     : https://prove2.me/submissions/4588047a-9e8d-44bd-84bd-f2d68315a8b1

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite-grid cash upper bounds survive the joint stopped noise and error limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (b : ℝ) (F MG MJ : Ω → ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hG : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJ : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hE : ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hUpper : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ b + G k ω + J k ω + E k ω) :
    ∀ᵐ ω ∂P, F ω ≤ b + MG ω + MJ ω := by
  have hAll : ∀ᵐ ω ∂P, ∀ k,
      F ω ≤ b + G k ω + J k ω + E k ω :=
    ae_all_iff.mpr hUpper
  filter_upwards [hG, hJ, hE, hAll] with ω hg hj he hbound
  have hb : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) :=
    tendsto_const_nhds
  have hlim : Tendsto
      (fun k => b + G k ω + J k ω + E k ω)
      atTop (𝓝 (b + MG ω + MJ ω)) := by
    simpa only [add_zero] using (((hb.add hg).add hj).add he)
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
