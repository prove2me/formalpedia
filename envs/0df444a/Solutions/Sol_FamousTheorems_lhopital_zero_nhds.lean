-- Prove2me | solution 1 for FamousTheorems.lhopital_zero_nhds
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:06:24.803774+00:00
-- url     : https://prove2.me/submissions/8657dece-16e1-4f2e-9859-07e143a32448

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem solution {f g : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝 a, deriv g x ≠ 0)
    (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝 a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l :=
  deriv.lhopital_zero_nhds hdf hg' hfa hga hdiv
