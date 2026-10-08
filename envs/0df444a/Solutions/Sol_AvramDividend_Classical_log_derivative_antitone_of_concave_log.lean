-- Prove2me | solution 1 for AvramDividend.Classical.log_derivative_antitone_of_concave_log
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:22:24.899507+00:00
-- url     : https://prove2.me/submissions/97c82611-63b1-4f2f-bccd-138071c999d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped Topology

theorem solution
    (V g : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hlogconcave :
      ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x) :
    AntitoneOn g (Ioi (0 : ℝ)) := by
  let L : ℝ → ℝ := fun x => Real.log (V x)
  have hL (x : ℝ) (hx : 0 < x) : HasDerivAt L (g x) x := by
    have hv : V x ≠ 0 := ne_of_gt (hVpos x hx)
    have hd := (hderiv x hx).log hv
    have he : V x * g x / V x = g x := by
      field_simp [hv]
    simpa only [L, he] using hd
  have hdif : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ L x := by
    intro x hx
    exact (hL x hx).differentiableAt
  have hanti : AntitoneOn (deriv L) (Ioi (0 : ℝ)) :=
    hlogconcave.antitoneOn_deriv hdif
  intro x hx y hy hxy
  have hxy' := hanti hx hy hxy
  simpa only [(hL x hx).deriv, (hL y hy).deriv] using hxy'
