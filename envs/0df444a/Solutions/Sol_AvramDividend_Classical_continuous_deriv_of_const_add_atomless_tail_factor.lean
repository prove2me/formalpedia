-- Prove2me | solution 1 for AvramDividend.Classical.continuous_deriv_of_const_add_atomless_tail_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:48:31.059545+00:00
-- url     : https://prove2.me/submissions/50e36188-e434-439e-aa93-72b367df5e83

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Ici_of_finite_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Ici x) ≠ ⊤)
    (φ : ℝ) (W : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    ContinuousOn (deriv W) (Ioi 0) := by
  have htail : Continuous (fun x : ℝ => μ.real (Ici x)) :=
    continuous_measureReal_Ici_of_finite_noAtoms μ hfin
  have hsum : Continuous (fun x : ℝ => φ + μ.real (Ici x)) :=
    continuous_const.add htail
  have hprod :
      ContinuousOn (fun x : ℝ => W x * (φ + μ.real (Ici x))) (Ioi 0) :=
    hWcont.mul hsum.continuousOn
  exact hprod.congr (by
    intro x hx
    exact hderiv x hx)
