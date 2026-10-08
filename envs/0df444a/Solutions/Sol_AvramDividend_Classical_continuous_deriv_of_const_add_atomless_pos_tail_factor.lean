-- Prove2me | solution 1 for AvramDividend.Classical.continuous_deriv_of_const_add_atomless_pos_tail_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:13:18.742457+00:00
-- url     : https://prove2.me/submissions/3773d0c2-24f3-421c-bcfd-26bfe4a98969

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_pos_finite_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (φ : ℝ) (W : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    ContinuousOn (deriv W) (Ioi 0) := by
  have htail :
      ContinuousOn (fun x : ℝ => μ.real (Ici x)) (Ioi 0) :=
    continuousOn_measureReal_Ici_of_pos_finite_noAtoms μ hfin
  have hsum :
      ContinuousOn (fun x : ℝ => φ + μ.real (Ici x)) (Ioi 0) :=
    continuousOn_const.add htail
  have hprod :
      ContinuousOn (fun x : ℝ => W x * (φ + μ.real (Ici x))) (Ioi 0) :=
    hWcont.mul hsum
  exact hprod.congr (by
    intro x hx
    exact hderiv x hx)
