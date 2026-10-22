-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_continuous_excursion_log_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:46:55.319785+00:00
-- url     : https://prove2.me/submissions/54e37046-d4cd-4712-8c25-5f3b2f08db39

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (W T : ℝ → ℝ) (φ : ℝ)
    (hd : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) → DifferentiableAt ℝ W x)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hDeriv : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      deriv W x = W x * (φ + T x)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  let s : Set ℝ := Ioi (0 : ℝ)
  have hs : IsOpen s := isOpen_Ioi
  have hdiffOn : DifferentiableOn ℝ W s := by
    intro x hx
    exact (hd x hx).differentiableWithinAt
  have hWcont : ContinuousOn W s := hdiffOn.continuousOn
  have hsum : ContinuousOn (fun x : ℝ => φ + T x) s :=
    continuousOn_const.add hT
  have hproduct : ContinuousOn (fun x : ℝ => W x * (φ + T x)) s :=
    hWcont.mul hsum
  have hderiv_cont : ContinuousOn (deriv W) s := by
    exact hproduct.congr (fun x hx => hDeriv x hx)
  have hwithin_cont : ContinuousOn (derivWithin W s) s := by
    apply hderiv_cont.congr
    intro x hx
    exact (derivWithin_of_isOpen (f := W) hs hx)
  exact (contDiffOn_one_iff_derivWithin hs.uniqueDiffOn).2
    ⟨hdiffOn, hwithin_cont⟩
