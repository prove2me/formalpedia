-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_continuous_integrated_excursion_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T23:08:16.029318+00:00
-- url     : https://prove2.me/submissions/c367d5f2-6f81-4035-964e-8e0a70d7df02

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory intervalIntegral

theorem solution (T W : ℝ → ℝ) (a c : ℝ)
    (hT : Continuous T)
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, T t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  have hFdiff : Differentiable ℝ
      (fun x : ℝ => ∫ t in a..x, T t) :=
    intervalIntegral.differentiable_integral_of_continuous hT
  have hFderiv : Continuous
      (deriv (fun x : ℝ => ∫ t in a..x, T t)) := by
    have heq : (deriv (fun x : ℝ => ∫ t in a..x, T t)) = T := by
      funext x
      exact Continuous.deriv_integral T hT a x
    rw [heq]
    exact hT
  have hF : ContDiff ℝ 1
      (fun x : ℝ => ∫ t in a..x, T t) :=
    (contDiff_one_iff_deriv).2 ⟨hFdiff, hFderiv⟩
  have hE : ContDiff ℝ 1
      (fun x : ℝ => Real.exp (∫ t in a..x, T t)) := hF.exp
  have hP : ContDiff ℝ 1
      (fun x : ℝ => c * Real.exp (∫ t in a..x, T t)) := by
    exact (contDiff_const (𝕜 := ℝ) (E := ℝ) (F := ℝ) (c := c)).mul hE
  exact hP.contDiffOn.congr (fun x hx => hW x hx)
