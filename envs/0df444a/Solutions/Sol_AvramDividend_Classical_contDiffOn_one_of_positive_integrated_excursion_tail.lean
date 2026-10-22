-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_positive_integrated_excursion_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T23:14:18.74044+00:00
-- url     : https://prove2.me/submissions/7c55ec34-2dee-452f-88de-fdb316119145

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory intervalIntegral

theorem solution (T W : ℝ → ℝ) (a c : ℝ) (ha : 0 < a)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, T t)) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  let s : Set ℝ := Ioi (0 : ℝ)
  let F : ℝ → ℝ := fun x => ∫ t in a..x, T t
  have hs : IsOpen s := isOpen_Ioi
  have hF_at (x : ℝ) (hx : x ∈ s) : HasDerivAt F (T x) x := by
    have hsub : uIcc a x ⊆ s := by
      intro y hy
      have hlo : min a x ≤ y := by
        rcases (mem_uIcc.mp hy) with h | h
        · exact (min_le_left a x).trans h.1
        · exact (min_le_right a x).trans h.1
      exact lt_of_lt_of_le (lt_min ha hx) hlo
    have hi : IntervalIntegrable T volume a x :=
      (hT.mono hsub).intervalIntegrable
    have hm : StronglyMeasurableAtFilter T (nhds x) volume :=
      ContinuousOn.stronglyMeasurableAtFilter hs hT x hx
    have hc : ContinuousAt T x := hT.continuousAt (hs.mem_nhds hx)
    exact intervalIntegral.integral_hasDerivAt_right hi hm hc
  have hFdiff : DifferentiableOn ℝ F s := by
    intro x hx
    exact (hF_at x hx).differentiableAt.differentiableWithinAt
  have hFderiv : ContinuousOn (derivWithin F s) s := by
    apply hT.congr
    intro x hx
    rw [derivWithin_of_isOpen (f := F) hs hx]
    exact (hF_at x hx).deriv
  have hF : ContDiffOn ℝ 1 F s :=
    (contDiffOn_one_iff_derivWithin hs.uniqueDiffOn).2
      ⟨hFdiff, hFderiv⟩
  have hE : ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (F x)) s :=
    hF.exp
  have hC : ContDiffOn ℝ 1 (fun _ : ℝ => c) s :=
    (contDiff_const (𝕜 := ℝ) (E := ℝ) (F := ℝ) (c := c)).contDiffOn
  have hP : ContDiffOn ℝ 1
      (fun x : ℝ => c * Real.exp (F x)) s := hC.mul hE
  exact hP.congr (fun x hx => hW x hx)
