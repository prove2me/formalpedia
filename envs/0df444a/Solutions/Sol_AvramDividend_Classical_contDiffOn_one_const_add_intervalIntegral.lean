-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_const_add_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T02:52:34.022529+00:00
-- url     : https://prove2.me/submissions/1aa588d1-ccb6-466d-a286-604bc6b4eb1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (f : ℝ → ℝ) (c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) :
    ContDiffOn ℝ 1 (fun x : ℝ => c + ∫ y in (0 : ℝ)..x, f y) (Ioi 0) := by
  have hprim : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun u : ℝ => ∫ y in (0 : ℝ)..u, f y) (f x) x := by
    intro x hx
    have hII : IntervalIntegrable f volume 0 x := hint x hx
    have hxmem : x ∈ Ioi (0 : ℝ) := hx
    have hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
      hcont.stronglyMeasurableAtFilter isOpen_Ioi x hxmem
    have hmem' : Ioi (0 : ℝ) ∈ 𝓝 x := isOpen_Ioi.mem_nhds hxmem
    have hcat : ContinuousAt f x := hcont.continuousAt hmem'
    exact intervalIntegral.integral_hasDerivAt_right hII hmeas hcat
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun u : ℝ => c + ∫ y in (0 : ℝ)..u, f y) (f x) x := by
    intro x hx
    have h := (hprim x hx).add_const c
    have hfun : (fun u : ℝ => (∫ y in (0 : ℝ)..u, f y) + c)
        = (fun u : ℝ => c + ∫ y in (0 : ℝ)..u, f y) := by
      funext u
      exact add_comm _ _
    rw [hfun] at h
    exact h
  have hdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (fun u : ℝ => c + ∫ y in (0 : ℝ)..u, f y) x :=
    fun x hx => (hderiv x hx).differentiableAt
  have hderivcont : ContinuousOn
      (deriv (fun u : ℝ => c + ∫ y in (0 : ℝ)..u, f y)) (Ioi 0) := by
    refine hcont.congr ?_
    intro x hx
    have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
    rw [(hderiv x hxpos).deriv]
  exact contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
    (fun u : ℝ => c + ∫ y in (0 : ℝ)..u, f y) hdiff hderivcont
