-- Prove2me | solution 1 for AvramDividend.Classical.causal_primitive_C1_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:30:37.314265+00:00
-- url     : https://prove2.me/submissions/60c3efbb-40c3-4f1a-98ce-d83b71bde858

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem solution
    (g : ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, g s ∂volume)
      (Ioi (0 : ℝ)) ∧
    (∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R →
        |∫ s in Ioc (0 : ℝ) x, g s ∂volume| ≤ C) := by
  let G : ℝ → ℝ := fun x => ∫ s in Ioc (0 : ℝ) x, g s ∂volume
  have hDeriv (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt G (g x) x := by
    have hx0 : (0 : ℝ) < x := hx
    have hnhds : Ici (0 : ℝ) ∈ 𝓝 x :=
      Filter.mem_of_superset (Ioi_mem_nhds hx) Set.Ioi_subset_Ici_self
    have hAt : ContinuousAt g x := hg.continuousAt hnhds
    have hMeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi
        (hg.mono Set.Ioi_subset_Ici_self)) x hx
    have hInt : IntervalIntegrable g volume (0 : ℝ) x := by
      apply ContinuousOn.intervalIntegrable
      apply hg.mono
      intro y hy
      have hxy : y ∈ Icc (0 : ℝ) x := by
        simpa [Set.uIcc_of_le hx0.le] using hy
      exact hxy.1
    have hFTC : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, g s) (g x) x :=
      intervalIntegral.integral_hasDerivAt_right hInt
        hMeas hAt
    apply hFTC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  have hC1 : ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).2
    constructor
    · intro x hx
      exact (hDeriv x hx).differentiableAt.differentiableWithinAt
    · apply (hg.mono Set.Ioi_subset_Ici_self).congr
      intro x hx
      rw [derivWithin_of_isOpen isOpen_Ioi hx]
      exact (hDeriv x hx).deriv
  constructor
  · exact hC1
  · intro R hR
    have hcont : ContinuousOn g (Icc (0 : ℝ) R) :=
      hg.mono (by intro y hy; exact hy.1)
    obtain ⟨C, hC⟩ :=
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) R)).exists_bound_of_continuousOn hcont
    have hCnonneg : 0 ≤ C := by
      have h0 := hC 0 (show (0 : ℝ) ∈ Icc 0 R from ⟨le_refl _, hR.le⟩)
      exact le_trans (norm_nonneg (g 0)) h0
    refine ⟨C * R, ?_⟩
    intro x hx
    have hnorm :
        ‖∫ s in (0 : ℝ)..x, g s‖ ≤ C * |x - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      apply hC y
      have hy' : y ∈ Ioc (0 : ℝ) x := by
        simpa [Set.uIoc_of_le hx.1.le] using hy
      exact ⟨hy'.1.le, le_trans hy'.2 hx.2⟩
    have hbound : |∫ s in Ioc (0 : ℝ) x, g s ∂volume| ≤ C * x := by
      simpa [intervalIntegral.integral_of_le hx.1.le,
        Real.norm_eq_abs, abs_of_nonneg hx.1.le] using hnorm
    exact le_trans hbound (mul_le_mul_of_nonneg_left hx.2 hCnonneg)