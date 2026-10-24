-- Prove2me | solution 1 for FiniteEnergyPlane.exists_fderiv_ne_zero_of_isCompact_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-23T16:07:29.372029+00:00
-- url     : https://prove2.me/submissions/2097b8d1-55d3-4554-8dda-f93c4a5f8b6e

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen



namespace FiniteEnergyPlane

open Metric Filter Topology

/-- Let `u` be differentiable on an open set `U ⊆ ℂ` and let `p ∈ u(U)` have compact fibre
`U ∩ u⁻¹(p)`. Then every neighbourhood `B_ε(p)` contains a value `u(z)`, `z ∈ U`, at which the
derivative of `u` is nonzero. -/
theorem exists_fderiv_ne_zero_of_isCompact_fiber_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F} (hu : DifferentiableOn ℝ u U)
    {p : F} (hp : p ∈ u '' U) (hK : IsCompact (U ∩ u ⁻¹' {p})) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ U, ‖u z - p‖ < ε ∧ fderiv ℝ u z ≠ 0 := by
  by_contra h
  push_neg at h
  set T := U ∩ u ⁻¹' {p} with hT
  have hTo : IsOpen T := by
    rw [Metric.isOpen_iff]
    intro z hz
    have hzU : z ∈ U := hz.1
    have hcz : ContinuousAt u z := ((hu z hzU).differentiableAt (hU.mem_nhds hzU)).continuousAt
    have h1 : ∀ᶠ w in 𝓝 z, w ∈ U ∧ ‖u w - p‖ < ε := by
      refine (hU.eventually_mem hzU).and ?_
      have : ‖u z - p‖ < ε := by simp [show u z = p from hz.2, hε]
      exact (hcz.sub continuousAt_const).norm.eventually (gt_mem_nhds this)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 h1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have hdiff : DifferentiableOn ℝ u (ball z δ) := fun y hy =>
      ((hu y (hball y hy).1).differentiableAt (hU.mem_nhds (hball y hy).1)).differentiableWithinAt
    have hconst : u w = u z := by
      refine (convex_ball z δ).is_const_of_fderivWithin_eq_zero hdiff (fun y hy => ?_) hw
        (mem_ball_self hδ)
      rw [fderivWithin_of_isOpen isOpen_ball hy]
      exact h y (hball y hy).1 (hball y hy).2
    exact ⟨(hball w hw).1, by simp [hconst, show u z = p from hz.2]⟩
  have hTc : IsClosed T := hK.isClosed
  obtain ⟨z, hzU, hzp⟩ := hp
  have hne : T.Nonempty := ⟨z, hzU, hzp⟩
  have huniv : T = Set.univ := IsClopen.eq_univ ⟨hTc, hTo⟩ hne
  exact noncompact_univ ℂ (huniv ▸ hK)

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → F} (hu : DifferentiableOn ℝ u U)
    {p : F} (hp : p ∈ u '' U) (hK : IsCompact (U ∩ u ⁻¹' {p})) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ U, ‖u z - p‖ < ε ∧ fderiv ℝ u z ≠ 0 :=
  exists_fderiv_ne_zero_of_isCompact_fiber_aux hU hu hp hK hε
