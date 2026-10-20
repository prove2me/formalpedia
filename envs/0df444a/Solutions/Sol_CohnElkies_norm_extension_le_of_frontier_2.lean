-- Prove2me | solution 2 for CohnElkies.norm_extension_le_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:22.582252+00:00
-- url     : https://prove2.me/submissions/cb8255a5-eca6-4e24-ab25-5a1ef8484e54

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology


theorem solution
    {U : Set ℂ}
    (hopen : IsOpen U)
    (hconnected : IsPreconnected U)
    (hbounded : Bornology.IsBounded U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {N : ℂ → ℝ}
    (hN : ContinuousOn N (closure U))
    (hinterior : ∀ z ∈ U, N z = ‖f z‖)
    {C : ℝ}
    (hfrontier : ∀ z ∈ frontier U, N z ≤ C)
    {z : ℂ} (hz : z ∈ closure U) :
    N z ≤ C := by
  have hK : IsCompact (closure U) := hbounded.isCompact_closure
  obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn ⟨z, hz⟩ hN
  have hzw : N z ≤ N w := isMaxOn_iff.mp hmax z hz
  by_cases hwf : w ∈ frontier U
  · exact hzw.trans (hfrontier w hwf)
  · have hwU : w ∈ U := by
      by_contra h
      exact hwf ⟨hw, by rwa [hopen.interior_eq]⟩
    have hmaxU : IsMaxOn (norm ∘ f) U w := by
      refine isMaxOn_iff.mpr (fun y hy => ?_)
      simp only [Function.comp]
      rw [← hinterior y hy, ← hinterior w hwU]
      exact isMaxOn_iff.mp hmax y (subset_closure hy)
    have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hconnected hopen hf hwU hmaxU
    have hNU : EqOn N (fun _ => N w) U := fun y hy => by
      have h1 := heq hy
      simp only [Function.comp, Function.const_apply] at h1
      simp only
      rw [hinterior y hy, h1, hinterior w hwU]
    have hNcl : EqOn N (fun _ => N w) (closure U) :=
      hNU.of_subset_closure hN continuousOn_const subset_closure le_rfl
    have hUne : U.Nonempty := ⟨w, hwU⟩
    have hUuniv : U ≠ Set.univ := fun h => NormedSpace.unbounded_univ ℝ ℂ (h ▸ hbounded)
    obtain ⟨p, hp⟩ := nonempty_frontier_iff.mpr ⟨hUne, hUuniv⟩
    have h2 := hNcl (frontier_subset_closure hp)
    simp only at h2
    linarith [hfrontier p hp]

