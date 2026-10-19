-- Prove2me | solution 1 for CohnElkies.norm_extension_le_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/fae21345-ff96-4181-9c1b-0c8b45c10c2f

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
namespace CohnElkies
theorem _root_.solution
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
  classical
  by_cases hnonempty : U.Nonempty
  · have hproper : U ≠ (Set.univ : Set ℂ) := by
      intro hu
      rw [hu] at hbounded
      exact NormedSpace.unbounded_univ ℂ ℂ hbounded
    have hcompact : IsCompact (closure U) :=
      hbounded.isCompact_closure
    obtain ⟨w, hwclosure, hwmax⟩ :=
      hcompact.exists_isMaxOn hnonempty.closure hN
    have hwcases : w ∈ U ∨ w ∈ frontier U := by
      rw [closure_eq_interior_union_frontier,
        hopen.interior_eq, Set.mem_union] at hwclosure
      exact hwclosure
    have hwbound : N w ≤ C := by
      rcases hwcases with hWinterior | hWfrontier
      · have hmaxnorm :
            IsMaxOn (norm ∘ f) U w := by
          intro x hx
          change ‖f x‖ ≤ ‖f w‖
          rw [← hinterior x hx,
            ← hinterior w hWinterior]
          exact hwmax (subset_closure hx)
        have hconstant :=
          Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
            hconnected hopen hf hWinterior hmaxnorm
        have hrealconstant :
            Set.EqOn N (Function.const ℂ (N w)) U := by
          intro x hx
          calc
            N x = ‖f x‖ := hinterior x hx
            _ = ‖f w‖ := by
              simpa [Function.comp_def, Function.const] using!
                hconstant hx
            _ = N w := (hinterior w hWinterior).symm
        have hclosedconstant :=
          hrealconstant.of_subset_closure hN
            continuousOn_const subset_closure Subset.rfl
        obtain ⟨t, ht⟩ :=
          nonempty_frontier_iff.mpr
            ⟨hnonempty, hproper⟩
        have htclosure : t ∈ closure U :=
          frontier_subset_closure ht
        calc
          N w = N t := by
            symm
            simpa [Function.const] using!
              hclosedconstant htclosure
          _ ≤ C := hfrontier t ht
      · exact hfrontier w hWfrontier
    exact le_trans (hwmax hz) hwbound
  · have hempty : U = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hempty] at hz
end CohnElkies
