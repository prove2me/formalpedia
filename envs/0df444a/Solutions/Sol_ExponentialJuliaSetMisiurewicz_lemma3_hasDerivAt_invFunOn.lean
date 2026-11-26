-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma3_hasDerivAt_invFunOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:38.702216+00:00
-- url     : https://prove2.me/submissions/56db51b0-ae16-43fe-8aa2-cd770c4d71c4

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_image_of_injOn
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_isOpen_image

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball b r))
    (hinj : Set.InjOn g (ball b r))
    (hne : ∀ z ∈ ball b r, deriv g z ≠ 0)
    {w : ℂ} (hw : w ∈ g '' ball b r) :
    HasDerivAt (Function.invFunOn g (ball b r))
      (deriv g (Function.invFunOn g (ball b r) w))⁻¹ w := by
  have hleft : ∀ u ∈ ball b r, Function.invFunOn g (ball b r) (g u) = u := by
    intro u hu
    have hex : ∃ a ∈ ball b r, g a = g u := ⟨u, hu, rfl⟩
    exact hinj (Function.invFunOn_mem hex) hu (Function.invFunOn_eq hex)
  obtain ⟨z, hz, rfl⟩ := hw
  have hhz : Function.invFunOn g (ball b r) (g z) = z := hleft z hz
  have hcont : ContinuousAt (Function.invFunOn g (ball b r)) (g z) := by
    rw [continuousAt_def]
    intro V hV
    rw [hhz] at hV
    obtain ⟨W, hWsub, hWopen, hzW⟩ := _root_.mem_nhds_iff.mp hV
    have hUopen : IsOpen (W ∩ ball b r) := hWopen.inter isOpen_ball
    have hUsub : W ∩ ball b r ⊆ ball b r := Set.inter_subset_right
    have hgU : IsOpen (g '' (W ∩ ball b r)) :=
      isOpen_image_of_injOn hUopen (hg.mono hUsub) (hinj.mono hUsub)
    refine Filter.mem_of_superset (hgU.mem_nhds ⟨z, ⟨hzW, hz⟩, rfl⟩) ?_
    rintro y ⟨u, hu, rfl⟩
    have hfix : Function.invFunOn g (ball b r) (g u) = u := hleft u hu.2
    rw [Set.mem_preimage, hfix]
    exact hWsub hu.1
  have hd : HasDerivAt g (deriv g z) z :=
    (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hfg : ∀ᶠ y in 𝓝 (g z), g (Function.invFunOn g (ball b r) y) = y := by
    filter_upwards [(lemma3_isOpen_image hg hinj).mem_nhds ⟨z, hz, rfl⟩] with y hy
    exact Function.invFunOn_eq hy
  rw [hhz]
  exact HasDerivAt.of_local_left_inverse hcont (by rw [hhz]; exact hd) (hne z hz) hfg
end ExponentialJuliaSetMisiurewicz
