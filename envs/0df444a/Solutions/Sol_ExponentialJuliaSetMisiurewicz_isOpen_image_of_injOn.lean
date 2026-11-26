-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isOpen_image_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:37.621505+00:00
-- url     : https://prove2.me/submissions/288ee931-3fd1-4ac8-b964-eaba8f3e1c47

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hinj : Set.InjOn g U) :
    IsOpen (g '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, rfl⟩
  have hnhds : U ∈ 𝓝 z := hU.mem_nhds hz
  have hana : AnalyticAt ℂ g z := hg.analyticAt hnhds
  rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
  · exfalso
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hconst.and hnhds)
    have hmem : z + (δ / 2 : ℝ) ∈ ball z δ := by
      simp [Metric.mem_ball, dist_eq_norm]
      rw [abs_of_pos (by linarith)]
      linarith
    obtain ⟨heq, hin⟩ := hsub hmem
    have hzz : z + (δ / 2 : ℝ) = z := hinj hin hz heq
    have hne : ((δ / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      linarith
    exact hne (by linear_combination hzz - (rfl : z = z))
  · exact hmap (Filter.image_mem_map hnhds)
end ExponentialJuliaSetMisiurewicz
