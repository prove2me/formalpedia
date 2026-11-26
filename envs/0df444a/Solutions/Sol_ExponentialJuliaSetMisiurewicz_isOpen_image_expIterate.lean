-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.isOpen_image_expIterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:36.404512+00:00
-- url     : https://prove2.me/submissions/4025b33c-2f39-4fa9-812b-5f6c7583d068

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_deriv_expIterate_ne_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiable_expIterate


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {V : Set ℂ} (hV : IsOpen V) (n : ℕ) :
    IsOpen (expIterate n '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨z, hz, rfl⟩
  have hnhds : V ∈ 𝓝 z := hV.mem_nhds hz
  have hana : AnalyticAt ℂ (expIterate n) z :=
    (differentiable_expIterate n).differentiableOn.analyticAt hnhds
  rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
  · exfalso
    have heq : expIterate n =ᶠ[𝓝 z] fun _ => expIterate n z := hconst
    have : deriv (expIterate n) z = 0 := by
      rw [heq.deriv_eq, deriv_const]
    exact deriv_expIterate_ne_zero n z this
  · exact hmap (Filter.image_mem_map hnhds)
end ExponentialJuliaSetMisiurewicz
