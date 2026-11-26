-- Prove2me | solution 1 for FriedCrossing.OrderCount.finrank_middle_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:43:52.634075+00:00
-- url     : https://prove2.me/submissions/1375691b-8508-476e-b470-301402b70c4c

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.OrderCount
variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup V₃] [Module K V₃]
namespace FriedCrossing.OrderCount
theorem _root_.solution (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    Module.finrank K V₂ = Module.finrank K V₁ + Module.finrank K V₃ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.ker_eq_bot.mpr hf, finrank_bot, add_zero] at h1
  rw [LinearMap.range_eq_top.mpr hg, finrank_top, ← hfg, h1] at h2
  omega
end FriedCrossing.OrderCount
