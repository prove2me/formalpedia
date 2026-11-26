-- Prove2me | solution 1 for FriedCrossing.Saturation.eigenvalue_eq_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:55.92797+00:00
-- url     : https://prove2.me/submissions/267bfaec-cff3-4112-9c2c-c7f13f7262e8

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_Saturation_scalar_of_two_eigenvectors

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.Saturation
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
namespace FriedCrossing.Saturation
theorem _root_.solution (hdim : Module.finrank K V = 2) (T : V →ₗ[K] V) (s : K)
    (v₁ v₂ : V) (hind : LinearIndependent K ![v₁, v₂])
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂)
    {μ : K} {v : V} (hv : v ≠ 0) (hμ : T v = μ • v) : μ = s := by
  have hT := scalar_of_two_eigenvectors hdim T s v₁ v₂ hind h₁ h₂
  rw [hT] at hμ
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] at hμ
  have : (μ - s) • v = 0 := by rw [sub_smul, hμ, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · exact (sub_eq_zero.mp h)
  · exact absurd h hv
end FriedCrossing.Saturation
