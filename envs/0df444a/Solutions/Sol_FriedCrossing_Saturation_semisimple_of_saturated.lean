-- Prove2me | solution 1 for FriedCrossing.Saturation.semisimple_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:59.316116+00:00
-- url     : https://prove2.me/submissions/f3c0aff0-26b6-4c42-9f1c-a64f2bd0d8bc

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
    (h₁ : T v₁ = s • v₁) (h₂ : T v₂ = s • v₂) :
    T - s • LinearMap.id = 0 := by
  rw [scalar_of_two_eigenvectors hdim T s v₁ v₂ hind h₁ h₂, sub_self]
end FriedCrossing.Saturation
