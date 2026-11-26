-- Prove2me | solution 1 for FriedCrossing.Saturation.scalar_of_two_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:41:01.131617+00:00
-- url     : https://prove2.me/submissions/45927965-040f-4cf2-b24d-28768d1fe8ca

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

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
    T = s • LinearMap.id := by
  have hcard : Fintype.card (Fin 2) = Module.finrank K V := by simp [hdim]
  let b := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hb : ∀ i, b i = ![v₁, v₂] i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine b.ext fun i => ?_
  rw [hb]
  fin_cases i
  · simpa using h₁
  · simpa using h₂
end FriedCrossing.Saturation
