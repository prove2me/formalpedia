-- Prove2me | solution 1 for BooleanFun.fourier_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:29.273852+00:00
-- url     : https://prove2.me/submissions/0900c8ea-9df5-4232-9ae5-f985063923ce

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_sum_translate
import Theorems.Thm_BooleanFun_walsh_add

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : 𝓕 (f ⋆ g) = (𝓕 f) * (𝓕 g) := by
  funext S
  change expectation (walshCharacter S * convolution f g) =
    expectation (walshCharacter S * f) * expectation (walshCharacter S * g)
  unfold convolution expectation
  dsimp
  simp_rw [mul_sum]; rw [sum_comm]
  conv => enter [1, 2, y]; rw [sum_translate y]
  simp_rw [walsh_add]
  rw [sum_comm]
  -- reorder -- there should be short tactics for these things
  simp_rw [sum_mul]
  apply sum_congr (by rfl)
  intro y _
  apply sum_congr (by rfl)
  intro x _
  ring_nf
  have hxy : y + x + x = y := by
    ext i
    simp only [Pi.add_apply]
    omega
  rw [hxy]
end BooleanFun
