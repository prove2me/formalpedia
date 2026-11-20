-- Prove2me | solution 1 for BooleanFun.expectation_eq_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:13.383338+00:00
-- url     : https://prove2.me/submissions/fd17d6ae-40a0-4fca-914c-92a61d0d0d87

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : 𝐄 f = 𝓕 f ∅ := by
  unfold fourierTransform
  unfold walshCharacter
  unfold expectation
  simp only [one_div, inv_pow, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.mul_apply, prod_empty, one_mul]
end BooleanFun
