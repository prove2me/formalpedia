-- Prove2me | solution 1 for BooleanFun.flipAt_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:14:20.578889+00:00
-- url     : https://prove2.me/submissions/7fa93535-1503-442b-8ce8-de669a4212d1

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_flipAt_involutive

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {i₀ : Fin n} : Function.Bijective (flipAt i₀) :=
    Function.Involutive.bijective (flipAt_involutive)
end BooleanFun
