-- Prove2me | solution 1 for BooleanFun.flipAt_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:30.873918+00:00
-- url     : https://prove2.me/submissions/2ffad47a-e6ef-431f-b414-9155fe937d5a

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
theorem _root_.solution {i₀ : Fin n} : Function.Involutive (flipAt i₀) := fun _ ↦ flipAt_flipAt_eq
end BooleanFun
