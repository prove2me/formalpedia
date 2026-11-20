-- Prove2me | solution 1 for BooleanFun.flipAt_unflipped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:30.414348+00:00
-- url     : https://prove2.me/submissions/7261f480-7f11-4c17-a561-398516654edc

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
theorem _root_.solution {i i₀ : Fin n} {x : Fin n → Fin 2} (h : i ≠ i₀) : flipAt i₀ x i = x i := by
  unfold flipAt
  split_ifs <;> tauto
end BooleanFun
