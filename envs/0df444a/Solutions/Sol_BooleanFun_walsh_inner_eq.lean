-- Prove2me | solution 1 for BooleanFun.walsh_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:03:10.774213+00:00
-- url     : https://prove2.me/submissions/9b7b9854-8809-4ac6-829b-f362b2fe72b0

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
theorem _root_.solution : ⟪χ S, χ S'⟫ = oneOn (S = S') := by
  unfold oneOn
  split_ifs with h
  · rw [← h]; exact walsh_inner_self_eq_one
  · exact walsh_orthogonal h
end BooleanFun
