-- Prove2me | solution 1 for BooleanFun.setAt_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:51.115043+00:00
-- url     : https://prove2.me/submissions/3a2a68a1-0d13-4386-acf5-10c21eaf961f

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
theorem _root_.solution (i₀ : Fin n) (v : Fin 2) (x : Fin n → Fin 2) (i : Fin n) (h : i₀ ≠ i) : setAt i₀ v x i = x i := by
  unfold setAt; split_ifs <;> tauto
end BooleanFun
