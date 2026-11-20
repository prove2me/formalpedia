-- Prove2me | solution 1 for BooleanFun.walsh_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:07.638809+00:00
-- url     : https://prove2.me/submissions/497f538b-e442-4c3b-9a97-516514e8d560

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
theorem _root_.solution : χ S (x + y) = (χ S x) * (χ S y) := by
  rw [← prod_mul_distrib, prod_congr (by rfl)]
  have (v : Fin 2) : v = 0 ∨ v = 1 := by omega
  intro i _
  dsimp
  obtain ⟨hx|hx, hy|hy⟩ := And.intro (this (x i)) (this (y i)) <;>
    { rw [hx, hy]; simp }
end BooleanFun
