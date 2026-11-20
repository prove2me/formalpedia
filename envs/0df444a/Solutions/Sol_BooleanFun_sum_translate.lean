-- Prove2me | solution 1 for BooleanFun.sum_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:07:53.598327+00:00
-- url     : https://prove2.me/submissions/566b9fcc-03cd-4590-980f-821fe9657a30

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
theorem _root_.solution (a : Fin n → Fin 2) : ∑ x, f x = ∑ x, f (x + a) := by
  apply sum_bijective (fun x ↦ x + a)
  · constructor
    · intro x y; simp
    · intro y
      use y + a
      ext i
      simp only [Pi.add_apply]
      omega
  · simp
  · intro i _
    congr 1
    ext j
    simp only [Pi.add_apply]
    omega
end BooleanFun
