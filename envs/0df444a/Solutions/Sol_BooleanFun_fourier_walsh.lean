-- Prove2me | solution 1 for BooleanFun.fourier_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:40.804506+00:00
-- url     : https://prove2.me/submissions/0731ae7a-e341-4670-9599-814cd87aa942

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_walsh_inner_eq

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : 𝓕 (χ S) S' = oneOn (S' = S) := walsh_inner_eq
end BooleanFun
