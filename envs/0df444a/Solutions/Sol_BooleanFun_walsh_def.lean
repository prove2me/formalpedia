-- Prove2me | solution 1 for BooleanFun.walsh_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:07:54.13918+00:00
-- url     : https://prove2.me/submissions/2157a3ab-a9b3-4b29-a3ff-579e3c14ce07

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
theorem _root_.solution : χ S x = ∏ i ∈ S, (-1) ^ (x i).val := by rfl
end BooleanFun
