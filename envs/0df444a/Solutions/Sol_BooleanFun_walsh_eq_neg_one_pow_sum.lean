-- Prove2me | solution 1 for BooleanFun.walsh_eq_neg_one_pow_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:08:02.736921+00:00
-- url     : https://prove2.me/submissions/8c765fcf-f2ce-4a30-a8d0-8ac200168f34

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
theorem _root_.solution : χ S x = (-1) ^ ∑ i ∈ S, (x i).val := prod_pow_eq_pow_sum _ _ _
end BooleanFun
